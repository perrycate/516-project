from collections import defaultdict
from sil import Command
from typing import (
    Dict,
    Iterable,
    List,
    Optional,
    Set,
    Tuple,
)
import z3
from z3 import (
    And,
    Implies,
    Not,
    BoolVal,
    unsat,
)


# Control flow automaton: directed graph with a command labelling each edge
class ControlFlowAutomaton:
    def __init__(self):
        self.max_loc = 0
        self.succs = {}
        self.labels = {}
        self.entry = 0

    def fresh_vertex(self):
        v = self.max_loc
        self.max_loc = v + 1
        self.succs[v] = set()
        return v

    def add_edge(self, u, cmd, v):
        self.succs[u].add(v)
        self.labels[(u, v)] = cmd

    def successors(self, v):
        """Set of all successors of a given vertex"""
        return self.succs[v]

    def command(self, u, v):
        """The command associated with a given edge"""
        return self.labels[(u, v)]

    def vars(self):
        """The set of variables that appear in the CFA"""
        vars = set()
        for command in self.labels.values():
            vars = vars | command.vars()
        return vars

    def locations(self):
        """The set of locations (vertices) in the CFA"""
        return set(range(self.max_loc))
############################################################################


def models(lhs: z3.BoolRef, rhs: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add(Not(Implies(lhs, rhs)))
    return s.check() == unsat


def timeshift(u_pi: Iterable[Command]) -> Iterable[z3.BoolRef]:
    vars_times: Dict[str, int] = defaultdict(int)
    for phi in u_pi:
        yield phi.to_formula(vars_times)


def untimeshift(phi: z3.BoolRef) -> z3.BoolRef:
    raise NotImplementedError()


class UnwindingVertex:
    next_num: int = 0

    def __init__(
            self,
            parent: Optional['UnwindingVertex'],
            transition: Optional[Command],
            location: int,
    ) -> None:
        self.num: int = UnwindingVertex.next_num
        UnwindingVertex.next_num += 1
        self.parent: Optional['UnwindingVertex'] = parent
        if self.parent is not None:
            self.parent.children.add(self)
        self.transition: Optional[Command] = transition  # \( T \)
        self.location: int = location  # \( M_v(self) \)
        # \( M_e(self.parent, self) \)
        self.children: Set['UnwindingVertex'] = set()
        self.label: z3.BoolRef = BoolVal(True)  # \( \psi(self) \)
        self.covered: bool = False

    def __lt__(self, other):  # \( \prec \)
        return self.num < other.num

    def __le__(self, other):
        return self.num <= other.num

    def __eq__(self, other):
        return self.num == other.num

    def __gt__(self, other):
        return self.num > other.num

    def __ge__(self, other):
        return self.num >= other.num

    def __ne__(self, other):
        return self.num != other.num

    def __hash__(self):
        return self.num.__hash__()

    def __str__(self):
        if self.is_unsafe:
            return "Unsafe: {}".format(self.error_path)

        return "Vertex {}: parent {}, transition {}, location {}, label {}, covered {}".format(
            self.num,
            self.parent.num if self.parent is not None else None,
            self.transition,
            self.location,
            self.label,
            self.covered,
        )

    def has_weak_ancestor(self, other):  # \( self \sqsubseteq other \)
        return self == other or (self.parent is not None and self.parent.has_weak_ancestor(other))

    def ancestors_path(self) -> Tuple[List['UnwindingVertex'], List[Command]]:
        if self.parent is None:
            return [self], []
        assert self.transition is not None
        v_pi, u_pi = self.parent.ancestors_path()
        v_pi.append(self)
        u_pi.append(self.transition)
        return v_pi, u_pi

    @property
    def is_leaf():
        return len(self.children) == 0


class Unwinding:
    def __init__(self, cfa, loc_entry, loc_exit) -> None:
        self.loc_entry: int = loc_entry  # \( l_i \)
        self.loc_exit: int = loc_exit  # \( l_f \)
        eps = UnwindingVertex(
            location=loc_entry,
            parent=None,
            transition=None,
        )

        # If error path is not None, unwinding is unsafe
        self._error_path: Optional[List[int]] = None

        self.verts: Set[UnwindingVertex] = {eps}  # \( V \leftarrow \{ \epsilon \} \)
        # \( E \) is stored as successor lists on vertices
        # \( \psi \) is stored as labels on vertices
        self.covering: Set[Tuple[UnwindingVertex, UnwindingVertex]] = set()  # \( \triangleright \)
        # self.uncovered_verts caches uncovered vertices
        # \( \epsilon \) is initially uncovered
        self.uncovered_leaves: Set[UnwindingVertex] = {eps}
        self.cfa: ControlFlowAutomaton = cfa  # cfa.verts is \( \Lambda \)
        while self.uncovered_leaves:
            v = self.uncovered_leaves.pop()
            w = v.parent
            while w is not None:
                self.close(w)
                w = w.parent
            self.dfs(v)

    def __str__(self) -> str:
        return "\n".join(map(str, self.verts))

    def close(self, v: UnwindingVertex) -> None:
        for w in self.verts:
            if w < v and w.location == v.location:
                self.cover(v, w)

    def dfs(self, v: UnwindingVertex) -> None:
        if self.is_unsafe:
            return

        self.close(v)
        if v.covered or v.location != self.loc_entry:
            return
        self.refine(v)
        w: Optional[UnwindingVertex] = v
        while w is not None:
            self.close(w)
            w = w.parent
        self.expand(v)
        for w in v.children:
            self.dfs(w)

    def cover(self, v: UnwindingVertex, w: UnwindingVertex) -> None:
        if v.covered or v.location != w.location or w.has_weak_ancestor(v):
            return
        if not models(v.label, w.label):
            return

        # Uncover ancestors of v
        for (x, y) in self.covering.copy():
            if y.has_weak_ancestor(v):
                self.covering.remove((x, y))

                if y.is_leaf:
                    self.uncovered_leaves.add(y)

        # Cover v
        v.covered = True
        self.covering.add((v, w))
        self.uncovered_leaves.remove(v)

    def refine(self, v: UnwindingVertex) -> None:
        if v.location != self.loc_exit:
            return
        if models(v.label, BoolVal(False)):
            return
        v_pi, u_pi = v.ancestors_path()
        u_pi = list(timeshift(u_pi))
        assert(len(v_pi) == len(u_pi) + 1)
        # make_interpolant aborts if no interpolant exists
        try:
            a_hat = z3.sequence_interpolant(u_pi)
        except z3.ModelRef as model:
            self.mark_unsafe(model)
            return
        assert(len(a_hat) == len(v_pi))
        for i in range(len(a_hat)):
            phi = untimeshift(a_hat[i])

            if not models(v_pi[i].label, phi):
                for (x, y) in self.covering.copy():
                    if y == v_pi[i]:
                        self.covering.remove((x, y))
                        if y.is_leaf:
                            self.uncovered_leaves.add(y)

                And(v_pi[i].label, phi)

    def expand(self, v: UnwindingVertex) -> None:
        if v.covered or v.children:
            return
        for m in self.cfa.successors(v.location):
            w = UnwindingVertex(
                parent=v,
                transition=self.cfa.command(v.location, m),
                location=m,
            )
            self.verts.add(w)
            self.uncovered_leaves.add(w)

    def mark_unsafe(self, error_path: List[int]):
        self._error_path = error_path

    @property
    def is_unsafe(self) -> bool:
        return self._error_path is not None

    @property
    def error_path(self) -> Optional[List[int]]:
        return self._error_path


def analyze_and_print(stmt):
    cfa = ControlFlowAutomaton()
    loc_entry = cfa.fresh_vertex()
    loc_exit = cfa.fresh_vertex()
    stmt.to_cfa(cfa, loc_entry, loc_exit)
    annotation = Unwinding(cfa, loc_entry, loc_exit)
    print(annotation)
    import code
    code.interact(local=locals())
    # stmt.print_annotation(annotation, 0)
    # print("{" + str(annotation[loc_exit]) + "}")
