import sil
from typing import List, Set, Optional, Tuple
import z3
from typing import Set, Tuple


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


def models(lhs, rhs):
    s = z3.Solver()
    s.add(z3.Not(z3.Implies(lhs, z3.rhs)))
    return s.check() == z3.unsat


def timeshift(u_pi):
    shifted_vars = {}
    for phi in u_pi:
        if isinstance(phi, CmdAssign):
            pass
        elif isinstance(phi, CmdAssume):
            pass


class UnwindingVertex:
    next_num: int = 0

    def __init__(
            self,
            parent: Optional['UnwindingVertex'],
            transition: Optional[sil.Command],
            location: int,
    ) -> None:
        self.num: int = UnwindingVertex.next_num
        UnwindingVertex.next_num += 1
        self.parent: Optional['UnwindingVertex'] = parent
        if self.parent is not None:
            self.parent.children.add(self)
        self.transition: Optional[sil.Command] = transition  # \( T \)
        self.location: int = location  # \( M_v(self) \)
        # \( M_e(self.parent, self) \)
        self.children: Set['UnwindingVertex'] = set([])
        self.label: bool = True  # \( \psi(self) \)
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

    def __repr__(self):
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

    def ancestors_path(self) -> Tuple[List['UnwindingVertex'], List[sil.Command]]:
        if self.parent is None:
            return [self], []
        assert self.transition is not None
        v_pi, u_pi = self.parent.ancestors_path()
        v_pi.append(self)
        u_pi.append(self.transition)
        return v_pi, u_pi


class Unwinding:
    def __init__(self, cfa, loc_entry, loc_exit) -> None:
        self.loc_entry: int = loc_entry  # \( l_i \)
        self.loc_exit: int = loc_exit  # \( l_f \)
        eps = UnwindingVertex(
            location=loc_entry,
            parent=None,
            transition=None,
        )
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
        return str(self.verts)

    def close(self, v: UnwindingVertex) -> None:
        for w in self.verts:
            if w < v and w.location == v.location:
                self.cover(v, w)

    def dfs(self, v: UnwindingVertex) -> None:
        self.close(v)
        if v.covered or v.location != self.loc_entry:
            return
        self.refine(v)
        w = v
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
        self.covering.add((v, w))
        self.covering = set(
            (x, y)
            for (x, y) in self.covering
            if not y.has_weak_ancestor(v)
        )
        v.covered = True
        self.uncovered_leaves.remove(v)
        # TODO: does this uncover anything? should anything be added to uncovered_leaves?

    def refine(self, v: UnwindingVertex) -> None:
        if v.location != self.loc_exit:
            return
        if models(v.label, False):
            return
        v_pi, u_pi = v.ancestors_path()
        u_pi = list(timeshift(u_pi))
        assert(len(v_pi) == len(u_pi) + 1)
        # make_interpolant aborts if no interpolant exists
        # TODO: catch make_interpolant expcetion and repackage it with current state
        a_hat = z3.sequence_interpolant(u_pi)
        assert(len(a_hat) == len(v_pi))
        for i in range(len(a_hat)):
            phi = untimeshift(a_hat[i], -i)  # TODO: timeshift
            if not models(v_pi[i].label, phi):
                self.covering = set(
                    (x, y)
                    for (x, y) in self.covering
                    if y == v_pi[i]
                )
                # TODO: does this uncover anything? should anything be added to uncovered_leaves?
                z3.And(v_pi[i].label, phi)

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


def analyze_and_print(stmt):
    cfa = ControlFlowAutomaton()
    loc_entry = cfa.fresh_vertex()
    loc_exit = cfa.fresh_vertex()
    stmt.to_cfa(cfa, loc_entry, loc_exit)
    annotation = Unwinding(cfa, loc_entry, loc_exit)
    print(annotation)
    # stmt.print_annotation(annotation, 0)
    # print("{" + str(annotation[loc_exit]) + "}")
