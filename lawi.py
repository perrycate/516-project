from collections import defaultdict
import logging
from sil import Annotation, Command, ControlFlowAutomaton, Stmt
from typing import (
    Any,
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
    Int,
    Not,
    BoolVal,
    unsat,
)


def models(lhs: z3.BoolRef, rhs: z3.BoolRef) -> bool:
    s = z3.Solver()
    s.add(Not(Implies(lhs, rhs)))
    return bool(unsat == s.check())


def timeshift(
        u_pi: Iterable[Command]
) -> Tuple[List[z3.BoolRef], Dict[str, int]]:
    vars_times: Dict[str, int] = defaultdict(int)
    ret = [phi.to_formula(vars_times) for phi in u_pi]
    return ret, vars_times


def untimeshift(phi: z3.BoolRef, times: Dict[str, int]) -> z3.BoolRef:
    for k, v in times.items():
        while v:
            phi = z3.substitute(phi, (Int(k + ("'" * v)), Int(k)))
            v -= 1

    return phi


class UnwindingVertex(Annotation):
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

    def __lt__(self, other: Any) -> bool:  # \( \prec \)
        return isinstance(other, UnwindingVertex) and self.num < other.num

    def __le__(self, other: Any) -> bool:
        return isinstance(other, UnwindingVertex) and self.num <= other.num

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, UnwindingVertex) and self.num == other.num

    def __gt__(self, other: Any) -> bool:
        return isinstance(other, UnwindingVertex) and self.num > other.num

    def __ge__(self, other: Any) -> bool:
        return isinstance(other, UnwindingVertex) and self.num >= other.num

    def __ne__(self, other: Any) -> bool:
        return isinstance(other, UnwindingVertex) and self.num != other.num

    def __hash__(self) -> int:
        return self.num.__hash__()

    def __str__(self) -> str:
        return (
            "Vertex {}:"
            " parent {},"
            " transition {},"
            " location {},"
            " label {},"
            " covered {}"
        ).format(
            self.num,
            self.parent.num if self.parent is not None else None,
            self.transition,
            self.location,
            self.label,
            self.covered,
        )

    # \( self \sqsubseteq other \)
    def has_weak_ancestor(self, other: 'UnwindingVertex') -> bool:
        return self == other or (
            self.parent is not None and self.parent.has_weak_ancestor(other)
        )

    def ancestors_path(self) -> Tuple[List['UnwindingVertex'], List[Command]]:
        if self.parent is None:
            return [self], []

        assert self.transition is not None
        v_pi, u_pi = self.parent.ancestors_path()
        v_pi.append(self)
        u_pi.append(self.transition)
        return v_pi, u_pi

    @property
    def is_leaf(self) -> bool:
        return len(self.children) == 0


class Unwinding(Annotation):
    def __init__(
            self,
            cfa: ControlFlowAutomaton,
            loc_entry: int,
            loc_exit: int
    ) -> None:
        self.loc_entry: int = loc_entry  # \( l_i \)
        self.loc_exit: int = loc_exit  # \( l_f \)
        eps = UnwindingVertex(
            location=loc_entry,
            parent=None,
            transition=None,
        )

        # If error path is not None, unwinding is unsafe
        self._error_path: Optional[
            Tuple[List[UnwindingVertex], z3.ModelRef]
        ] = None

        # \( V \leftarrow \{ \epsilon \} \)
        self.verts: Set[UnwindingVertex] = {eps}
        # \( E \) is stored as successor lists on vertices
        # \( \psi \) is stored as labels on vertices
        # \( \triangleright \)
        self.covering: Set[Tuple[UnwindingVertex, UnwindingVertex]] = set()
        # self.uncovered_verts caches uncovered vertices
        # \( \epsilon \) is initially uncovered
        self.uncovered_leaves: Set[UnwindingVertex] = {eps}
        self.cfa: ControlFlowAutomaton = cfa  # cfa.verts is \( \Lambda \)
        while self.uncovered_leaves:
            v = self.uncovered_leaves.pop()
            logging.debug("Unwinding: " + str(v))
            w = v.parent
            while w is not None:
                self.close(w)
                w = w.parent

            self.dfs(v)

    def __str__(self) -> str:
        if self.is_unsafe:
            assert self.error_path is not None
            error_path, error_assign = self.error_path
            return "Unsafe: {}{}".format(
                repr(error_assign),
                "".join(map("\n\t{}".format, error_path))
            )

        return "Safe: {}".format(
            "".join(map("\n\t{}".format, self.verts)),
        )

    def close(self, v: UnwindingVertex) -> None:
        logging.debug("Closing: " + str(v))
        for w in self.verts:
            if w < v and w.location == v.location:
                self.cover(v, w)

    def dfs(self, v: UnwindingVertex) -> None:
        logging.debug("Searching: " + str(v))
        if self.is_unsafe:
            return

        self.close(v)
        if v.covered:
            return

        if v.location == self.loc_exit:
            self.refine(v)
            w: Optional[UnwindingVertex] = v
            while w is not None:
                self.close(w)
                w = w.parent

        self.expand(v)
        for w in v.children:
            self.dfs(w)

    def cover(self, v: UnwindingVertex, w: UnwindingVertex) -> None:
        logging.debug("Covering: " + str(v))
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
        logging.debug("Refining: " + str(v))
        if v.location != self.loc_exit:
            return
        if models(v.label, BoolVal(False)):
            return

        v_pi, u_pi = v.ancestors_path()
        assert(len(v_pi) == len(u_pi) + 1)
        u_pi_, times = timeshift(u_pi)
        assert(len(u_pi) == len(u_pi_))
        try:
            a_hat = z3.sequence_interpolant(u_pi_)
        except z3.ModelRef as model:
            self.mark_unsafe(v, model)
            return

        assert(len(v_pi) == len(a_hat) + 2)
        for i in range(len(a_hat)):
            phi = untimeshift(a_hat[i], times)
            if not models(v_pi[i].label, phi):
                for (x, y) in self.covering.copy():
                    if y == v_pi[i]:
                        self.covering.remove((x, y))
                        if y.is_leaf:
                            self.uncovered_leaves.add(y)

                v_pi[i].label = z3.simplify(And(v_pi[i].label, phi))

    def expand(self, v: UnwindingVertex) -> None:
        logging.debug("Expanding: " + str(v))
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

    def mark_unsafe(
            self,
            unsafe_vert: UnwindingVertex,
            sat_assign: z3.ModelRef
    ) -> None:
        error_path, _ = unsafe_vert.ancestors_path()
        self._error_path = (error_path, sat_assign)

    @property
    def is_unsafe(self) -> bool:
        return self._error_path is not None

    @property
    def error_path(self) -> Optional[Tuple[List[UnwindingVertex], z3.ModelRef]]:
        return self._error_path

    def get_entry(self, loc: int, indent: int = 0) -> str:
        formatStr = "\n" + (indent + 1) * "    " + "{}"
        return "Location {}:{}".format(
            loc,
            "".join(
                formatStr.format(v)
                for v in self.verts
                if v.location == loc
            ),
        )

    @staticmethod
    def analyze(stmt: Stmt) -> 'Unwinding':
        cfa = ControlFlowAutomaton()
        loc_entry = cfa.fresh_vertex()
        loc_exit = cfa.fresh_vertex()
        stmt.to_cfa(cfa, loc_entry, loc_exit)
        return Unwinding(cfa, loc_entry, loc_exit)
