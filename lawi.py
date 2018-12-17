import z3


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


def timeshift(phi, i):
    return phi


class UnwindingVertex:
    next_num = 0

    def __init__(self, parent, transition, location):
        self.parent = parent
        self.parent.children.add(self)
        self.transition = transition  # \( T \)
        self.location = location  # \( M_v(self) \)
        # \( M_e(self.parent, self) \)
        self.children = set()
        self.label = True  # \( \psi(self) \)
        self.covered = False
        self.num = UnwindingVertex.next_num
        UnwindingVertex.next_num += 1

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

    def has_weak_ancestor(self, other):  # \( self \sqsubseteq other \)
        return self == other or (self.parent is not None and self.parent.has_weak_ancestor(other))

    def ancestors_path(self):
        if self.parent is None:
            return [self], []
        v_pi, u_pi = self.parent.ancestors_path()
        v_pi.append(self)
        u_pi.append(self.transition)
        return v_pi, u_pi


class Unwinding:
    def __init__(self, cfa, loc_entry, loc_exit):
        self.loc_entry = loc_entry  # \( l_i \)
        self.loc_exit = loc_exit  # \( l_f \)
        eps = UnwindingVertex(
            location=loc_entry,
            parent=None,
            transition=None,
        )
        self.verts = {eps}  # \( V \leftarrow \{ \epsilon \} \)
        # \( E \) is stored as successor lists on vertices
        # \( \psi \) is stored as labels on vertices
        self.covering = set()  # \( \triangleright \)
        # self.uncovered_verts caches uncovered vertices
        # \( \epsilon \) is initially uncovered
        self.uncovered_leaves = {eps}
        self.cfa = cfa  # cfa.verts is \( \Lambda \)
        while self.uncovered_leaves:
            v = self.uncovered_leaves.pop()
            w = v.parent
            while w is not None:
                self.close(w)
                w = w.parent
            self.dfs(v)

    def close(self, v):
        for w in self.verts:
            if w < v and w.location == v.location:
                self.cover(v, w)

    def dfs(self, v):
        self.close(v)
        if v.covered or v.location != self.loc_entry:
            return
        self.refine(v)
        w = v
        while w is not None:
            self.close(w)
            w = w.parent
        self.expand(v)
        for w in v.children():
            self.dfs(w)

    def cover(self, v, w):
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

    def refine(self, v):
        if v.location != self.loc_exit:
            return
        if models(v.label, False):
            return
        v_pi, u_pi = v.ancestors_path()
        u_pi = [timeshift(t, i) for (i, t) in enumerate(u_pi)]  # TODO: timeshift (wtf is it)
        assert(len(v_pi) == len(u_pi) + 1)
        # make_interpolant aborts if no interpolant exists
        # TODO: catch make_interpolant expcetion and repackage it with current state
        a_hat = z3.sequence_interpolant(u_pi)
        assert(len(a_hat) == len(v_pi))
        for i in range(len(a_hat)):
            phi = timeshift(a_hat[i], -i)  # TODO: timeshift
            if not models(v_pi[i].label, phi):
                self.covering = set(
                    (x, y)
                    for (x, y) in self.covering
                    if y == v_pi[i]
                )
                # TODO: does this uncover anything? should anything be added to uncovered_leaves?
                z3.And(v_pi[i].label, phi)

    def expand(self, v):
        if v.covered or v.children:
            return
        for m in cfa.successors(v.location):
            w = UnwindingVertex(
                parent=v,
                transition=self.cfa.command(v.location, m),
                location=m,
            )
            self.verts.add(w)
            self.uncovered_leaves.add(w)


def analyze_and_print(domain, stmt):
    cfa = ControlFlowAutomaton()
    loc_entry = cfa.fresh_vertex()
    loc_exit = cfa.fresh_vertex()
    stmt.to_cfa(cfa, loc_entry, loc_exit)
    annotation = Unwinding(cfa, loc_entry, loc_exit)
    stmt.print_annotation(annotation, 0)
    print("{" + str(annotation[loc_exit]) + "}")
