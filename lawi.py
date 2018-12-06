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


class UnwindingVertex:
    next_num = 0

    def __init__(self, parent, transition, location):
        self.parent = parent
        self.parent.children.add(self)
        self.transition = transition
        self.location = location
        self.children = set()
        self.label = True
        self.num = UnwindingVertex.next_num
        UnwindingVertex.next_num += 1

    def __lt__(self, other):
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

    def has_weak_ancestor(self, other):
        return self == other or (self.parent is not None and self.parent.has_weak_ancestor(other))

    def ancestors_path(self):
        if self.parent is None:
            return [self], []
        v_pi, u_pi = self.parent.ancestors_path()
        v_pi.append(self)
        u_pi.append(self.transition)
        return v_pi, u_pi


class Unwinding:
    def __init__(self, cfa):
        self.verts = set(UnwindingVertex(None, None, None))
        self.uncovered_verts = set(self.verts)
        self.covering = set()
        while self.uncovered_verts:
            v = self.uncovered_verts.pop()
            w = v.parent
            while w is not None:
                self.close(w)
                w = w.parent
            self.dfs(v)

    def close(self, v):
        for w in self.verts:
            if w < v and self.M(v)(w) == self.M(v)(v):
                self.cover(v, w)

    def dfs(self, v):
        self.close(v)
        if v not in self.uncovered_verts:
            return
        if self.M(v)(v) == self.l_f:
            self.refine(v)
            w = v
            while w is not None:
                self.close(w)
                w = w.parent
            self.expand(v)
            for w in v.children():
                self.dfs(w)

    def cover(self, v, w):
        if v in self.uncovered_verts and self.M(v)(v) == self.M(v)(w) and not w.has_weak_ancestor(v):
            if v.label.models(w.label):
                self.covering.add((v, w))
                self.covering = set(
                    (x, y)
                    for (x, y) in self.covering
                    if not y.has_weak_ancestor(v)
                )

    def refine(self, v):
        if self.M(v)(v) == self.l_f and v.label.satisfiable():
            v_pi, u_pi = v.ancestors_path()
            u_pi = [t.timeshift(i) for (i, t) in enumerate(u_pi)]
            assert(len(v_pi) == len(u_pi) + 1)
            a_hat = make_interpolant(u_pi)
            assert(len(a_hat) == len(v_pi))
            for i in range(len(a_hat)):
                phi = a_hat[i].timeshift(-i)
                if v_pi[i].label.derives(phi):
                    self.covering = set(
                        (x, y)
                        for (x, y) in self.covering
                        if y == v_pi[i]
                    )
                    v_pi[i].label &= phi

    def expand(self, cfa, v):
        if v in self.uncovered_verts and v.children:
            for (m_v_v, t, m) in cfa.succs[v.location]:
                self.verts.add(UnwindingVertex(v, t, m))
                self.m(v)[w] = m
                self.m(e)[(v, w)] = True


def analyze(domain, cfa):
    """Given a domain and a control flow automaton, compute the least
    inductive annotation (i.e., for all edge (u,v), we have
    domain.leq(annotation[u].post(cfa.command(u,v)), annotation[v])) such that
    annotation[cfa.entry] is domain.top
    """
    return {}


def analyze_and_print(domain, stmt):
    cfa = ControlFlowAutomaton()
    loc_entry = cfa.fresh_vertex()
    loc_exit = cfa.fresh_vertex()
    stmt.to_cfa(cfa, loc_entry, loc_exit)
    annotation = analyze(domain, cfa)
    stmt.print_annotation(annotation, 0)
    print("{" + str(annotation[loc_exit]) + "}")
