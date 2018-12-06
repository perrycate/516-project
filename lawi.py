

from sil import ControlFlowAutomaton


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
