#!/usr/bin/env python3
from sil import program
from lawi import ControlFlowAutomaton, analyze_and_print
import socket
import sys
import random

if __name__ == '__main__':
    if 'courselab' in socket.gethostname():
        print('Initializing Z3')
        z3.init('/u/cos516/z3/bin/')
    else:
        print('Not initializing Z3')

    if len(sys.argv) != 3:
        print("Usage: ./run_analysis.py [lawi|constant] file")
    else:
        pgm = program.parseFile(sys.argv[2], parseAll=True)[0]
        if (sys.argv[1] == "lawi"):
            analyze_and_print(pgm)
        elif (sys.argv[1] == "exec"):
            cfa = ControlFlowAutomaton()
            loc_entry = cfa.fresh_vertex()
            loc_exit = cfa.fresh_vertex()
            pgm.to_cfa(cfa, loc_entry, loc_exit)
            vars = cfa.vars()
            state = {}
            for var in vars:
                state[var] = random.randint(-10, 10)
            print("Initial state: " + str(state))
            pgm.execute(state)
        else:
            print("Usage: ./run_analysis.py [lawi|constant] file")
