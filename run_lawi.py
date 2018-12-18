#!/usr/bin/env python3
from lawi import ControlFlowAutomaton, analyze_and_print
import logging
import random
from sil import program
import sys
from test_lawi import init_z3

USAGE = "Usage: {} [lawi|constant] file".format(sys.argv[0])

if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    init_z3()

    if len(sys.argv) != 3:
        logging.critical(USAGE)
        sys.exit()

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
        logging.critical(USAGE)
