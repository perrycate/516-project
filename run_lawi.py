#!/usr/bin/env python2
from invgen import ControlFlowAutomaton, SignValuation, ConstantValuation, analyze_and_print
from sil import program
import sys
import random

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: ./run_analysis.py [exec|sign|constant] file")
    else:
        pgm = program.parseFile(sys.argv[2], parseAll=True)[0]
        if (sys.argv[1] == "constant"):
            analyze_and_print(ConstantValuation, pgm)
        elif (sys.argv[1] == "sign"):
            analyze_and_print(SignValuation, pgm)
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
            print("Usage: ./run_analysis.py [exec|sign|constant] file")
