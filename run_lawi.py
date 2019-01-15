#!/usr/bin/env python3
import code
from lawi import Unwinding
import logging
import random
from sil import ControlFlowAutomaton, program
import sys

USAGE = "Usage: {} [lawi|constant] file".format(sys.argv[0])

if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)

    if len(sys.argv) != 3:
        logging.critical(USAGE)
        sys.exit()

    pgm = program.parseFile(sys.argv[2], parseAll=True)[0]
    if (sys.argv[1] == "lawi"):
        unwinding = Unwinding.analyze(pgm)
        print(unwinding)
        print(pgm.annotation(unwinding))
        print("{{{}\n}}".format(unwinding.get_entry(unwinding.cfa.loc_exit)))
        if logging.getLogger().getEffectiveLevel() == logging.DEBUG:
            code.interact(local=locals())
    elif (sys.argv[1] == "exec"):
        cfa = ControlFlowAutomaton()
        pgm.to_cfa(cfa, cfa.loc_entry, cfa.loc_exit)
        vars = cfa.vars()
        state = {}
        for var in vars:
            state[var] = random.randint(-10, 10)
        print("Initial state: " + str(state))
        pgm.execute(state)
    else:
        logging.critical(USAGE)
