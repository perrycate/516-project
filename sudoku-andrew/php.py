#!/usr/bin/env python2
from z3 import And, Implies, Int, Or, Solver, unsat, sat
import sys
import time

# PHP with Theory
# Define a variable for each pigeon to represent the hole that pigeon goes into


def getVar(i):
        return (Int("x_%d" % (i)))


# An array with a variable per pigeon
def getArray(n):
    return [getVar(i) for i in range(n)]


# each pigeon can be in a hole {1,...,n}
def addPigeonInHole(A, n):
    p_in_h = [And(1 <= A[i], A[i] <= n)
              for i in range(n + 1)]
    return p_in_h

def addOnePigeonOnly(A, n):
    one_only = []
    for h in range(1, n + 1):
        for p in range(n + 1):
            one_only.append(Implies(A[p] == h,
                                    And([Or(A[r] < h, A[r] > h)
                                         for r in range(n + 1) if r is not p]
                                        )))
            # one_only.append(Implies(A[p] == h,
            #                         And([A[r] != h
            #                              for r in range(n + 1) if r is not p]
            #                             )))
    return And(one_only)

# Solve PHP
def solvePHP(n):

    out = sys.stdout

    # Helper functions
    def p(txt):
        if out:
            out.write(txt + '\n')

    def pr(txt):
        if out:
            out.write(txt)

    A = getArray(n + 1)

    p("---")
    p("Solving PHP for %d pigeons and %d holes" % (n + 1, n))

    # Handle time
    start = time.clock()

    # Create one solver instance that we'll use all the time
    s = Solver()

    s.add(addPigeonInHole(A, n))
    s.add(addOnePigeonOnly(A, n))

    #    print s

    result = s.check()
    p("The solver says: " + str(result))

    if result == unsat:
        solution = "nonexistent"

    elif result == sat:
        print(s.model())
        solution = "found"

    else:
        assert(result == unknown)
        p('"unknown" (with reason "'
          + s.reason_unknown()
          + '") returned by the solver, aborting!')
        solution = "error"

    elapsed = time.clock() - start
    p("Time to solve = %12.2f[s]" % elapsed)
    return solution
