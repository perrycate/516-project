#!/usr/bin/env python2
from z3 import And, If, Implies, Int, Solver, Or, print_matrix, sat
# import sys


# A variable representing the value of a specific cell
def matrixvar(i, j):
    return Int("x_%s_%s" % (i, j))


# Create a 9x9 matrix of integer variables
def getMatrix():
    return [[matrixvar(i + 1, j + 1) for j in range(9)]
            for i in range(9)]


# Students should add their code in the following 4 functions
# (instead of the 'return True' statement)

# Add constraints such that each cell contains a value in {1, ..., 9}
def addCellConstraints(X):
    return [And(X[i][j] >= 1,
                X[i][j] <= 9)
            for i in range(9)
            for j in range(9)]


# Add constraints such that each row contains a digit at most once
def addRowConstraints(X):
    return [Implies(X[i][j] == h,
                    And([Or(X[i][k] < h,
                            X[i][k] > h)
                         for k in range(9)
                         if k != j]))
            for h in range(1, 10)
            for i in range(9)
            for j in range(9)]


# Add constraints such that each column contains a digit at most once
def addColumnConstraints(X):
    return [Implies(X[i][j] == h,
                    And([Or(X[k][j] < h,
                            X[k][j] > h)
                         for k in range(9)
                         if k != i]))
            for h in range(1, 10)
            for i in range(9)
            for j in range(9)]


# Add constraints such that each 3x3 square contains a digit at most once
def addSquareConstraints(X):
    return [Implies(X[i][j] == h,
                    And([Or(X[ii][jj] < h,
                            X[ii][jj] > h)
                         for ii in range(i / 3 * 3,
                                         (i / 3 + 1) * 3)
                         for jj in range(j / 3 * 3,
                                         (j / 3 + 1) * 3)
                         if i != ii or j != jj]))
            for h in range(1, 10)
            for i in range(9)
            for j in range(9)]


def solveSudoku(instance):
    X = getMatrix()

    # Create the initial constraints of the puzzle
    # based on the input instance. Note that '0' represents
    # an empty cells
    instance_c = [If(instance[i][j] == 0,
                     True,
                     X[i][j] == instance[i][j])
                  for i in range(9) for j in range(9)]

    # Create the Z3 solver
    s = Solver()

    # Add all needed constraints
    s.add(instance_c)
    s.add(addCellConstraints(X))
    s.add(addRowConstraints(X))
    s.add(addColumnConstraints(X))
    s.add(addSquareConstraints(X))

    # If the problem is satisfiable, a solution exists
    if s.check() == sat:
        m = s.model()
        r = [[m.evaluate(X[i][j]) for j in range(9)]
             for i in range(9)]
        print_matrix(r)
    else:
        print("failed to solve")
