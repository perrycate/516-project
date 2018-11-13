from z3 import *
import sys

# A variable representing the value of a specific cell
def matrixvar(i, j):
    return Int("x_%s_%s" % (i,j))

# Create a 9x9 matrix of integer variables
def getMatrix():
    return [ [ matrixvar(i+1, j+1) for j in range(9) ] 
             for i in range(9) ]

# My (student-made) helper functions

# Returns all variables on the row containing this coordinate
def getRow(X, i, j=0):
    return X[i]

# Returns all variables on the column containing this coordinate
def getCol(X, i, j):
    return [X[x][j] for x in range(9)]

# Returns all variables on the 3x3 square containing this coordinate
def getSquare(matrix, i, j):
    start_row = (i/3)*3
    start_col = (j/3)*3

    items = []
    for y in range(3):
        items += [matrix[start_row+y][start_col+x] for x in range(3)]

    return items

# Add constraint that no 2 vars in items can have the same value
def addOnceConstraints(items):
    constraints = []

    length = len(items)
    for i in range(length):
        for num in range(1, len(items)+1):
            constraints.append(
                Implies(items[i] == num,
                        And([items[r] != num for r in range(length) if r is not i])))
    return constraints


# Students should add their code in the following 4 functions
# (instead of the 'return True' statement)

# Add constraints such that each cell contains a value in {1, ..., 9} 
def addCellConstraints(X):
    constraints = []
    for i in range(9):
        constraints += [And(X[i][j] <= 9, X[i][j] >= 1) for j in range(9)]
    return constraints

# Add constraints such that each row contains a digit at most once
def addRowConstraints(X):
    constraints = []
    for i in range(9):
        row = getRow(X, i)
        constraints += addOnceConstraints(row)
    return constraints

# Add constraints such that each column contains a digit at most once
def addColumnConstraints(X):
    constraints = []
    for i in range(9):
        col = getCol(X, 0, i)
        constraints += addOnceConstraints(col)
    return constraints

# Add constraints such that each 3x3 square contains a digit at most once
def addSquareConstraints(X):
    constraints = []
    for i in range(0, 9, 3):
        for j in range(0, 9, 3):
            square = getSquare(X, i, j)
        constraints += addOnceConstraints(square)
    return constraints

def solveSudoku(instance):
    X = getMatrix()

    # Create the initial constraints of the puzzle
    # based on the input instance. Note that '0' represents 
    # an empty cells
    instance_c = [ If(instance[i][j] == 0, 
                      True, 
                      X[i][j] == instance[i][j]) 
                   for i in range(9) for j in range(9) ]

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
        r = [ [ m.evaluate(X[i][j]) for j in range(9) ] 
              for i in range(9) ]
        print_matrix(r)
    else:
        print "failed to solve"
