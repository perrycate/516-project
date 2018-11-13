#!/usr/bin/env python2
from sudoku import solveSudoku

# Students can create their own instances and try their solution :-)

if __name__ == '__main__':
    # sudoku puzzle with holes (we use '0' for empty cells)
    instance = ((5, 3, 0, 0, 7, 0, 0, 0, 0),
                (6, 0, 0, 1, 9, 5, 0, 0, 0),
                (0, 9, 8, 0, 0, 0, 0, 6, 0),
                (8, 0, 0, 0, 6, 0, 0, 0, 3),
                (4, 0, 0, 8, 0, 3, 0, 0, 1),
                (7, 0, 0, 0, 2, 0, 0, 0, 6),
                (0, 6, 0, 0, 0, 0, 2, 8, 0),
                (0, 0, 0, 4, 1, 9, 0, 0, 5),
                (0, 0, 0, 0, 8, 0, 0, 7, 9))

    solveSudoku(instance)
