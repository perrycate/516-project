#!/usr/bin/env python2

from php import solvePHP
import sys

if __name__ == '__main__':
    if (len(sys.argv) == 2):
        n = (int)(sys.argv[1])
        print(n)
        solvePHP(n)
