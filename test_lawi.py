#!/usr/bin/env python3

import socket
import unittest
import z3

if __name__ == '__main__':
    if 'courselab' in socket.gethostname():
        print('Initializing Z3')
        z3.init('/u/cos516/z3/bin/')
    else:
        print('Not initializing Z3')
    unittest.main()
