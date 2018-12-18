#!/usr/bin/env python3
import logging
import socket
import unittest
import z3


def init_z3(z3path: str = '/u/cos516/z3/bin/') -> None:
    if 'courselab' in socket.gethostname():
        logging.info('Initializing Z3 at path: {}'.format(z3path))
        z3.init(z3path)
    else:
        logging.info('Not initializing Z3')


if __name__ == '__main__':
    logging.basicConfig(level=logging.DEBUG)
    init_z3()
    unittest.main()
