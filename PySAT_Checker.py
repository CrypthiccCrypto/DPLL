from base64 import decode
from cmath import sqrt
from xml.etree.ElementTree import tostring
from pysat.solvers import Glucose3, Solver
from pysat.card import *
import numpy as np
from pysat.formula import CNF

URL = 'testcases/uf150-0'
#for i in range(1, 21):
f1 = CNF(from_file=URL+ str(3) +'.cnf')
m = Solver(name="g3", bootstrap_with=f1)
result = m.solve() # solve with assumptions
print(result)
print(m.get_model())
m.delete() # delete solver

