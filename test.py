import networkx as nx
import matplotlib.pyplot as plt

from factoring import *
from graph_generator import *

import pickle
import time

from pysat.formula import CNF
from pysat.solvers import Solver

GRAPH = False
SOLVESAT = True

BITS = 21

# 16 bits
# primes = [
#   46727,
#   54851
# ]

# 21 bits
primes = [
  1390547,
  1549937
]

# 24 bits
# primes = [
#   10506467,
#   10962901
# ]

# 32 bits
# primes = [
#   2467286519,
#   3859726399
# ]


# 64 bits
# primes = [
#   15222133893380444963,
#   17566287317352414763
# ]


# 330 bits
# primes = [
#   37975227936943673922808872755445627854565536638199,
#   40094690950920881030683735292761468389214899724061
# ]

# 512 bits
# primes = [
#   102639592829741105772054196573991675900716567808038066803341933521790711307779,
#   106603488380168454820927220360012878679207958575989291522270608237193062808643
# ]

DICT = {}

for i in range(len(primes)):
  for j in range(i+1, len(primes)):

    p = primes[i]
    q = primes[j]

    print( f"Primes: {p} and {q}" )

    # cnf = generate_instance_known_factors( p, q )
    cnf = generate_instance( p*q, BITS, BITS )

    n_vars, n_clauses, clauses = create_clauses( cnf )

    # print("Clauses dictionary\n")
    # print(clauses)
    print( f"Number of variables {n_vars}" )
    print( f"Number of clauses {n_clauses}" )


    dic2 = sorted( len(v) for _,v in clauses.items() )
    print(dic2)

    if SOLVESAT:
      # Create the CNF for PySat
      clauses_list = []
      for _,v in clauses.items():
        clauses_list.append( v )

      s = 0
      for _,v in clauses.items():
        s += len(v)

      print(f"Total literals: {s}")

      # print( clauses_list )
      print( "Creating CNF" )
      cnf_pysat = CNF( from_clauses=clauses_list )


      print( "Launching Solver" )

      # create a SAT solver for this formula:
      with Solver(bootstrap_with=cnf_pysat) as solver:

        start = time.time()

        # 1.1 call the solver for this formula:
        print('formula is', f'{"s" if solver.solve() else "uns"}atisfiable')

        end = time.time()

        # # Get all the models
        # for m in solver.enum_models():
        #   print("Solution")
        #   # print(m)

      print(f"SAT solved in time {end - start} seconds")

    # # Convert the instance to 3sat
    # cnf3_clauses, new_vars, new_clauses = transformCNF( n_vars, n_clauses, clauses, 3 )

    if GRAPH:
      print( "Creating graph" )
      # CREATE Graph
      G, easyG = create_nodes_edges( n_vars, n_clauses, clauses )
      Delta = max( [ val for (node,val) in easyG.degree() ] )

      print(f"Graph max degree: {Delta}")

      print( f"#Nodes: {easyG.number_of_nodes()}" )
      print( f"#Edges: {easyG.number_of_edges()}" )

      # greedyMIS( G )

      # nx.draw( G )
      # plt.show()

      # Let's save graphs
      # if Delta > 0 and Delta < 20:
      #   DICT[(p,q)] = {
      #     "G": G,
      #     "Easy_G": easyG,
      #     "SAT": clauses,
      #     "N_vars": n_vars,
      #     "N_clauses": n_clauses,
      #     "CNF": cnf,
      #     "Max_deg": Delta
      #   }

      # # Solve the MIS and check if |MIS|==n_clauses
      # model = solve_MIS( easyG )

      # MIS_size = sizeMIS( easyG, model )

      # print(f"#Clauses: {n_clauses}")
      # print(f"#MIS size: {MIS_size}")
      # model.x.pprint()


# Write the graphs to a file
# with open( "graphs/instances.pkl", "wb" ) as f:
#   pickle.dump( DICT, f, protocol=pickle.HIGHEST_PROTOCOL )