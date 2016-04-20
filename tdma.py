from z3 import *
import math
import sys
import itertools
import datetime


def getSlotName(i, s):
	return 'i'+`i`+'s'+`s`

def main():
	if(len(sys.argv) != 5):
		print 'Usage: python tdma.py <# ports> <# ReCOP> <# JOPs> <# Slots to check>'
		sys.exit(1)

	# Declaring a z3 solver
	st = datetime.datetime.now()
	solver = Tactic('qflia').solver()

	np = int(sys.argv[1]) # number of ports
	nr = int(sys.argv[2]) # number of recops
	nj = int(sys.argv[3]) # number of jops
	obj = int(sys.argv[4]) # number of slots to check

	N = int(math.pow(2, math.ceil(math.log(np,2))))
	s = math.log(N,2);
	tdma = [[0 for x in range(N)] for x in range(N)]
	smtv = {}
	for i in range(len(tdma)): # i = input port number
		slot = int(('{:0'+str(int(s))+'b}').format(i)[::-1], 2) 
		smtv["match"+`i`] = Int('match'+`i`)
		for y in range(len(tdma[i])): # y = slot number
			tdma[i][y] = slot ^ y
			o = Int(getSlotName(i,y))
			smtv[getSlotName(i,y)] = o
			solver.add(o == tdma[i][y])

	rl = []
	jl = []
	for i in range(nr):
		rl.append(Int('iReCOP'+`i`))

	for i in range(nj):
		jl.append(Int('iJOP'+`i`))

	solver.add(And(*([v for sublist in [[x < N, x >= 0] for x in rl + jl] for v in sublist])))
	
	def f1(i, j):
		of = Or(*[x == smtv[getSlotName(j, i)] for x in rl])
		os = Or(*[x == j for x in jl])
		and1 = And(of,os)
		of = Or(*[x == smtv[getSlotName(j, i)] for x in jl])
		os = Or(*[x == j for x in rl])
		and2 = And(of,os)
		return (and1,and2)

	def f2(i):
		chain = [f1(i, j) for j in range(N)]
		chain = itertools.chain(*chain)
		return If(Or(*chain), smtv['match'+`i`] == 1, smtv['match'+`i`] == 0)

	solver.add(And(*[f2(i) for i in range(N)]))


	solver.add(And(*[[ Not(j == rl[i]) for i in range(len(rl)) for j in rl[i+1:]] + [ Not(j == jl[i]) for i in range(len(jl)) for j in jl[i+1:]] + [ Not(i == j) for i in rl for j in jl  ] ]))
	
	ns = [smtv[i] for i in smtv if i.startswith('match')]
	solver.add(reduce(lambda x, y: x+y, [i for i in ns], 0) <= obj)

	print 'formulation time : ' + str(datetime.datetime.now() - st)
	st = datetime.datetime.now()
#  print solver.sexpr()
#  sys.exit(1)
	print solver.check()
	print 'solving time : ' + str(datetime.datetime.now() - st)
	print solver.model()

if __name__ == "__main__":
	main()
