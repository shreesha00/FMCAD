
"""
Protocol Description:

vote(n, r):
	require ~has_voted(n)
	require ~decide_commit(n)
	require ~decide_abort(n)
	voted(n, r) = true
	has_voted(n) = true

go1:
	require forall N. voted(N, true)
	require forall N. ~go_commit(N)
	require forall N. ~go_abort(N)
	go_commit(N) = true

go2: 
	require exists N. voted(N, false)
	require forall N. ~go_commit(N)
	require forall N. ~go_abort(N)
	go_abort(N) = true

commit(n):
	require go_commit(n)
	decide_commit(n) = true

abort(n):
	require go_abort(n)
	decide_abort(n) = true

Backward Analysis:
decide_commit(A), decide_abort(B), go_commit(A), go_abort(B), ~go_commit(*), ~go_abort(*), q. voted(*, true), q. voted(*, false)
"""


from z3 import *

node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')

voted_L = Function('voted_L', node_L, BoolSort(), BoolSort())
votedP_L = Function('votedP_L', node_L, BoolSort(), BoolSort())
voted_S = Function('voted_S', node_S, BoolSort(), BoolSort())
votedP_S = Function('votedP_S', node_S, BoolSort(), BoolSort())
go_commit_L = Function('go_commit_L', node_L, BoolSort())
go_commitP_L = Function('go_commitP_L', node_L, BoolSort())
go_commit_S = Function('go_commit_S', node_S, BoolSort())
go_commitP_S = Function('go_commitP_S', node_S, BoolSort())
go_abort_L = Function('go_abort_L', node_L, BoolSort())
go_abortP_L = Function('go_abortP_L', node_L, BoolSort())
go_abort_S = Function('go_abort_S', node_S, BoolSort())
go_abortP_S = Function('go_abortP_S', node_S, BoolSort())
decide_commit_L = Function('decide_commit_L', node_L, BoolSort())
decide_commitP_L = Function('decide_commitP_L', node_L, BoolSort())
decide_commit_S = Function('decide_commit_S', node_S, BoolSort())
decide_commitP_S = Function('decide_commitP_S', node_S, BoolSort())
decide_abort_L = Function('decide_abort_L', node_L, BoolSort())
decide_abortP_L = Function('decide_abortP_L', node_L, BoolSort())
decide_abort_S = Function('decide_abort_S', node_S, BoolSort())
decide_abortP_S = Function('decide_abortP_S', node_S, BoolSort())

has_voted_L = Function('has_voted_L', node_L, BoolSort())
has_votedP_L = Function('has_votedP_L', node_L, BoolSort())
has_voted_S = Function('has_voted_S', node_S, BoolSort())
has_votedP_S = Function('has_votedP_S', node_S, BoolSort())


s = Solver()
N = Const('N', node_L)
c = Const('c', node_S)

L1 = Const('L1', node_L)
L2 = Const('L2', node_L)
c1 = Const('c1', node_S)
c2 = Const('c2', node_S)
s.add(ForAll([c], Or(c == c1, c == c2)))
s.add(Not(c1 == c2))
s.add(Not(L1 == L2))

def voted_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', BoolSort())
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), votedP_L(tempL_0, tempL_1) == voted_L(tempL_0, tempL_1))), votedP_L(arg_0, arg_1) == arg_2)

def voted_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', BoolSort())
	return ForAll([tempL_0, tempL_1], votedP_L(tempL_0, tempL_1) == voted_L(tempL_0, tempL_1))

def voted_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', BoolSort())
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), votedP_S(tempS_0, tempS_1) == voted_S(tempS_0, tempS_1))), votedP_S(arg_0, arg_1) == arg_2)

def voted_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', BoolSort())
	return ForAll([tempS_0, tempS_1], votedP_S(tempS_0, tempS_1) == voted_S(tempS_0, tempS_1))

def go_commit_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), go_commitP_L(tempL_0) == go_commit_L(tempL_0))), go_commitP_L(arg_0) == arg_1)

def go_commit_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], go_commitP_L(tempL_0) == go_commit_L(tempL_0))

def go_commit_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), go_commitP_S(tempS_0) == go_commit_S(tempS_0))), go_commitP_S(arg_0) == arg_1)

def go_commit_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], go_commitP_S(tempS_0) == go_commit_S(tempS_0))

def go_abort_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), go_abortP_L(tempL_0) == go_abort_L(tempL_0))), go_abortP_L(arg_0) == arg_1)

def go_abort_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], go_abortP_L(tempL_0) == go_abort_L(tempL_0))

def go_abort_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), go_abortP_S(tempS_0) == go_abort_S(tempS_0))), go_abortP_S(arg_0) == arg_1)

def go_abort_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], go_abortP_S(tempS_0) == go_abort_S(tempS_0))

def decide_commit_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), decide_commitP_L(tempL_0) == decide_commit_L(tempL_0))), decide_commitP_L(arg_0) == arg_1)

def decide_commit_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], decide_commitP_L(tempL_0) == decide_commit_L(tempL_0))

def decide_commit_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), decide_commitP_S(tempS_0) == decide_commit_S(tempS_0))), decide_commitP_S(arg_0) == arg_1)

def decide_commit_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], decide_commitP_S(tempS_0) == decide_commit_S(tempS_0))

def decide_abort_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), decide_abortP_L(tempL_0) == decide_abort_L(tempL_0))), decide_abortP_L(arg_0) == arg_1)

def decide_abort_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], decide_abortP_L(tempL_0) == decide_abort_L(tempL_0))

def decide_abort_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), decide_abortP_S(tempS_0) == decide_abort_S(tempS_0))), decide_abortP_S(arg_0) == arg_1)

def decide_abort_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], decide_abortP_S(tempS_0) == decide_abort_S(tempS_0))

def has_voted_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), has_votedP_L(tempL_0) == has_voted_L(tempL_0))), has_votedP_L(arg_0) == arg_1)

def has_voted_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], has_votedP_L(tempL_0) == has_voted_L(tempL_0))

def has_voted_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), has_votedP_S(tempS_0) == has_voted_S(tempS_0))), has_votedP_S(arg_0) == arg_1)

def has_voted_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], has_votedP_S(tempS_0) == has_voted_S(tempS_0))

def vote(n, r):
	formula = And(Not(has_voted_L(n)), Not(decide_commit_L(n)), Not(decide_abort_L(n)))
	formula = And(formula, voted_set_L(n, r, True))
	formula = And(formula, has_voted_set_L(n, True))
	formula = And(formula, go_abort_preserved_L())
	formula = And(formula, go_commit_preserved_L())
	formula = And(formula, decide_abort_preserved_L())
	formula = And(formula, decide_commit_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, go_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, go_commit_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, has_voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_commit_preserved_S())

	b = Const('b', BoolSort())
	formula_S_vote_yes = ForAll([c], If(And(Not(has_voted_S(c)), Not(decide_commit_S(c)), Not(decide_abort_S(c))), And(votedP_S(c, True) == True, votedP_S(c, False) == False, has_votedP_S(c)), And(votedP_S(c, True) == voted_S(c, True), votedP_S(c, False) == voted_S(c, False), has_votedP_S(c) == has_voted_S(c))))
	formula_S_vote_yes = And(formula_S_vote_yes, go_abort_preserved_S())
	formula_S_vote_yes = And(formula_S_vote_yes, go_commit_preserved_S())
	formula_S_vote_yes = And(formula_S_vote_yes, decide_abort_preserved_S())
	formula_S_vote_yes = And(formula_S_vote_yes, decide_commit_preserved_S())

	formula_S_vote_no =  ForAll([c], If(And(Not(has_voted_S(c)), Not(decide_commit_S(c)), Not(decide_abort_S(c))), And(votedP_S(c, False) == True, votedP_S(c, True) == False, has_votedP_S(c)), And(votedP_S(c, True) == voted_S(c, True), votedP_S(c, False) == voted_S(c, False), has_votedP_S(c) == has_voted_S(c))))
	formula_S_vote_no = And(formula_S_vote_no, go_abort_preserved_S())
	formula_S_vote_no = And(formula_S_vote_no, go_commit_preserved_S())
	formula_S_vote_no = And(formula_S_vote_no, decide_abort_preserved_S())
	formula_S_vote_no = And(formula_S_vote_no, decide_commit_preserved_S())

	return And(formula, If(ForAll(N, votedP_L(N, True) == True), formula_S_vote_yes, If(r == False, formula_S_vote_no, formula_S_preserved)))

def go1():
	formula = And(ForAll(N, Not(go_commit_L(N))), ForAll(N, Not(go_abort_L(N))), ForAll(N, voted_L(N, True)))
	formula = And(formula, voted_preserved_L())
	formula = And(formula, decide_abort_preserved_L())
	formula = And(formula, decide_commit_preserved_L())
	formula = And(formula, has_voted_preserved_L())
	formula = And(formula, go_abort_preserved_L())
	formula = And(formula, ForAll(N, go_commitP_L(N) == True))


	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, go_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, go_commit_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, has_voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_commit_preserved_S())

	formula_S = voted_preserved_S()
	formula_S = And(formula_S, decide_abort_preserved_S())
	formula_S = And(formula_S, decide_commit_preserved_S())
	formula_S = And(formula_S, go_abort_preserved_S())
	formula_S = And(formula_S, has_voted_preserved_S())
	formula_S = And(formula_S, ForAll(c, go_commitP_S(c) == True))

	return And(formula, If(And(ForAll(c, Not(go_commit_S(c))), ForAll(c, Not(go_abort_S(c))), ForAll(c, voted_S(c, True))), formula_S, formula_S_preserved))

def go2():
	formula = And(ForAll(N, Not(go_commit_L(N))), ForAll(N, Not(go_abort_L(N))), Exists(N, voted_L(N, False)))
	formula = And(formula, voted_preserved_L())
	formula = And(formula, decide_abort_preserved_L())
	formula = And(formula, decide_commit_preserved_L())
	formula = And(formula, go_commit_preserved_L())
	formula = And(formula, has_voted_preserved_L())
	formula = And(formula, ForAll(N, go_abortP_L(N) == True))
	
	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, go_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, go_commit_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, has_voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_commit_preserved_S())

	formula_S = voted_preserved_S()
	formula_S = And(formula_S, decide_abort_preserved_S())
	formula_S = And(formula_S, decide_commit_preserved_S())
	formula_S = And(formula_S, go_commit_preserved_S())
	formula_S = And(formula_S, has_voted_preserved_S())
	formula_S = And(formula_S, ForAll(c, go_abortP_S(c) == True))

	return And(formula, If(And(ForAll(c, Not(go_commit_S(c))), ForAll(c, Not(go_abort_S(c))), Exists(c, voted_S(c, False))), formula_S, formula_S_preserved))

def commit(n):
	formula = go_commit_L(n)
	formula = And(formula, decide_commit_set_L(n, True))
	formula = And(formula, go_abort_preserved_L())
	formula = And(formula, go_commit_preserved_L())
	formula = And(formula, decide_abort_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, has_voted_preserved_L())


	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, go_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, go_commit_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, has_voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_commit_preserved_S())

	formula_S_1 = decide_commit_set_S(c1, True)
	formula_S_1 = And(formula_S_1, go_abort_preserved_S())
	formula_S_1 = And(formula_S_1, go_commit_preserved_S())
	formula_S_1 = And(formula_S_1, decide_abort_preserved_S())
	formula_S_1 = And(formula_S_1, voted_preserved_S())
	formula_S_1 = And(formula_S_1, has_voted_preserved_S())
	
	return And(formula, If(And(n == L1, go_commit_S(c1)), formula_S_1, formula_S_preserved))

def abort(n):
	formula = go_abort_L(n)
	formula = And(formula, decide_abort_set_L(n, True))
	formula = And(formula, go_abort_preserved_L())
	formula = And(formula, go_commit_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, decide_commit_preserved_L())
	formula = And(formula, has_voted_preserved_L())


	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, go_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, go_commit_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_abort_preserved_S())
	formula_S_preserved = And(formula_S_preserved, has_voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decide_commit_preserved_S())

	formula_S_2 = decide_abort_set_S(c2, True)
	formula_S_2 = And(formula_S_2, go_abort_preserved_S())
	formula_S_2 = And(formula_S_2, go_commit_preserved_S())
	formula_S_2 = And(formula_S_2, decide_commit_preserved_S())
	formula_S_2 = And(formula_S_2, voted_preserved_S())
	formula_S_2 = And(formula_S_2, has_voted_preserved_S())

	
	return And(formula, If(And(n == L2, go_abort_S(c2)), formula_S_2, formula_S_preserved))


# initial state of a node in the cutoff system
def init_c(n):
	return And(Not(voted_S(n, True)), Not(voted_S(n, False)), Not(has_voted_S(n)), Not(decide_commit_S(n)), Not(decide_abort_S(n)), Not(go_commit_S(n)), Not(go_abort_S(n)))

def initP_c(n):
	return And(Not(votedP_S(n, True)), Not(votedP_S(n, False)), Not(has_votedP_S(n)), Not(decide_commitP_S(n)), Not(decide_abortP_S(n)), Not(go_commitP_S(n)), Not(go_abortP_S(n)))

action = Const('action', IntSort())

n = Const('n', node_L)
r = Const('r', BoolSort())
step = And(vote(n, r), action == 1)
step = Xor(step, And(go1(), action == 2))
step = Xor(step, And(go2(), action == 3))
step = Xor(step, And(commit(n), action == 4))
step = Xor(step, And(abort(n), action == 5))

N1 = Const('N1', node_L)
b = Const('b', BoolSort())
simulation_relation = ForAll([N, N1], Implies(decide_commit_L(N), Not(decide_abort_L(N1))))
simulation_relation = And(simulation_relation, ForAll(N, Exists(b, voted_L(N, b)) == has_voted_L(N)))
simulation_relation = And(simulation_relation, ForAll([N], Implies(voted_L(N, True), Not(voted_L(N, False)))))

simulation_relation = And(simulation_relation, Implies(decide_commit_L(L1), decide_commit_S(c1)))
simulation_relation = And(simulation_relation, Implies(decide_abort_L(L2), decide_abort_S(c2)))
simulation_relation = And(simulation_relation, Implies(go_commit_L(L1), go_commit_S(c1)))
simulation_relation = And(simulation_relation, Implies(go_abort_L(L2), go_abort_S(c2)))
simulation_relation = And(simulation_relation, Implies(ForAll(N, Not(go_commit_L(N))), ForAll(c, Not(go_commit_S(c)))))
simulation_relation = And(simulation_relation, Implies(ForAll(N, Not(go_abort_L(N))), ForAll(c, Not(go_abort_S(c)))))
simulation_relation = And(simulation_relation, Implies(ForAll(N, voted_L(N, True)), ForAll(c, voted_S(c, True))))
simulation_relation = And(simulation_relation, Implies(Exists(N, voted_L(N, False)), ForAll(c, voted_S(c, False))))

# If no quorum event has occured then the cutoff system is in a clean slate init state
simulation_relation = And(simulation_relation, Implies(Not(Or(ForAll(N, voted_L(N, True)), Exists(N, voted_L(N, False)))), ForAll(c, init_c(c))))

s.add(simulation_relation)
s.add(step)
print(s.check())
violation = Const('violation', IntSort())
neg = And(decide_commitP_L(L1), decide_commitP_S(c1) == False, violation == 1)
neg = Or(neg, And(decide_abortP_L(L2), decide_abortP_S(c2) == False, violation == 2))
neg = Or(neg, And(go_commitP_L(L1), go_commitP_S(c1) == False, violation == 3))
neg = Or(neg, And(go_abortP_L(L2), go_abortP_S(c2) == False, violation == 4))
neg = Or(neg, And(ForAll(N, Not(go_commitP_L(N))), ForAll(c, Not(go_commitP_S(c))) == False, violation == 5))
neg = Or(neg, And(ForAll(N, Not(go_abortP_L(N))), ForAll(c, Not(go_abortP_S(c))) == False, violation == 6))
neg = Or(neg, And(ForAll(N, votedP_L(N, True)), ForAll(c, votedP_S(c, True)) == False, violation == 7))
neg = Or(neg, And(Exists(N, votedP_L(N, False)), ForAll(c, votedP_S(c, False)) == False, violation == 8))

neg = Or(neg, And(Not(Or(ForAll(N, votedP_L(N, True)), Exists(N, votedP_L(N, False)))), ForAll(c, initP_c(c)) == False, violation == 13))

s.add(neg)
print(s.check())


if(str(s.check()) == 'sat') :
    print(s.model())

