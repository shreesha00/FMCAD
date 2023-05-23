from z3 import *
from contextlib import redirect_stdout

"""
Protocol Description:
axiom: forall q1, q2. exists n. member(n, q1) & member(n, q2)

action cast_vote(n, v):
	require ~voted(n)
	vote(n, v) = true
	voted(n) = true

action decide(v, q):
	require forall n. member(n, q) -> vote(n, v)
	decided(v) = true

Backward Analysis:
decided(v_1), decided(v_2), q. vote(*, v_1), q. vote(*, v_2)
"""

node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')
quorum = DeclareSort('quorum')
value = DeclareSort('value')

member_L = Function('member_L', node_L, quorum, BoolSort())
memberP_L = Function('memberP_L', node_L, quorum, BoolSort())
member_S = Function('member_S', node_S, quorum, BoolSort())
memberP_S = Function('memberP_S', node_S, quorum, BoolSort())
vote_L = Function('vote_L', node_L, value, BoolSort())
voteP_L = Function('voteP_L', node_L, value, BoolSort())
vote_S = Function('vote_S', node_S, value, BoolSort())
voteP_S = Function('voteP_S', node_S, value, BoolSort())
decided_L = Function('decided_L', value, BoolSort())
decidedP_L = Function('decidedP_L', value, BoolSort())
decided_S = Function('decided_S', value, BoolSort())
decidedP_S = Function('decidedP_S', value, BoolSort())
voted_L = Function('voted_L', node_L, BoolSort())
votedP_L = Function('votedP_L', node_L, BoolSort())
voted_S = Function('voted_S', node_S, BoolSort())
votedP_S = Function('votedP_S', node_S, BoolSort())

def member_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', quorum)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), memberP_L(tempL_0, tempL_1) == member_L(tempL_0, tempL_1))), memberP_L(arg_0, arg_1) == arg_2)

def member_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', quorum)
	return ForAll([tempL_0, tempL_1], memberP_L(tempL_0, tempL_1) == member_L(tempL_0, tempL_1))

def member_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', quorum)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), memberP_S(tempS_0, tempS_1) == member_S(tempS_0, tempS_1))), memberP_S(arg_0, arg_1) == arg_2)

def member_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', quorum)
	return ForAll([tempS_0, tempS_1], memberP_S(tempS_0, tempS_1) == member_S(tempS_0, tempS_1))

def vote_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', value)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), voteP_L(tempL_0, tempL_1) == vote_L(tempL_0, tempL_1))), voteP_L(arg_0, arg_1) == arg_2)

def vote_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', value)
	return ForAll([tempL_0, tempL_1], voteP_L(tempL_0, tempL_1) == vote_L(tempL_0, tempL_1))


def voted_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), votedP_L(tempL_0) == voted_L(tempL_0))), votedP_L(arg_0) == arg_1)

def voted_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], votedP_L(tempL_0) == voted_L(tempL_0))

def voted_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), votedP_S(tempS_0) == voted_S(tempS_0))), votedP_S(arg_0) == arg_1)

def voted_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], votedP_S(tempS_0) == voted_S(tempS_0))

def vote_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', value)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), voteP_S(tempS_0, tempS_1) == vote_S(tempS_0, tempS_1))), voteP_S(arg_0, arg_1) == arg_2)

def vote_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', value)
	return ForAll([tempS_0, tempS_1], voteP_S(tempS_0, tempS_1) == vote_S(tempS_0, tempS_1))

def decided_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', value)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), decidedP_L(tempL_0) == decided_L(tempL_0))), decidedP_L(arg_0) == arg_1)

def decided_preserved_L():
	tempL_0 = Const('tempL_0', value)
	return ForAll([tempL_0], decidedP_L(tempL_0) == decided_L(tempL_0))

def decided_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', value)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), decidedP_S(tempS_0) == decided_S(tempS_0))), decidedP_S(arg_0) == arg_1)

def decided_preserved_S():
	tempS_0 = Const('tempS_0', value)
	return ForAll([tempS_0], decidedP_S(tempS_0) == decided_S(tempS_0))

def single_node_vote_S(n, v):
	temp_val = Const('temp_val', value)
	return And(voteP_S(n, v) == True, ForAll(temp_val, Implies(Not(temp_val == v), voteP_S(n, temp_val) == vote_S(n, temp_val))))

def single_node_vote_preserved_S(n):
	temp_val = Const('temp_val', value)
	return ForAll(temp_val, voteP_S(n, temp_val) == vote_S(n, temp_val))

N1, N2 = Consts('N1 N2', node_L)
S1, S2 = Consts('S1 S2', node_S)
Q1, Q2 = Consts('Q1 Q2', quorum)
V1, V2 = Consts('V1 V2', value)
v1, v2 = Consts('v1 v2', value)


s = Solver()
s1 = Const('s1', node_S)
s.add(ForAll([S1], S1 == s1))
s.add(v1 != v2)

def cast_vote(n, v):
	formula = Not(voted_L(n))
	formula = And(formula, vote_set_L(n, v, True))
	formula = And(formula, member_preserved_L())
	formula = And(formula, voted_set_L(n, True))
	formula = And(formula, decided_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, vote_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decided_preserved_S())

	formula_S_vote = ForAll(S1, If(Not(voted_S(S1)), And(single_node_vote_S(S1, v), votedP_S(S1)), And(single_node_vote_preserved_S(S1), votedP_S(S1) == voted_S(S1))))
	formula_S_vote = And(formula_S_vote, member_preserved_S())
	formula_S_vote = And(formula_S_vote, decided_preserved_S())
	
	return And(formula, If(And(Exists(Q1, ForAll(N1, Implies(memberP_L(N1, Q1), voteP_L(N1, v)))), Or(v == v1, v == v2)), formula_S_vote, formula_S_preserved))

def decide(v, q):
	formula = ForAll(N1, Implies(member_L(N1, q), vote_L(N1, v)))
	formula = And(formula, decided_set_L(v, True))
	formula = And(formula, vote_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, member_preserved_L())
	
	formula_S = If(ForAll(S1, vote_S(S1, v)), decided_set_S(v, True), decided_preserved_S())
	formula_S = And(formula_S, vote_preserved_S())
	formula_S = And(formula_S, voted_preserved_S())
	formula_S = And(formula_S, member_preserved_S())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, vote_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, decided_preserved_S())

	return And(formula, If(Or(v == v1, v == v2), formula_S, formula_S_preserved))

action = Const('action', IntSort())
n = Const('n', node_L)
q = Const('q', quorum)
v = Const('v', value)

step = And(cast_vote(n, v), action == 1)
step = Xor(step, And(decide(v, q), action == 2))

simulation_relation = ForAll([V1, V2], Implies(And(decided_L(V1), decided_L(V2)), V1 == V2))
simulation_relation = And(simulation_relation, ForAll([N1, V1, V2], Implies(And(vote_L(N1, V1), vote_L(N1, V2)), V1 == V2)))
simulation_relation = And(simulation_relation, ForAll([N1], Exists(V1, vote_L(N1, V1)) == voted_L(N1)))
simulation_relation = And(simulation_relation, ForAll([Q1, Q2], Exists(N1, And(member_L(N1, Q1), member_L(N1, Q2)))))

simulation_relation = And(simulation_relation, Implies(decided_L(v1), decided_S(v1)))
simulation_relation = And(simulation_relation, Implies(decided_L(v2), decided_S(v2)))
simulation_relation = And(simulation_relation, ForAll([Q1], Implies(ForAll(N1, Implies(member_L(N1, Q1), vote_L(N1, v1))), ForAll(S1, vote_S(S1, v1)))))
simulation_relation = And(simulation_relation, ForAll([Q1], Implies(ForAll(N1, Implies(member_L(N1, Q1), vote_L(N1, v2))), ForAll(S1, vote_S(S1, v2)))))
simulation_relation = And(simulation_relation, Implies(Not(Or(Exists([Q1], ForAll(N1, Implies(member_L(N1, Q1), vote_L(N1, v1)))), Exists([Q1], ForAll(N1, Implies(member_L(N1, Q1), vote_L(N1, v2)))))), And(ForAll([S1, V1], Not(vote_S(S1, V1))), ForAll(S1, Not(voted_S(S1))))))

s.add(simulation_relation)
s.add(step)

violation = Const('violation', IntSort())
neg = And(decidedP_L(v1), Not(decidedP_S(v1)), violation == 1)
neg = Or(neg, And(decidedP_L(v2), Not(decidedP_S(v2)), violation == 3))
neg = Or(neg, And(ForAll(N1, Implies(memberP_L(N1, Q1), voteP_L(N1, v1))), ForAll(S1, voteP_S(S1, v1)) == False, violation == 4))
neg = Or(neg, And(ForAll(N1, Implies(memberP_L(N1, Q1), voteP_L(N1, v2))), ForAll(S1, voteP_S(S1, v2)) == False, violation == 5))
neg = Or(neg, And(Not(Or(Exists([Q1], ForAll(N1, Implies(memberP_L(N1, Q1), voteP_L(N1, v1)))), Exists([Q1], ForAll(N1, Implies(memberP_L(N1, Q1), voteP_L(N1, v2)))))), And(ForAll([S1, V1], Not(voteP_S(S1, V1))), ForAll(S1, Not(votedP_S(S1)))) == False, violation == 6))
print(s.check())

s.add(neg)
print(s.check())

if(str(s.check()) == 'sat') :
    f = open('ToyConsensusModel.txt', 'w')
    with redirect_stdout(f):
        m = s.model()
        for k in m:
            print('%s = %s\n' % (k, m[k]))