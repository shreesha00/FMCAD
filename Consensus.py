from z3 import *
from contextlib import redirect_stdout

"""
type value
type quorum
type node

relation member(N:node, Q:quorum)
axiom forall Q1, Q2. exists N. member(N, Q1) & member(N, Q2)

relation vote_request_msg(N:node, M:node)
relation voted(N:node)
relation vote_msg(N:node, M:node)
relation votes(N:node, M:node)
relation leader(N:node)

after init {
    vote_request_msg(N1, N2)  := false
    voted(N) := false
    vote_msg(N1, N2) := false
    votes(N1, N2) := false
    leader(N1) := false
}

action send_request_vote(src: node, dst: node) = {
    vote_request_msg(src, dst) := true
}

action send_vote(src: node, dst: node) = {
    require ~voted(src) & vote_request_msg(dst, src)
    vote_msg(src, dst) := true
    voted(src) = true
}

action recv_vote(n: node, sender: node) = {
    require (vote_msg(sender, n))
    votes(n, sender) := true
}

action become_leader(n: node, q: quorum) = {
    require (member(N, q) -> (votes(n, N)))
    leader(n) := true
}

Backward analysis gives, the following relevant state components
leader(A), leader(B), q. votes(A, *), q. votes(B, *), q. vote_msg(*, A), q. vote_msg(*, B), q. vote_request_msg(A, *), q. vote_request_msg(B, *)
"""
node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')
quorum = DeclareSort('quorum')
value = DeclareSort('value')

member_L = Function('member_L', node_L, quorum, BoolSort())
memberP_L = Function('memberP_L', node_L, quorum, BoolSort())
member_S = Function('member_S', node_S, quorum, BoolSort())
memberP_S = Function('memberP_S', node_S, quorum, BoolSort())
vote_request_msg_L = Function('vote_request_msg_L', node_L, node_L, BoolSort())
vote_request_msgP_L = Function('vote_request_msgP_L', node_L, node_L, BoolSort())
vote_request_msg_S = Function('vote_request_msg_S', node_S, node_S, BoolSort())
vote_request_msgP_S = Function('vote_request_msgP_S', node_S, node_S, BoolSort())
vote_msg_L = Function('vote_msg_L', node_L, node_L, BoolSort())
vote_msgP_L = Function('vote_msgP_L', node_L, node_L, BoolSort())
vote_msg_S = Function('vote_msg_S', node_S, node_S, BoolSort())
vote_msgP_S = Function('vote_msgP_S', node_S, node_S, BoolSort())
voted_L = Function('voted_L', node_L, BoolSort())
votedP_L = Function('votedP_L', node_L, BoolSort())
voted_S = Function('voted_S', node_S, BoolSort())
votedP_S = Function('votedP_S', node_S, BoolSort())
votes_L = Function('votes_L', node_L, node_L, BoolSort())
votesP_L = Function('votesP_L', node_L, node_L, BoolSort())
votes_S = Function('votes_S', node_S, node_S, BoolSort())
votesP_S = Function('votesP_S', node_S, node_S, BoolSort())
leader_L = Function('leader_L', node_L, BoolSort())
leaderP_L = Function('leaderP_L', node_L, BoolSort())
leader_S = Function('leader_S', node_S, BoolSort())
leaderP_S = Function('leaderP_S', node_S, BoolSort())

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

def vote_request_msg_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), vote_request_msgP_L(tempL_0, tempL_1) == vote_request_msg_L(tempL_0, tempL_1))), vote_request_msgP_L(arg_0, arg_1) == arg_2)

def vote_request_msg_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], vote_request_msgP_L(tempL_0, tempL_1) == vote_request_msg_L(tempL_0, tempL_1))

def vote_request_msg_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), vote_request_msgP_S(tempS_0, tempS_1) == vote_request_msg_S(tempS_0, tempS_1))), vote_request_msgP_S(arg_0, arg_1) == arg_2)

def vote_request_msg_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], vote_request_msgP_S(tempS_0, tempS_1) == vote_request_msg_S(tempS_0, tempS_1))

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

def votes_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), votesP_L(tempL_0, tempL_1) == votes_L(tempL_0, tempL_1))), votesP_L(arg_0, arg_1) == arg_2)

def votes_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], votesP_L(tempL_0, tempL_1) == votes_L(tempL_0, tempL_1))

def votes_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), votesP_S(tempS_0, tempS_1) == votes_S(tempS_0, tempS_1))), votesP_S(arg_0, arg_1) == arg_2)

def vote_msg_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), vote_msgP_L(tempL_0, tempL_1) == vote_msg_L(tempL_0, tempL_1))), vote_msgP_L(arg_0, arg_1) == arg_2)

def vote_msg_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], vote_msgP_L(tempL_0, tempL_1) == vote_msg_L(tempL_0, tempL_1))

def vote_msg_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), vote_msgP_S(tempS_0, tempS_1) == vote_msg_S(tempS_0, tempS_1))), vote_msgP_S(arg_0, arg_1) == arg_2)

def vote_msg_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], vote_msgP_S(tempS_0, tempS_1) == vote_msg_S(tempS_0, tempS_1))

def votes_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], votesP_S(tempS_0, tempS_1) == votes_S(tempS_0, tempS_1))

def leader_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), leaderP_L(tempL_0) == leader_L(tempL_0))), leaderP_L(arg_0) == arg_1)

def leader_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], leaderP_L(tempL_0) == leader_L(tempL_0))

def leader_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), leaderP_S(tempS_0) == leader_S(tempS_0))), leaderP_S(arg_0) == arg_1)

def leader_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], leaderP_S(tempS_0) == leader_S(tempS_0))

# consts for universal quantifiers
N, N1, N2, N3 = Consts('N N1 N2 N3', node_L)
S, S1, S2 = Consts('S S1 S2', node_S)
Q2, Q1 = Consts('Q2 Q1', quorum)
V, V1 = Consts('V V1', value)

# violating nodes
A_L, B_L = Consts('A_L B_L', node_L)
A_S, B_S = Consts('A_S B_S', node_S)

def send_request_vote(src, dst):
	formula = True
	formula = And(formula, vote_request_msg_set_L(src, dst, True))
	formula = And(formula, votes_preserved_L())
	formula = And(formula, member_preserved_L())
	formula = And(formula, leader_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, vote_msg_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, votes_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_request_msg_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, leader_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_msg_preserved_S())

	temp_S = Const('temp_S', node_S)
	formula_S = ForAll([S, S1], If(S == temp_S, vote_request_msgP_S(S, S1), vote_request_msgP_S(S, S1) == vote_request_msg_S(S, S1)))
	formula_S = And(formula_S, votes_preserved_S())
	formula_S = And(formula_S, member_preserved_S())
	formula_S = And(formula_S, leader_preserved_S())
	formula_S = And(formula_S, voted_preserved_S())
	formula_S = And(formula_S, vote_msg_preserved_S())

	
	# exists a quorum such that A_L/B_L has requested votes from all the nodes in the quorum
	t_1 = Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), vote_request_msgP_L(src, N))))

	# assign n
	t_2 = If(src == A_L, temp_S == A_S, temp_S == B_S)

	# if either A_L or B_L are the source node and after this action have sent vote requests to a quorum of nodes
	# Do the same with A_S/B_S and all the nodes of the cutoff system
	# if not, the state of the cutoff system stays the same as before
	return And(formula, If(And(Or(src == A_L, src == B_L), t_1), And(t_2, formula_S), formula_S_preserved))

def send_vote(src, dst):
	formula = And(Not(voted_L(src)), vote_request_msg_L(dst, src))
	formula = And(formula, vote_msg_set_L(src, dst, True))
	formula = And(formula, voted_set_L(src, True))
	#formula = And(formula, voted_preserved_L())
	formula = And(formula, vote_request_msg_preserved_L())
	formula = And(formula, member_preserved_L())
	formula = And(formula, leader_preserved_L())
	formula = And(formula, votes_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, votes_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_request_msg_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, leader_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_msg_preserved_S())

	temp_S = Const('temp_S', node_S)

	formula_S = ForAll(S, If(And(Not(voted_S(S)), vote_request_msg_S(temp_S, S)), 
			  				And(vote_msgP_S(S, temp_S), votedP_S(S), ForAll(S1, Implies(Not(S1 == temp_S), vote_msgP_S(S, S1) == vote_msg_S(S, S1)))),
							And(ForAll(S1, vote_msgP_S(S, S1) == vote_msg_S(S, S1)), votedP_S(S) == voted_S(S))))
	formula_S = And(formula_S, member_preserved_S())
	formula_S = And(formula_S, leader_preserved_S())
	formula_S = And(formula_S, vote_request_msg_preserved_S())
	formula_S = And(formula_S, votes_preserved_S())
	
	# set n
	t_2 = If(dst == A_L, temp_S == A_S, temp_S == B_S)

	# exists quorum which has voted for same destination node
	t_1 = Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), vote_msgP_L(N, dst))))

	# if guards are true, trigger send vote action in the cutoff system
	return And(formula, If(And(Or(dst == A_L, dst == B_L), t_1), And(t_2, formula_S), formula_S_preserved))

def recv_vote(n, sender):
	formula = vote_msg_L(sender, n)
	formula = And(formula, votes_set_L(n, sender, True))
	formula = And(formula, vote_request_msg_preserved_L())
	formula = And(formula, member_preserved_L())
	formula = And(formula, leader_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, vote_msg_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, votes_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_request_msg_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, leader_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_msg_preserved_S())

	temp_S = Const('temp_S', node_S)

	# node in the cutoff system
	t_1 = If(n == A_L, temp_S == A_S, temp_S == B_S)

	# do action only if a quorum does so in L
	t_2 = Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), votesP_L(n, N))))

	formula_S = ForAll(S, If(vote_msg_S(S, temp_S), And(votesP_S(temp_S, S), ForAll(S1, Implies(Not(S1 == temp_S), votesP_S(S1, S) == votes_S(S1, S)))), ForAll(S1, votesP_S(S1, S) == votes_S(S1, S))))
	formula_S = And(formula_S, vote_msg_preserved_S())
	formula_S = And(formula_S, voted_preserved_S())
	formula_S = And(formula_S, leader_preserved_S())
	formula_S = And(formula_S, vote_request_msg_preserved_S())
	formula_S = And(formula_S, member_preserved_S())

	return And(formula, If(And(Or(n == A_L, n == B_L), t_2), And(t_1, formula_S), formula_S_preserved))

def become_leader(n, q):
	formula = ForAll(N, Implies(member_L(N, q), votes_L(n, N)))
	formula = And(formula, leader_set_L(n, True))
	formula = And(formula, votes_preserved_L())
	formula = And(formula, vote_request_msg_preserved_L())
	formula = And(formula, member_preserved_L())
	formula = And(formula, voted_preserved_L())
	formula = And(formula, vote_msg_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, votes_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_request_msg_preserved_S())
	formula_S_preserved = And(formula_S_preserved, member_preserved_S())
	formula_S_preserved = And(formula_S_preserved, leader_preserved_S())
	formula_S_preserved = And(formula_S_preserved, voted_preserved_S())
	formula_S_preserved = And(formula_S_preserved, vote_msg_preserved_S())

	temp_S = Const('temp_S', node_S)

	# node in the cutoff system
	t_1 = If(n == A_L, temp_S == A_S, temp_S == B_S)

	formula_S = If(ForAll(S, votes_S(temp_S, S)), leader_set_S(temp_S, True), leader_preserved_S())
	formula_S = And(formula_S, vote_msg_preserved_S())
	formula_S = And(formula_S, voted_preserved_S())
	formula_S = And(formula_S, votes_preserved_S())
	formula_S = And(formula_S, vote_request_msg_preserved_S())
	formula_S = And(formula_S, member_preserved_S())

	return And(formula, If(Or(n == A_L, n == B_L), And(t_1, formula_S), formula_S_preserved))


s = Solver()
s.add(Not(A_L == B_L))
s.add(Not(A_S == B_S))
s.add(ForAll(S, Or(S == A_S, S == B_S)))
action = Const('action', IntSort())
n = Const('n', node_L)
n_1 = Const('n_1', node_L)
q = Const('q', quorum)
v = Const('v', value)

step = And(send_request_vote(n, n_1), action == 1)
step = Xor(step, And(send_vote(n, n_1), action == 2))
step = Xor(step, And(recv_vote(n, n_1), action == 3))
step = Xor(step, And(become_leader(n, q), action == 4))

simulation_relation = ForAll([N, N1], Implies(And(leader_L(N), leader_L(N1)), N == N1))

# Is this enough??
simulation_relation = And(simulation_relation, ForAll([N, N1, N2], Implies(And(vote_msg_L(N, N1), vote_msg_L(N, N2)), N1 == N2)))
simulation_relation = And(simulation_relation, ForAll(N, Exists(N1, vote_msg_L(N, N1)) == voted_L(N)))
simulation_relation = And(simulation_relation, ForAll([Q1, Q2], And(Exists(N1, And(member_L(N1, Q1), member_L(N1, Q2))), Exists(S, And(member_S(S, Q1), member_S(S, Q2))))))
simulation_relation = And(simulation_relation, ForAll([N, N1], Implies(vote_msg_L(N, N1), vote_request_msg_L(N1, N))))
simulation_relation = And(simulation_relation, ForAll([N, N1], Implies(votes_L(N, N1), vote_msg_L(N1, N))))

quorum_on_vote_request_msg = lambda node_l, prime : Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), vote_request_msgP_L(node_l, N)))) if prime else Exists(Q1, ForAll(N, Implies(member_L(N, Q1), vote_request_msg_L(node_l, N))))
quorum_on_vote_msg = lambda node_l, prime: Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), vote_msgP_L(N, node_l)))) if prime else Exists(Q1, ForAll(N, Implies(member_L(N, Q1), vote_msg_L(N, node_l))))
quorum_on_votes = lambda node_l, prime: Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), votesP_L(node_l, N)))) if prime else Exists(Q1, ForAll(N, Implies(member_L(N, Q1), votes_L(node_l, N))))
quorum_on_not_voted = lambda prime : Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), Not(votedP_L(N))))) if prime else Exists(Q1, ForAll(N, Implies(member_L(N, Q1), Not(voted_L(N)))))
quorum_on_voted = lambda prime : Exists(Q1, ForAll(N, Implies(memberP_L(N, Q1), votedP_L(N)))) if prime else Exists(Q1, ForAll(N, Implies(member_L(N, Q1), voted_L(N))))

stage_3 = lambda prime : And(Not(leaderP_S(A_S)), Not(leaderP_S(B_S)), ForAll([S, S1], Not(votesP_S(S, S1)))) if prime else And(Not(leader_S(A_S)), Not(leader_S(B_S)), ForAll([S, S1], Not(votes_S(S, S1))))
stage_2 = lambda prime : And(stage_3(True), ForAll([S, S1], Not(vote_msgP_S(S, S1))), ForAll(S, Not(votedP_S(S)))) if prime else And(stage_3(False), ForAll([S, S1], Not(vote_msg_S(S, S1))), ForAll(S, Not(voted_S(S))))
stage_1 = lambda prime : And(stage_2(True), ForAll([S, S1], Not(vote_request_msgP_S(S, S1)))) if prime else And(stage_2(False), ForAll([S, S1], Not(vote_request_msg_S(S, S1))))

simulation_relation = And(simulation_relation, Implies(quorum_on_vote_request_msg(A_L, False), 
						       						   ForAll(S, vote_request_msg_S(A_S, S))))
simulation_relation = And(simulation_relation, Implies(quorum_on_vote_request_msg(B_L, False), 
						       						   ForAll(S, vote_request_msg_S(B_S, S))))
simulation_relation = And(simulation_relation, Implies(quorum_on_vote_msg(A_L, False), 
						  						       ForAll(S, vote_msg_S(S, A_S))))
simulation_relation = And(simulation_relation, Implies(quorum_on_vote_msg(B_L, False), 
						  						       ForAll(S, vote_msg_S(S, B_S))))
simulation_relation = And(simulation_relation, Implies(quorum_on_votes(A_L, False), 
						  						       ForAll(S, votes_S(A_S, S))))
simulation_relation = And(simulation_relation, Implies(quorum_on_votes(B_L, False), 
						  						       ForAll(S, votes_S(B_S, S))))
simulation_relation = And(simulation_relation, Implies(leader_L(A_L), leader_S(A_S)))
simulation_relation = And(simulation_relation, Implies(leader_L(B_L), leader_S(B_S)))
simulation_relation = And(simulation_relation, Implies(Not(Or(quorum_on_votes(A_L, False), quorum_on_votes(B_L, False))), stage_3(False)))
simulation_relation = And(simulation_relation, Implies(Not(Or(quorum_on_vote_msg(A_L, False), quorum_on_vote_msg(B_L, False))), stage_2(False)))
simulation_relation = And(simulation_relation, Implies(Not(Or(quorum_on_vote_request_msg(A_L, False), quorum_on_vote_request_msg(B_L, False))), stage_1(False)))


s.add(simulation_relation)
s.add(step)
print(s.check())

violation = Const('violation', IntSort())
## define negation
neg = And(quorum_on_vote_request_msg(A_L, True), ForAll(S, vote_request_msgP_S(A_S, S)) == False, violation == 1)
neg = Or(neg, And(quorum_on_vote_request_msg(B_L, True), ForAll(S, vote_request_msgP_S(B_S, S)) == False, violation == 2))
neg = Or(neg, And(quorum_on_vote_msg(A_L, True), ForAll(S, vote_msgP_S(S, A_S)) == False, violation == 3))
neg = Or(neg, And(quorum_on_vote_msg(B_L, True), ForAll(S, vote_msgP_S(S, B_S)) == False, violation == 4))
neg = Or(neg, And(quorum_on_votes(A_L, True), ForAll(S, votesP_S(A_S, S)) == False, violation == 5))
neg = Or(neg, And(quorum_on_votes(B_L, True), ForAll(S, votesP_S(B_S, S)) == False, violation == 6))
neg = Or(neg, And(leaderP_L(A_L), leaderP_S(A_S) == False, violation == 7))
neg = Or(neg, And(leaderP_L(B_L), leaderP_S(B_S) == False, violation == 8))
neg = Or(neg, And(Not(Or(quorum_on_votes(A_L, True), quorum_on_votes(B_L, True))), stage_3(True) == False, violation == 9))
neg = Or(neg, And(Not(Or(quorum_on_vote_msg(A_L, True), quorum_on_vote_msg(B_L, True))), stage_2(True) == False, violation == 10))
neg = Or(neg, And(Not(Or(quorum_on_vote_request_msg(A_L, True), quorum_on_vote_request_msg(B_L, True))), stage_1(True) == False, violation == 11))

s.add(neg)
print(s.check())

if(str(s.check()) == 'sat') :
    f = open('ConsensusModel.txt', 'w')
    with redirect_stdout(f):
        m = s.model()
        for k in m:
            print('%s = %s\n' % (k, m[k]))
