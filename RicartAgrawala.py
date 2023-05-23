from z3 import *

node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')

"""
type node

relation requested(N1: node, N2:node)
relation replied(N1:node, N2:node)
relation holds(N:node)

after init {
    requested(N1, N2) := false;
    replied(N1, N2) := false;
    holds(N) := false;
}

action request(requester: node, responder: node) = {
    require ~requested(requester, responder);
    require requester ~= responder;
    requested(requester, responder) := true;
}

action reply(requester: node, responder: node) = {
    require ~replied(requester, responder);
    require ~holds(responder);
    require ~replied(responder, requester);
    require requested(requester, responder);
    require requester ~= responder;
    requested(requester, responder) := false;
    replied(requester, responder) := true;
}

action enter(requester: node) = {
    require N ~= requester -> replied(requester, N);
    holds(requester) := true;
}

action leave(requester: node) = {
    require holds(requester);
    holds(requester) := false;
    replied(requester, N) := false;
}

"""
requested_L = Function('requested_L', node_L, node_L, BoolSort())
requestedP_L = Function('requestedP_L', node_L, node_L, BoolSort())
requested_S = Function('requested_S', node_S, node_S, BoolSort())
requestedP_S = Function('requestedP_S', node_S, node_S, BoolSort())
replied_L = Function('replied_L', node_L, node_L, BoolSort())
repliedP_L = Function('repliedP_L', node_L, node_L, BoolSort())
replied_S = Function('replied_S', node_S, node_S, BoolSort())
repliedP_S = Function('repliedP_S', node_S, node_S, BoolSort())
holds_L = Function('holds_L', node_L, BoolSort())
holdsP_L = Function('holdsP_L', node_L, BoolSort())
holds_S = Function('holds_S', node_S, BoolSort())
holdsP_S = Function('holdsP_S', node_S, BoolSort())


N, N1, N2 = Consts('N N1 N2', node_L)
M, M1, M2 = Consts('M M1 M2', node_S)

A_L, B_L = Consts('A_L B_L', node_L)
A_S, B_S = Consts('A_S B_S', node_S)

sol = Solver()
sol.add(Not(A_L == B_L))
sol.add(Not(A_S == B_S))

sim = Function('sim', node_L, node_S)
sol.add(sim(A_L) == A_S)
sol.add(sim(B_L) == B_S)

sol.add(ForAll(M, Or(M == A_S, M == B_S)))

def requested_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), requestedP_L(tempL_0, tempL_1) == requested_L(tempL_0, tempL_1))), requestedP_L(arg_0, arg_1) == arg_2)

def requested_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], requestedP_L(tempL_0, tempL_1) == requested_L(tempL_0, tempL_1))

def requested_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), requestedP_S(tempS_0, tempS_1) == requested_S(tempS_0, tempS_1))), requestedP_S(arg_0, arg_1) == arg_2)

def requested_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], requestedP_S(tempS_0, tempS_1) == requested_S(tempS_0, tempS_1))

def replied_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), repliedP_L(tempL_0, tempL_1) == replied_L(tempL_0, tempL_1))), repliedP_L(arg_0, arg_1) == arg_2)

def replied_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], repliedP_L(tempL_0, tempL_1) == replied_L(tempL_0, tempL_1))

def replied_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), repliedP_S(tempS_0, tempS_1) == replied_S(tempS_0, tempS_1))), repliedP_S(arg_0, arg_1) == arg_2)

def replied_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], repliedP_S(tempS_0, tempS_1) == replied_S(tempS_0, tempS_1))

def holds_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', node_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), holdsP_L(tempL_0) == holds_L(tempL_0))), holdsP_L(arg_0) == arg_1)

def holds_preserved_L():
	tempL_0 = Const('tempL_0', node_L)
	return ForAll([tempL_0], holdsP_L(tempL_0) == holds_L(tempL_0))

def holds_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', node_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), holdsP_S(tempS_0) == holds_S(tempS_0))), holdsP_S(arg_0) == arg_1)

def holds_preserved_S():
	tempS_0 = Const('tempS_0', node_S)
	return ForAll([tempS_0], holdsP_S(tempS_0) == holds_S(tempS_0))

def request(requester, responder):
	formula = And(Not(requested_L(requester, responder)), Not(requester == responder))
	formula = And(formula, requested_set_L(requester, responder, True))
	formula = And(formula, replied_preserved_L())
	formula = And(formula, holds_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, requested_preserved_S())
	formula_S_preserved = And(formula_S_preserved, replied_preserved_S())
	formula_S_preserved = And(formula_S_preserved, holds_preserved_S())

	formula_S = requested_set_S(sim(requester), sim(responder), True)
	formula_S = And(formula_S, replied_preserved_S())
	formula_S = And(formula_S, holds_preserved_S())
	
	formula = And(formula, If(And(Or(And(requester == A_L, responder == B_L), And(requester == B_L, responder == A_L)), And(Not(requested_S(sim(requester), sim(responder))), Not(sim(requester) == sim(responder)))), formula_S, formula_S_preserved))

	return formula

def reply(requester, responder):
	formula = And(Not(replied_L(requester, responder)), Not(holds_L(responder)), Not(replied_L(responder, requester)), requested_L(requester, responder), Not(requester == responder))
	formula = And(formula, requested_set_L(requester, responder, False))
	formula = And(formula, replied_set_L(requester, responder, True))
	formula = And(formula, holds_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, requested_preserved_S())
	formula_S_preserved = And(formula_S_preserved, replied_preserved_S())
	formula_S_preserved = And(formula_S_preserved, holds_preserved_S())

	formula_S = requested_set_S(sim(requester), sim(responder), False)
	formula_S = And(formula_S, replied_set_S(sim(requester), sim(responder), True))
	formula_S = And(formula_S, holds_preserved_S())

	formula = And(formula, If(And(Or(And(requester == A_L, responder == B_L), And(requester == B_L, responder == A_L)), And(Not(replied_S(sim(requester), sim(responder))), Not(holds_S(sim(responder))), Not(replied_S(sim(responder), sim(requester))), requested_S(sim(requester), sim(responder)), Not(sim(requester) == sim(responder)))), formula_S, formula_S_preserved))

	return formula

def enter(requester):
	formula = ForAll(N, Implies(Not(N == requester), replied_L(requester, N)))
	formula = And(formula, holds_set_L(requester, True))
	formula = And(formula, requested_preserved_L())
	formula = And(formula, replied_preserved_L())

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, requested_preserved_S())
	formula_S_preserved = And(formula_S_preserved, replied_preserved_S())
	formula_S_preserved = And(formula_S_preserved, holds_preserved_S())

	formula_S = holds_set_S(sim(requester), True)
	formula_S = And(formula_S, requested_preserved_S())
	formula_S = And(formula_S, replied_preserved_S())

	formula = And(formula, If(And(Or(requester == A_L, requester == B_L), ForAll(M, Implies(Not(M == sim(requester)), replied_S(sim(requester), M)))), formula_S, formula_S_preserved))

	return formula

def leave(requester):
	formula = holds_L(requester)
	formula = And(formula, holds_set_L(requester, False))
	formula = And(formula, requested_preserved_L())
	formula = And(formula, ForAll(N, repliedP_L(requester, N) == False), ForAll([N, N1], Implies(Not(N == requester), repliedP_L(N, N1) == replied_L(N, N1))))

	formula_S_preserved = True
	formula_S_preserved = And(formula_S_preserved, requested_preserved_S())
	formula_S_preserved = And(formula_S_preserved, replied_preserved_S())
	formula_S_preserved = And(formula_S_preserved, holds_preserved_S())

	formula_S = holds_set_S(sim(requester), False)
	formula_S = And(formula_S, requested_preserved_S())
	formula_S = And(formula_S, ForAll(M, repliedP_S(sim(requester), M) == False), ForAll([M, M1], Implies(Not(M == sim(requester)), repliedP_S(M, M1) == replied_S(M, M1))))

	formula = And(formula, If(And(Or(requester == A_L, requester == B_L), holds_S(sim(requester))), formula_S, formula_S_preserved))

	return formula

action = Const('action', IntSort())

requester = Const('requester', node_L)
responder = Const('responder', node_L)

sim_relation = ForAll([N1, N2], Implies(And(holds_L(N1), holds_L(N2)), N1 == N2))

sim_relation = And(sim_relation, holds_L(A_L) == holds_S(A_S))
sim_relation = And(sim_relation, holds_L(B_L) == holds_S(B_S))
sim_relation = And(sim_relation, requested_L(A_L, B_L) == requested_S(A_S, B_S))
sim_relation = And(sim_relation, requested_L(B_L, A_L) == requested_S(B_S, A_S))
sim_relation = And(sim_relation, replied_L(A_L, B_L) == replied_S(A_S, B_S))
sim_relation = And(sim_relation, replied_L(B_L, A_L) == replied_S(B_S, A_S))

sol.add(sim_relation)
step = And(request(requester, responder), action == 1)
step = Xor(step, And(reply(requester, responder), action == 2))
step = Xor(step, And(enter(requester), action == 3))
step = Xor(step, And(leave(requester), action == 4))

sol.add(step)

violation = Const('violation', IntSort())

negation = And(Not(holdsP_L(A_L) == holdsP_S(A_S)), violation == 1)
negation = Or(negation, And(Not(holdsP_L(B_L) == holdsP_S(B_S)), violation == 2))
negation = Or(negation, And(Not(requestedP_L(A_L, B_L) == requestedP_S(A_S, B_S)), violation == 3))
negation = Or(negation, And(Not(requestedP_L(B_L, A_L) == requestedP_S(B_S, A_S)), violation == 4))
negation = Or(negation, And(Not(repliedP_L(A_L, B_L) == repliedP_S(A_S, B_S)), violation == 5))
negation = Or(negation, And(Not(repliedP_L(B_L, A_L) == repliedP_S(B_S, A_S)), violation == 6))

print(sol.check())
sol.add(negation)

print(sol.check())
if(str(sol.check()) == 'sat') :
    print(sol.model())

