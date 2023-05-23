from z3 import *

client_L = DeclareSort('client_L')
client_S = DeclareSort('client_S')
server_L = DeclareSort('server_L')
server_S = DeclareSort('server_S')

link_L = Function('link_L', client_L, server_L, BoolSort())
linkP_L = Function('linkP_L', client_L, server_L, BoolSort())
link_S = Function('link_S', client_S, server_S, BoolSort())
linkP_S = Function('linkP_S', client_S, server_S, BoolSort())
semaphore_L = Function('semaphore_L', server_L, BoolSort())
semaphoreP_L = Function('semaphoreP_L', server_L, BoolSort())
semaphore_S = Function('semaphore_S', server_S, BoolSort())
semaphoreP_S = Function('semaphoreP_S', server_S, BoolSort())

def link_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', client_L)
	tempL_1 = Const('tempL_1', server_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), linkP_L(tempL_0, tempL_1) == link_L(tempL_0, tempL_1))), linkP_L(arg_0, arg_1) == arg_2)

def link_preserved_L():
	tempL_0 = Const('tempL_0', client_L)
	tempL_1 = Const('tempL_1', server_L)
	return ForAll([tempL_0, tempL_1], linkP_L(tempL_0, tempL_1) == link_L(tempL_0, tempL_1))

def link_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', client_S)
	tempS_1 = Const('tempS_1', server_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), linkP_S(tempS_0, tempS_1) == link_S(tempS_0, tempS_1))), linkP_S(arg_0, arg_1) == arg_2)

def link_preserved_S():
	tempS_0 = Const('tempS_0', client_S)
	tempS_1 = Const('tempS_1', server_S)
	return ForAll([tempS_0, tempS_1], linkP_S(tempS_0, tempS_1) == link_S(tempS_0, tempS_1))

def semaphore_set_L(arg_0, arg_1):
	tempL_0 = Const('tempL_0', server_L)
	return And(ForAll([tempL_0], Implies(Not(And(tempL_0 == arg_0)), semaphoreP_L(tempL_0) == semaphore_L(tempL_0))), semaphoreP_L(arg_0) == arg_1)

def semaphore_preserved_L():
	tempL_0 = Const('tempL_0', server_L)
	return ForAll([tempL_0], semaphoreP_L(tempL_0) == semaphore_L(tempL_0))

def semaphore_set_S(arg_0, arg_1):
	tempS_0 = Const('tempS_0', server_S)
	return And(ForAll([tempS_0], Implies(Not(And(tempS_0 == arg_0)), semaphoreP_S(tempS_0) == semaphore_S(tempS_0))), semaphoreP_S(arg_0) == arg_1)

def semaphore_preserved_S():
	tempS_0 = Const('tempS_0', server_S)
	return ForAll([tempS_0], semaphoreP_S(tempS_0) == semaphore_S(tempS_0))

def connect(x, y):
	formula = semaphore_L(y) 
	formula = And(formula, link_set_L(x, y, True))
	formula = And(formula, semaphore_set_L(y, False))

	formula_S = link_set_S(sim(x), sim_server(y), True)
	formula_S = And(formula_S, semaphore_set_S(sim_server(y), False))
	return And(formula, formula_S)

def disconnect(x, y):
	formula = link_L(x, y)
	formula = And(formula, link_set_L(x, y, False))
	formula = And(formula, semaphore_set_L(y, True))

	formula_S = link_set_S(sim(x), sim_server(y), False)
	formula_S = And(formula_S, semaphore_set_S(sim_server(y), True))
	return And(formula, formula_S)

C = Const('C', client_L)
C1 = Const('C1', client_L)
c = Const('c', client_S)
S = Const('S', server_L)
s = Const('s', server_S)

C1 = Const('C1', client_L)
c1 = Const('c1', client_S)
C2 = Const('C2', client_L)
c2 = Const('c2', client_S)
VS = Const('VS', server_L)
vs = Const('vs', server_S)

# Define sim function
sol = Solver()
sim = Function('sim', client_L, client_S)
sol.add(sim(C1) == c1)
sol.add(ForAll(C, Implies(Not(C == C1), sim(C) == c2)))
sol.add(Not(C1 == C2))
sol.add(Not(c1 == c2))

# Define a sim function for server
sim_server = Function('sim_server', server_L, server_S)
sol.add(sim_server(VS) == vs)

# Assert that only one server in both L and S
sol.add(ForAll(S, S == VS))
sol.add(ForAll(s, s == vs))

# Assert that safety property holds prior to step
sol.add(ForAll([C, C1, S], Implies(And(link_L(C, S), link_L(C1, S)), C1 == C)))
# Assert simulation relation
sol.add(Implies(semaphore_L(VS), semaphore_S(vs)))
sol.add(ForAll(C, Implies(link_L(C, VS), link_S(sim(C), vs))))

print(sol.check())

action = Const('action', IntSort())

x, y = Const('x', client_L), Const('y', server_L)

step = And(connect(x, y), action == 1)
step = Xor(step, And(disconnect(x, y), action == 2))

sol.add(step)

# Assert violation of sim after step
violation = Const('violation', IntSort())
violation_sim = And(semaphoreP_L(VS), Not(semaphoreP_S(vs)), violation == 1)
violation_sim = Or(violation_sim, And(linkP_L(C, VS), Not(linkP_S(sim(C), vs)), violation == 2))

sol.add(violation_sim)

print(sol.check())

if(str(sol.check()) == 'sat') :
    print(sol.model())

