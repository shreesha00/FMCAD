from z3 import *
from contextlib import redirect_stdout

node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')
ID = DeclareSort('ID')

pnd_L = Function('pnd_L', ID, node_L, BoolSort())
pndP_L = Function('pndP_L', ID, node_L, BoolSort())
pnd_S = Function('pnd_S', ID, node_S, BoolSort())
pndP_S = Function('pndP_S', ID, node_S, BoolSort())
leader_L = Function('leader_L', node_L, BoolSort())
leaderP_L = Function('leaderP_L', node_L, BoolSort())
leader_S = Function('leader_S', node_S, BoolSort())
leaderP_S = Function('leaderP_S', node_S, BoolSort())

def pnd_set_L(arg_0, arg_1, arg_2):
	tempL_0 = Const('tempL_0', ID)
	tempL_1 = Const('tempL_1', node_L)
	return And(ForAll([tempL_0, tempL_1], Implies(Not(And(tempL_0 == arg_0, tempL_1 == arg_1)), pndP_L(tempL_0, tempL_1) == pnd_L(tempL_0, tempL_1))), pndP_L(arg_0, arg_1) == arg_2)

def pnd_preserved_L():
	tempL_0 = Const('tempL_0', ID)
	tempL_1 = Const('tempL_1', node_L)
	return ForAll([tempL_0, tempL_1], pndP_L(tempL_0, tempL_1) == pnd_L(tempL_0, tempL_1))

def pnd_set_S(arg_0, arg_1, arg_2):
	tempS_0 = Const('tempS_0', ID)
	tempS_1 = Const('tempS_1', node_S)
	return And(ForAll([tempS_0, tempS_1], Implies(Not(And(tempS_0 == arg_0, tempS_1 == arg_1)), pndP_S(tempS_0, tempS_1) == pnd_S(tempS_0, tempS_1))), pndP_S(arg_0, arg_1) == arg_2)

def pnd_preserved_S():
	tempS_0 = Const('tempS_0', ID)
	tempS_1 = Const('tempS_1', node_S)
	return ForAll([tempS_0, tempS_1], pndP_S(tempS_0, tempS_1) == pnd_S(tempS_0, tempS_1))

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

s = Solver()
# total order on the IDs
le = Function('le', ID, ID, BoolSort())
id1, id2, id3 = Consts('id1 id2 id3', ID)
s.add(ForAll(id1, le(id1, id1) == True))
s.add(ForAll([id1, id2, id3], Implies(And(le(id1, id2) == True, le(id2, id3) == True), le(id1, id3) == True)))
s.add(ForAll([id1, id2], Implies(And(le(id1, id2) == True, le(id2, id1) == True), id1 == id2)))
s.add(ForAll([id1, id2], Or(le(id1, id2) == True, le(id2, id1) == True)))

id_L = Function('id_L', node_L, ID)
id_S = Function('id_S', node_S, ID)

# defining the ring topology for the larger system
btw_L = Function('btw_L', node_L, node_L, node_L, BoolSort())
n1, n2, n3, n4 = Consts('n1 n2 n3 n4', node_L)
s.add(ForAll([n1, n2, n3], Implies(btw_L(n1, n2, n3) == True, btw_L(n2, n3, n1) == True)))
s.add(ForAll([n1, n2, n3, n4], Implies(And(btw_L(n1, n2, n3) == True, btw_L(n1, n3, n4) == True), btw_L(n1, n2, n4) == True)))
s.add(ForAll([n1, n2, n3], Implies(btw_L(n1, n2, n3) == True, btw_L(n1, n3, n2) == False)))
s.add(ForAll([n1, n2, n3], Implies(And(n1 != n2, n2 != n3, n3 != n1), Or(btw_L(n1, n2, n3) == True, btw_L(n1, n3, n2) == True))))

N, N1 = Consts('N N1', node_L)
S, S1 = Consts('S S1', node_S)

AL, BL = Consts('AL BL', node_L)
AS, BS = Consts('AS BS', node_S)

s.add(ForAll(S, Or(S == AS, S == BS)))
s.add(ForAll([N, N1], Implies(Not(N == N1), Not(id_L(N) == id_L(N1)))))
s.add(Not(AL == BL))
s.add(Not(AS == BS))
s.add(id_L(AL) == id_S(AS))
s.add(id_L(BL) == id_S(BS))

sim = Function('sim', node_L, node_S)
s.add(ForAll(N, Implies(btw_L(AL, N, BL) == True, sim(N) == BS)))
s.add(ForAll(N, Implies(btw_L(BL, N, AL) == True, sim(N) == AS)))
s.add(sim(AL) == AS)
s.add(sim(BL) == BS)

next = Function('next', node_S, node_S)
s.add(next(AS) == BS)
s.add(next(BS) == AS)

def send(n, n1):
    formula = ForAll(N, Implies(And(Not(N == n), Not(N == n1)), btw_L(n, n1, N) == True))
    formula = And(formula, pnd_set_L(id_L(n), n1, True))
    formula = And(formula, leader_preserved_L())

    formula_S_preserved = True
    formula_S_preserved = And(formula_S_preserved, pnd_preserved_S())
    formula_S_preserved = And(formula_S_preserved, leader_preserved_S())

    n_S = Const('n_S', node_S)
    t1 = sim(n) == n_S
    formula_S = pnd_set_S(id_S(n_S), next(n_S), True)
    formula_S = And(formula_S, leader_preserved_S())

    return And(formula, If(Or(n == AL, n == BL), And(t1, formula_S), formula_S_preserved))

def become_leader(n):
    formula = pnd_L(id_L(n), n)
    formula = And(formula, leader_set_L(n, True))
    formula = And(formula, pnd_preserved_L())

    formula_S_preserved = True
    formula_S_preserved = And(formula_S_preserved, pnd_preserved_S())
    formula_S_preserved = And(formula_S_preserved, leader_preserved_S())

    n_S = Const('n_S', node_S)
    t1 = sim(n) == n_S
    formula_S = If(pnd_S(id_S(n_S), n_S), leader_set_S(n_S, True), leader_preserved_S())
    formula_S = And(formula_S, pnd_preserved_S())

    return And(formula, If(Or(n == AL, n == BL), And(t1, formula_S), formula_S_preserved))

def forward(n, n1, id):
    formula = And(ForAll(N, Implies(And(Not(N == n), Not(N == n1)), btw_L(n, n1, N) == True)), pnd_L(id, n), le(id_L(n), id))
    formula = And(formula, pnd_set_L(id, n1, True))
    formula = And(formula, leader_preserved_L())

    formula_S_preserved = True
    formula_S_preserved = And(formula_S_preserved, pnd_preserved_S())
    formula_S_preserved = And(formula_S_preserved, leader_preserved_S())

    n_S = Const('n_S', node_S)
    t1 = n_S == sim(n)
    formula_S = If(And(pnd_S(id, n_S), le(id_S(n_S), id)), pnd_set_S(id, next(n_S), True), pnd_preserved_S())
    formula_S = And(formula_S, leader_preserved_S())
    return And(formula, If(Not(sim(n) == sim(n1)), And(t1, formula_S), formula_S_preserved))

action = Const('action', IntSort())
n = Const('n', node_L)
n_1 = Const('n_1', node_L)
id = Const('id', ID)

step = And(send(n, n_1), action == 1)
step = Xor(step, And(become_leader(n), action == 2))
step = Xor(step, And(forward(n, n_1, id), action == 3))

simulation_relation = ForAll([N, N1], Implies(And(leader_L(N), leader_L(N1)), N == N1))
simulation_relation = And(simulation_relation, ForAll(N, Implies(pnd_L(id_L(AL), N), pnd_S(id_S(AS), sim(N)))))
simulation_relation = And(simulation_relation, ForAll(N, Implies(pnd_L(id_L(BL), N), pnd_S(id_S(BS), sim(N)))))
simulation_relation = And(simulation_relation, Implies(leader_L(AL), leader_S(AS)))
simulation_relation = And(simulation_relation, Implies(leader_L(BL), leader_S(BS)))

s.add(simulation_relation)
s.add(step)
print(s.check())
violation = Const('violation', IntSort())
neg = And(pndP_L(id_L(AL), N), pndP_S(id_S(AS), sim(N)) == False, violation == 1)
neg = Or(neg, And(pndP_L(id_L(BL), N), pndP_S(id_S(BS), sim(N)) == False, violation == 2))
neg = Or(neg, And(leaderP_L(AL), leaderP_S(AS) == False, violation == 3))
neg = Or(neg, And(leaderP_L(BL), leaderP_S(BS) == False, violation == 4))

s.add(neg)
print(s.check())
if(str(s.check()) == 'sat') :
    f = open('LEModel.txt', 'w')
    with redirect_stdout(f):
        m = s.model()
        for k in m:
            print('%s = %s\n' % (k, m[k]))