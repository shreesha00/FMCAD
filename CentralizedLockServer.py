from z3 import *
from contextlib import redirect_stdout

agent_L = DeclareSort('agent_L')
agent_S = DeclareSort('agent_S')

queue_L = Function('queue_L', IntSort(), agent_L)
head_L = Const('head_L', IntSort())
tail_L = Const('tail_L', IntSort())

queue_S = Function('queue_S', IntSort(), agent_S)
head_S = Const('head_S', IntSort())
tail_S = Const('tail_S', IntSort())

queueP_L = Function('queueP_L', IntSort(), agent_L)
headP_L = Const('headP_L', IntSort())
tailP_L = Const('tailP_L', IntSort())

queueP_S = Function('queueP_S', IntSort(), agent_S)
headP_S = Const('headP_S', IntSort())
tailP_S = Const('tailP_S', IntSort())

has_key_L = Function('has_key_L', agent_L, BoolSort())
has_key_S = Function('has_key_S', agent_S, BoolSort())
lock_msg_L = Function('lock_msg_L', agent_L, IntSort())
lock_msg_S = Function('lock_msg_S', agent_S, agent_L, IntSort())
unlock_msg_L = Function('unlock_msg_L', agent_L, IntSort())
unlock_msg_S = Function('unlock_msg_S', agent_S, agent_L, IntSort())
grant_msg_L = Function('grant_msg_L', agent_L, IntSort())
grant_msg_S = Function('grant_msg_S', agent_S, agent_L, IntSort())

has_keyP_L = Function('has_keyP_L', agent_L, BoolSort())
has_keyP_S = Function('has_keyP_S', agent_S, BoolSort())
lock_msgP_L = Function('lock_msgP_L', agent_L, IntSort())
lock_msgP_S = Function('lock_msgP_S', agent_S, agent_L, IntSort())
unlock_msgP_L = Function('unlock_msgP_L', agent_L, IntSort())
unlock_msgP_S = Function('unlock_msgP_S', agent_S, agent_L, IntSort())
grant_msgP_L = Function('grant_msgP_L', agent_L, IntSort())
grant_msgP_S = Function('grant_msgP_S', agent_S, agent_L, IntSort())

N = Const('N', agent_L)
S = Const('S', agent_S)
q_it = Const('q_it', IntSort())

s = Solver()

simulate = Function('simulate', agent_L, agent_S)
U_L, V_L = Consts('U_L V_L', agent_L)
U_S, V_S = Consts('U_S V_S', agent_S)

D = Const('D', agent_S)

N_S = Const('N_S', agent_S)
s.add(Not(U_L == V_L))
s.add(Not(U_S == V_S))
s.add(Not(U_S == D))
s.add(Not(V_S == D))
s.add(Exists(N, And(Not(N == U_L), Not(N == V_L))))
s.add(ForAll(N_S, Or(N_S == U_S, N_S == V_S, N_S == D)))

s.add(simulate(U_L) == U_S)
s.add(simulate(V_L) == V_S)
s.add(ForAll(N, Implies(And(Not(N == U_L), Not(N == V_L)), simulate(N) == D)))

def has_key_set_L(n, b) :
    return And(ForAll(N, Implies(Not(N == n), has_keyP_L(N) == has_key_L(N))), has_keyP_L(n) == b)

def has_key_preserved_L() : 
    return ForAll(N, has_keyP_L(N) == has_key_L(N))

def lock_msg_inc_L(n) :
    return And(ForAll(N, Implies(Not(N == n), lock_msgP_L(N) == lock_msg_L(N))), lock_msgP_L(n) == lock_msg_L(n) + 1)

def lock_msg_dec_L(n) :
    return And(ForAll(N, Implies(Not(N == n), lock_msgP_L(N) == lock_msg_L(N))), lock_msgP_L(n) == lock_msg_L(n) - 1)

def lock_msg_preserved_L() :
    return ForAll(N, lock_msgP_L(N) == lock_msg_L(N))
    

def unlock_msg_inc_L(n) :
    return And(ForAll(N, Implies(Not(N == n), unlock_msgP_L(N) == unlock_msg_L(N))), unlock_msgP_L(n) == unlock_msg_L(n) + 1)

def unlock_msg_dec_L(n) :
    return And(ForAll(N, Implies(Not(N == n), unlock_msgP_L(N) == unlock_msg_L(N))), unlock_msgP_L(n) == unlock_msg_L(n) - 1)

def unlock_msg_preserved_L() :
    return ForAll(N, unlock_msgP_L(N) == unlock_msg_L(N))

def grant_msg_inc_L(n) :
    return And(ForAll(N, Implies(Not(N == n), grant_msgP_L(N) == grant_msg_L(N))), grant_msgP_L(n) == grant_msg_L(n) + 1)

def grant_msg_dec_L(n) :
    return And(ForAll(N, Implies(Not(N == n), grant_msgP_L(N) == grant_msg_L(N))), grant_msgP_L(n) == grant_msg_L(n) - 1)

def grant_msg_preserved_L() :
    return ForAll(N, grant_msgP_L(N) == grant_msg_L(N))

def has_key_set_S(n, b) :
    return And(ForAll(S, Implies(Not(S == n), has_keyP_S(S) == has_key_S(S))), has_keyP_S(n) == b)

def has_key_preserved_S() : 
    return ForAll(S, has_keyP_S(S) == has_key_S(S))

def lock_msg_inc_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), lock_msgP_S(S, N) == lock_msg_S(S, N)))), lock_msgP_S(n, sim_n) == lock_msg_S(n, sim_n) + 1)

def lock_msg_dec_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), lock_msgP_S(S, N) == lock_msg_S(S, N)))), lock_msgP_S(n, sim_n) == lock_msg_S(n, sim_n) - 1)

def lock_msg_preserved_S() :
    return ForAll([S, N], Implies(simulate(N) == S, lock_msgP_S(S, N) == lock_msg_S(S, N)))

def unlock_msg_inc_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), unlock_msgP_S(S, N) == unlock_msg_S(S, N)))), unlock_msgP_S(n, sim_n) == unlock_msg_S(n, sim_n) + 1)

def unlock_msg_dec_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), unlock_msgP_S(S, N) == unlock_msg_S(S, N)))), unlock_msgP_S(n, sim_n) == unlock_msg_S(n, sim_n) - 1)

def unlock_msg_preserved_S() :
    return ForAll([S, N], Implies(simulate(N) == S, unlock_msgP_S(S, N) == unlock_msg_S(S, N)))

def grant_msg_inc_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), grant_msgP_S(S, N) == grant_msg_S(S, N)))), grant_msgP_S(n, sim_n) == grant_msg_S(n, sim_n) + 1)

def grant_msg_dec_S(n, sim_n) :
    return And(ForAll([S, N], Implies(simulate(N) == S, Implies(Not(And(S == n, N == sim_n)), grant_msgP_S(S, N) == grant_msg_S(S, N)))), grant_msgP_S(n, sim_n) == grant_msg_S(n, sim_n) - 1)

def grant_msg_preserved_S() :
    return ForAll([S, N], Implies(simulate(N) == S, grant_msgP_S(S, N) == grant_msg_S(S, N)))

def queue_push_L(n) :
    return And(headP_L == head_L, tailP_L == tail_L + 1, ForAll(q_it, Implies(Not(q_it == tail_L), queueP_L(q_it) == queue_L(q_it))), queueP_L(tail_L) == n)

def queue_pop_L() :
    return If(head_L < tail_L, And(headP_L == head_L + 1, tailP_L == tail_L, ForAll(q_it, Implies(And(q_it >= headP_L, q_it < tailP_L), queueP_L(q_it) == queue_L(q_it)))), queue_preserved_L())

def get_head_L() :
    return queue_L(head_L)

def get_head_S() :
    return queue_S(head_S)

def get_headP_L() :
    return queueP_L(headP_L)

def get_headP_S() :
    return queueP_S(headP_S)

def queue_push_S(n) :
    return And(headP_S == head_S, tailP_S == tail_S + 1, ForAll(q_it, Implies(Not(q_it == tail_S), queueP_S(q_it) == queue_S(q_it))), queueP_S(tail_S) == n)

def queue_pop_S() :
    return If(head_S < tail_S, And(headP_S == head_S + 1, tailP_S == tail_S, ForAll(q_it, Implies(And(q_it >= headP_S, q_it < tailP_S), queueP_S(q_it) == queue_S(q_it)))), queue_preserved_S())

def queue_preserved_S() :
    return And(tailP_S == tail_S, headP_S == head_S, ForAll(q_it, Implies(And(q_it >= headP_S, q_it < tailP_S), queueP_S(q_it) == queue_S(q_it))))

def queue_preserved_L() : 
    return And(tailP_L == tail_L, headP_L == head_L, ForAll(q_it, Implies(And(q_it >= headP_L, q_it < tailP_L), queueP_L(q_it) == queue_L(q_it))))



def lock(n) :
    formula = lock_msg_inc_L(n)

    formula = And(formula, unlock_msg_preserved_L())
    formula = And(formula, grant_msg_preserved_L())
    formula = And(formula, has_key_preserved_L())
    formula = And(formula, queue_preserved_L())

    n_s = simulate(n)

    formula = And(formula, lock_msg_inc_S(n_s, n))

    formula = And(formula, unlock_msg_preserved_S())
    formula = And(formula, grant_msg_preserved_S())
    formula = And(formula, has_key_preserved_S())
    formula = And(formula, queue_preserved_S())

    return formula

def unlock(n) :
    formula = (has_key_L(n) == True)

    formula = And(formula, unlock_msg_inc_L(n))
    formula = And(formula, has_key_set_L(n, False))

    formula = And(formula, grant_msg_preserved_L())
    formula = And(formula, lock_msg_preserved_L())
    formula = And(formula, queue_preserved_L())

    n_s = simulate(n)

    formula = And(formula, unlock_msg_inc_S(n_s, n))
    formula = And(formula, has_key_set_S(n_s, False))

    formula = And(formula, grant_msg_preserved_S())
    formula = And(formula, lock_msg_preserved_S())
    formula = And(formula, queue_preserved_S())

    return formula

def handle_grant_msg(n) :
    formula = (grant_msg_L(n) > 0)

    formula = And(formula, has_key_set_L(n, True))
    formula = And(formula, grant_msg_dec_L(n))

    formula = And(formula, lock_msg_preserved_L())
    formula = And(formula, unlock_msg_preserved_L())
    formula = And(formula, queue_preserved_L())

    n_s = simulate(n)

    formula = And(formula, has_key_set_S(n_s, True))
    formula = And(formula, grant_msg_dec_S(n_s, n))

    formula = And(formula, lock_msg_preserved_S())
    formula = And(formula, unlock_msg_preserved_S())
    formula = And(formula, queue_preserved_S())

    return formula

def handle_lock_msg(n) :
    formula = (lock_msg_L(n) > 0)
    formula = And(formula, lock_msg_dec_L(n))
    formula = And(formula, If(head_L >= tail_L, grant_msg_inc_L(n), grant_msg_preserved_L()))
    formula = And(formula, queue_push_L(n))

    formula = And(formula, has_key_preserved_L())
    formula = And(formula, unlock_msg_preserved_L())

    n_s = simulate(n)

    formula = And(formula, lock_msg_dec_S(n_s, n))
    formula = And(formula, If(head_S >= tail_S, grant_msg_inc_S(n_s, n), grant_msg_preserved_S()))
    formula = And(formula, queue_push_S(n_s))

    formula = And(formula, has_key_preserved_S())
    formula = And(formula, unlock_msg_preserved_S())

    return formula

def handle_unlock_msg(n) :
    formula = And(unlock_msg_L(n) > 0)
    formula = And(formula, queue_pop_L())
    formula = And(formula, unlock_msg_dec_L(n))
    formula = And(formula, If(headP_L < tailP_L, grant_msg_inc_L(get_headP_L()), grant_msg_preserved_L()))

    formula = And(formula, lock_msg_preserved_L())
    formula = And(formula, has_key_preserved_L())

    n_s = simulate(n)

    formula = And(formula, queue_pop_S())
    formula = And(formula, unlock_msg_dec_S(n_s, n))
    formula = And(formula, If(headP_S < tailP_S, grant_msg_inc_S(get_headP_S(), get_headP_L()), grant_msg_preserved_S()))

    formula = And(formula, lock_msg_preserved_S())
    formula = And(formula, has_key_preserved_S())

    return formula

N1 = Const('N1', agent_L)
# Assert that safety property holds
s.add(ForAll([N, N1], Implies(And(has_key_L(N), has_key_L(N1)), N == N1)))

# Asserting Simulation Relation
s.add(ForAll(N, lock_msg_L(N) == lock_msg_S(simulate(N), N)))
s.add(ForAll(N, unlock_msg_L(N) == unlock_msg_S(simulate(N), N)))
s.add(ForAll(N, grant_msg_L(N) == grant_msg_S(simulate(N), N)))
s.add(ForAll(N, Implies(has_key_L(N), has_key_S(simulate(N)))))
s.add(And(head_L == head_S, tail_L == tail_S, ForAll(q_it, Implies(And(q_it >= head_L, q_it < tail_L), simulate(queue_L(q_it)) == queue_S(q_it)))))

n = Const('n', agent_L)
action = Const('action', IntSort())
step_formula = And(unlock(n), action == 1)
step_formula = Xor(step_formula, And(unlock(n), action == 2))
step_formula = Xor(step_formula, And(handle_lock_msg(n), action == 3))
step_formula = Xor(step_formula, And(handle_grant_msg(n), action == 4))
step_formula = Xor(step_formula, And(handle_unlock_msg(n), action == 5))

s.add(step_formula)
print(s.check())

# Assert negation of simulation relation
violation = Const('violation', IntSort())
negation = And(Not(lock_msgP_L(N) == lock_msgP_S(simulate(N), N)), violation == 1)
negation = Or(negation, And(Not(unlock_msgP_L(N) == unlock_msgP_S(simulate(N), N)), violation == 2))
negation = Or(negation, And(Not(grant_msgP_L(N) == grant_msgP_S(simulate(N), N)), violation == 3))
negation = Or(negation, And(has_keyP_L(N) == True, has_keyP_S(simulate(N)) == False, violation == 4))
negation = Or(negation, And(And(q_it >= headP_L, q_it < tailP_L) == True, Not(simulate(queueP_L(q_it)) == queueP_S(q_it)), violation == 5))
negation = Or(negation, And(Not(headP_L == headP_S), violation == 6))
negation = Or(negation, And(Not(tailP_L == tailP_S), violation == 7))

s.add(negation)
print(s.check())
if(str(s.check()) == 'sat') :
    f = open('lock_server_output.txt', 'w')
    with redirect_stdout(f):
        m = s.model()
        for k in m:
            print('%s = %s\n' % (k, m[k]))