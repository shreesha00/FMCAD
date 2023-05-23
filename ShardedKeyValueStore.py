"""

"""

from z3 import *

key = DeclareSort('key')
value = DeclareSort('value')
seqnum = DeclareSort('seqnum')

node_L = DeclareSort('node_L')
node_S = DeclareSort('node_S')

table_L = Function('table_L', node_L, key, value, BoolSort())
tableP_L = Function('tableP_L', node_L, key, value, BoolSort())
transfer_message_L = Function('transfer_message_L', node_L, node_L, key, value, seqnum, BoolSort())
transfer_messageP_L = Function('transfer_messageP_L', node_L, node_L, key, value, seqnum, BoolSort())
ack_msg_L = Function('ack_msg_L', node_L, node_L, seqnum, BoolSort())
ack_msgP_L = Function('ack_msgP_L', node_L, node_L, seqnum, BoolSort())
seqnum_sent_L = Function('seqnum_sent_L', seqnum, BoolSort())
seqnum_sentP_L = Function('seqnum_sentP_L', seqnum, BoolSort())
unacked_L = Function('unacked_L', node_L, node_L, key, value, seqnum, BoolSort())
unackedP_L = Function('unackedP_L', node_L, node_L, key, value, seqnum, BoolSort())
seqnum_recvd_L = Function('seqnum_recvd_L', seqnum, BoolSort())
seqnum_recvdP_L = Function('seqnum_recvdP_L', seqnum, BoolSort())

table_S = Function('table_S', node_S, key, value, BoolSort())
tableP_S = Function('tableP_S', node_S, key, value, BoolSort())
transfer_message_S = Function('transfer_message_S', node_S, node_S, key, value, seqnum, BoolSort())
transfer_messageP_S = Function('transfer_messageP_S', node_S, node_S, key, value, seqnum, BoolSort())
ack_msg_S = Function('ack_msg_S', node_S, node_S, seqnum, BoolSort())
ack_msgP_S = Function('ack_msgP_S', node_S, node_S, seqnum, BoolSort())
seqnum_sent_S = Function('seqnum_sent_S', seqnum, BoolSort())
seqnum_sentP_S = Function('seqnum_sentP_S', seqnum, BoolSort())
unacked_S = Function('unacked_S', node_S, node_S, key, value, seqnum, BoolSort())
unackedP_S = Function('unackedP_S', node_S, node_S, key, value, seqnum, BoolSort())
seqnum_recvd_S = Function('seqnum_recvd_S', seqnum, BoolSort())
seqnum_recvdP_S = Function('seqnum_recvdP_S', seqnum, BoolSort())

# dummy node for quantifiers
N = Const('N', node_L)
N1 = Const('N1', node_L)

M = Const('M', node_S)
M1 = Const('M1', node_S)
N2, N3 = Consts('N2 N3', node_L)

# dummy seqnum for quantifiers
S = Const('S', seqnum)

# dummy key and value for quantifiers
K = Const('K', key)
V = Const('V', value)
V1 = Const('V1', value)
V1 = Const('V1', value)
S1 = Const('S1', seqnum)


# dummy value 
dummy_val = Const('dummy_val', value)

# placeholder value for ownership
owner_val = Const('owner_val', value)

def table_modifier_L(n, k, v, b, preserved = False) :
    if preserved == True : 
        return ForAll([N, K, V], tableP_L(N, K, V) == table_L(N, K, V))
    else : 
        return And(ForAll([N, K, V], Implies(Not(And(N == n, K == k, V == v)), tableP_L(N, K, V) == table_L(N, K, V))), tableP_L(n, k, v) == b)

def transfer_message_modifier_L(n1, n2, k, v, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([N, N1, K, V, S], transfer_messageP_L(N, N1, K, V, S) == transfer_message_L(N, N1, K, V, S))
    else : 
        return And(ForAll([N, N1, K, V, S], Implies(Not(And(N == n1, N1 == n2, K == k, V == v, S == s)), transfer_messageP_L(N, N1, K, V, S) == transfer_message_L(N, N1, K, V, S))), transfer_messageP_L(n1, n2, k, v, s) == b)

def ack_msg_modifier_L(n1, n2, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([N, N1, S], ack_msgP_L(N, N1, S) == ack_msg_L(N, N1, S))
    else : 
        return And(ForAll([N, N1, S], Implies(Not(And(N == n1, N1 == n2, S == s)), ack_msgP_L(N, N1, S) == ack_msg_L(N, N1, S))), ack_msgP_L(n1, n2, s) == b)

def seqnum_sent_modifier_L(s, b, preserved = False) :
    if preserved == True : 
        return ForAll([S], seqnum_sentP_L(S) == seqnum_sent_L(S))
    else : 
        return And(ForAll([S], Implies(Not(S == s), seqnum_sentP_L(S) == seqnum_sent_L(S))), seqnum_sentP_L(s) == b)

def unacked_modifier_L(n1, n2, k, v, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([N, N1, K, V, S], unackedP_L(N, N1, K, V, S) == unacked_L(N, N1, K, V, S))
    else :
        return And(ForAll([N, N1, K, V, S], Implies(Not(And(N == n1, N1 == n2, K == k, V == v, S == s)), unackedP_L(N, N1, K, V, S) == unacked_L(N, N1, K, V, S))), unackedP_L(n1, n2, k, v, s) == b)

def seqnum_recvd_modifier_L(s, b, preserved = False) :
    if preserved == True : 
        return ForAll([S], seqnum_recvdP_L(S) == seqnum_recvd_L(S))
    else : 
        return And(ForAll([S], Implies(Not(S == s), seqnum_recvdP_L(S) == seqnum_recvd_L(S))), seqnum_recvdP_L(s) == b)

def table_modifier_S(n, k, v, b, preserved = False) :
    if preserved == True :
        return ForAll([M, K, V], tableP_S(M, K, V) == table_S(M, K, V))
    else : 
        return And(ForAll([M, K, V], Implies(Not(And(M == n, K == k, V == v)), tableP_S(M, K, V) == table_S(M, K, V))), tableP_S(n, k, v) == b)

def transfer_message_modifier_S(n1, n2, k, v, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([M, M1, K, V, S], transfer_messageP_S(M, M1, K, V, S) == transfer_message_S(M, M1, K, V, S))
    else : 
        return And(ForAll([M, M1, K, V, S], Implies(Not(And(M == n1, M1 == n2, K == k, V == v, S == s)), transfer_messageP_S(M, M1, K, V, S) == transfer_message_S(M, M1, K, V, S))), transfer_messageP_S(n1, n2, k, v, s) == b)


def ack_msg_modifier_S(n1, n2, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([M, M1, S], ack_msgP_S(M, M1, S) == ack_msg_S(M, M1, S))
    else : 
        return And(ForAll([M, M1, S], Implies(Not(And(M == n1, M1 == n2, S == s)), ack_msgP_S(M, M1, S) == ack_msg_S(M, M1, S))), ack_msgP_S(n1, n2, s) == b)

def seqnum_sent_modifier_S(s, b, preserved = False) :
    if preserved == True : 
        return ForAll([S], seqnum_sentP_S(S) == seqnum_sent_S(S))
    else : 
        return And(ForAll([S], Implies(Not(S == s), seqnum_sentP_S(S) == seqnum_sent_S(S))), seqnum_sentP_S(s) == b)

def unacked_modifier_S(n1, n2, k, v, s, b, preserved = False) :
    if preserved == True : 
        return ForAll([M, M1, K, V, S], unackedP_S(M, M1, K, V, S) == unacked_S(M, M1, K, V, S))
    else : 
        return And(ForAll([M, M1, K, V, S], Implies(Not(And(M == n1, M1 == n2, K == k, V == v, S == s)), unackedP_S(M, M1, K, V, S) == unacked_S(M, M1, K, V, S))), unackedP_S(n1, n2, k, v, s) == b)

def seqnum_recvd_modifier_S(s, b, preserved = False) :
    if preserved == True : 
        return ForAll([S], seqnum_recvdP_S(S) == seqnum_recvd_S(S))
    else : 
        return And(ForAll([S], Implies(Not(S == s), seqnum_recvdP_S(S) == seqnum_recvd_S(S))), seqnum_recvdP_S(s) == b)
s = Solver()


simulate = Function('simulate', node_L, node_S)
AL = Const('AL', node_L)
BL = Const('BL', node_L)
AS = Const('AS', node_S)
BS = Const('BS', node_S)
K = Const('K', key)
Vp = Const('Vp', value)
v1 = Const('v1', value)
v2 = Const('v2', value)

# exists more than 2 nodes in L
s.add(Exists(N, And(Not(N == AL), Not(N == BL))))

# only 3 nodes in S
s.add(ForAll(M, Or(M == AS, M == BS)))

# A and B not the same
s.add(Not(AL == BL))
s.add(Not(AS == BS))

s.add(simulate(AL) == AS)
s.add(simulate(BL) == BS)
s.add(ForAll(N, Implies(Not(Or(N == AL, N == BL)), simulate(N) == BS)))

# faulting_key
faulting_key = Const('faulting_key', key)


# assert simulation relation holds prior to the lock-step
s.add(ForAll([N, N1, V, V1], Implies(And(table_L(N, K, V), table_L(N1, K, V1)), And(N == N1, V == V1))))

s.add(ForAll([N, V], Implies(And(table_L(N, faulting_key, V), Or(V == v1, V == v2)), table_S(simulate(N), faulting_key, V))))
s.add(ForAll([N, N1, S], Implies(And(transfer_message_L(N, N1, faulting_key, V, S), Or(V == v1, V == v2)), transfer_message_S(simulate(N), simulate(N1), faulting_key, V, S))))
s.add(ForAll([N, N1, S], Implies(And(unacked_L(N, N1, faulting_key, V, S), Or(V == v1, V == v2)), unacked_S(simulate(N), simulate(N1), faulting_key, V, S))))
s.add(ForAll(S, Implies(Not(seqnum_sent_L(S)), Not(seqnum_sent_S(S)))))
s.add(ForAll(S, Implies(Not(seqnum_recvd_L(S)), Not(seqnum_recvd_S(S)))))

def reshard(n_old, n_new, k, v, s):

    # guard
    formula = And(table_L(n_old, k, v), Not(seqnum_sent_L(s)))

    # modified relations
    formula = And(formula, seqnum_sent_modifier_L(s, True))
    formula = And(formula, table_modifier_L(n_old, k, v, False))
    formula = And(formula, transfer_message_modifier_L(n_old, n_new, k, v, s, True))
    formula = And(formula, unacked_modifier_L(n_old, n_new, k, v, s, True))

    # unchanged relations
    formula = And(formula, ack_msg_modifier_L(n_old, n_new, s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(n_old)
    n_new_S = simulate(n_new)
    
    # repeat steps in S
    formula_S = seqnum_sent_modifier_S(s, True)
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, v, False))
    formula_S = And(formula_S, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True))

    formula_S = And(formula_S, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))

    # all relations preserved if n_old_S == n_new_S 
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, v, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, If(And(k == faulting_key, Or(v == v1, v == v2)), formula_S, formula_S_preserved))

    return formula

def drop_transfer_msg(src, dst, k, v, s):
    
    # guard
    formula = transfer_message_L(src, dst, k, v, s)

    # modified relations
    formula = And(formula, transfer_message_modifier_L(src, dst, k, v, s, False))

    # unchanged relations
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, table_modifier_L(src, k, v, False, True))
    formula = And(formula, unacked_modifier_L(src, dst, k, v, s, True, True))
    formula = And(formula, ack_msg_modifier_L(src, dst, s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    
    # repeat steps in S 
    formula_S = transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, False)

    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, v, False, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S = And(formula_S, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))

    
    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, v, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    
    formula = And(formula, formula_S_preserved)

    return formula

def retransmit(src, dst, k, v, s): 

    # guard
    formula = unacked_L(src, dst, k, v, s)

    # modified relations
    formula = And(formula, transfer_message_modifier_L(src, dst, k, v, s, True))

    # unchanged relations
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, table_modifier_L(src, k, v, False, True))
    formula = And(formula, unacked_modifier_L(src, dst, k, v, s, True, True))
    formula = And(formula, ack_msg_modifier_L(src, dst, s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    # repeat steps in S
    formula_S = transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True)

    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, v, False, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S = And(formula_S, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))


    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, v, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, If(And(k == faulting_key, Or(v == v1, v == v2)), formula_S, formula_S_preserved))

    return formula

def recv_transfer_msg(src, dst, k, v, s):

    # guard 
    formula = And(transfer_message_L(src, dst, k, v, s), Not(seqnum_recvd_L(s)))

    # modified relations
    formula = And(formula, seqnum_recvd_modifier_L(s, True))
    formula = And(formula, table_modifier_L(dst, k, v, True))

    # unchanged relations    
    formula = And(formula, transfer_message_modifier_L(src, dst, k, v, s, False, True))
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, unacked_modifier_L(src, dst, k, v, s, True, True))
    formula = And(formula, ack_msg_modifier_L(src, dst, s, True, True))
    
    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    # repeat steps in S
    formula_S = table_modifier_S(n_new_S, k, v, True)
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True))

    formula_S = And(formula_S, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, False, True))
    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S = And(formula_S, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))

    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, v, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, If(And(k == faulting_key, Or(v == v1, v == v2)), formula_S, formula_S_preserved))

    return formula

def send_ack(src, dst, k, v, s):

    # guard
    formula = And(transfer_message_L(src, dst, k, v, s), seqnum_recvd_L(s))

    # modified relations
    formula = And(formula, ack_msg_modifier_L(src, dst, s, True))

    # unchanged relations
    formula = And(formula, transfer_message_modifier_L(src, dst, k, v, s, False, True))
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, table_modifier_L(src, k, v, False, True))
    formula = And(formula, unacked_modifier_L(src, dst, k, v, s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    # repeat steps in S
    formula_S = ack_msg_modifier_S(n_old_S, n_new_S, s, True)

    formula_S = And(formula_S, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, False, True))
    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, v, False, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))

    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, v, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, v, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, formula_S_preserved)

    return formula

def drop_ack_msg(src, dst, k, s): # figure out why k is passed

    # guard
    formula = ack_msg_L(src, dst, s)

    # modified relations
    formula = And(formula, ack_msg_modifier_L(src, dst, s, False))

    # unchanged relations
    formula = And(formula, transfer_message_modifier_L(src, dst, k, dummy_val, s, False, True))
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, table_modifier_L(src, k, dummy_val, False, True))
    formula = And(formula, unacked_modifier_L(src, dst, k, dummy_val, s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    # repeat steps in S
    formula_S = ack_msg_modifier_S(n_old_S, n_new_S, s, False) 

    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, dummy_val, False, True))
    formula_S = And(formula_S, unacked_modifier_S(n_old_S, n_new_S, k, dummy_val, s, True, True))
    formula_S = And(formula_S, transfer_message_modifier_S(n_old_S, n_new_S, k, dummy_val, s, False, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))

    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, dummy_val, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, formula_S_preserved)

    return formula

def recv_ack_msg(src, dst, k, s):

    # guard
    formula = ack_msg_L(src, dst, s)
    
    # unacked(src, dst, *, *, s) == False
    formula = And(formula, ForAll([N, N1, K, V, S], If(And(N == src, N1 == dst, S == s), unackedP_L(N, N1, K, V, S) == False, unackedP_L(N, N1, K, V, S) == unacked_L(N, N1, K, V, S))))

    # unchanged relations
    formula = And(formula, ack_msg_modifier_L(src, dst, s, False, True))
    formula = And(formula, transfer_message_modifier_L(src, dst, k, dummy_val, s, False, True))
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, table_modifier_L(src, k, dummy_val, False, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))

    n_old_S = simulate(src)
    n_new_S = simulate(dst)
    
    # repeat steps in S
    formula_S = ForAll([M, M1, K, V, S], If(And(M == n_old_S, M1 == n_new_S, S == s), unackedP_S(M, M1, K, V, S) == False, unackedP_S(M, M1, K, V, S) == unacked_S(M, M1, K, V, S)))

    formula_S = And(formula_S, ack_msg_modifier_S(n_old_S, n_new_S, s, False, True)) 
    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, table_modifier_S(n_old_S, k, dummy_val, False, True))
    formula_S = And(formula_S, transfer_message_modifier_S(n_old_S, n_new_S, k, dummy_val, s, False, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))

    # all relations preserved if n_old_S == n_new_S or Not(k == faulting_key)    
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_old_S, k, dummy_val, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_old_S, n_new_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_old_S, n_new_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_old_S, n_new_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))
    
    formula = And(formula, formula_S_preserved)
    return formula

def put(n, k, v):

    # guard 
    formula = Exists([V], table_L(n, k, V))

    # table(n, k, *) == False and table(n, k, v) == True
    formula = And(formula, And(ForAll([N, K, V], Implies(And(N == n, K == k), tableP_L(N, K, V) == False)), tableP_L(n, k, v) == True))

    # unchanged relations
    formula = And(formula, ack_msg_modifier_L(n, n, s, False, True))
    formula = And(formula, transfer_message_modifier_L(n, n, k, dummy_val, s, False, True))
    formula = And(formula, seqnum_sent_modifier_L(s, True, True))
    formula = And(formula, seqnum_recvd_modifier_L(s, True, True))
    formula = And(formula, unacked_modifier_L(n, n, k, dummy_val, s, True, True))

    n_S = simulate(n)    

    # repeat steps in S
    formula_S = And(ForAll([M, K, V], Implies(And(M == n_S, K == k), tableP_S(M, K, V) == False)), tableP_S(n_S, k, v) == True)

    formula_S = And(formula_S, ack_msg_modifier_S(n_S, n_S, s, False, True)) 
    formula_S = And(formula_S, seqnum_sent_modifier_S(s, True, True))
    formula_S = And(formula_S, transfer_message_modifier_S(n_S, n_S, k, dummy_val, s, False, True))
    formula_S = And(formula_S, seqnum_recvd_modifier_S(s, True, True))
    formula_S = And(formula_S, unacked_modifier_S(n_S, n_S, k, dummy_val, s, True, True))
    
    # all relations preserved if Not(k == faulting_key)
    formula_S_preserved = seqnum_sent_modifier_S(s, True, True)
    formula_S_preserved = And(formula_S_preserved, table_modifier_S(n_S, k, dummy_val, False, True))
    formula_S_preserved = And(formula_S_preserved, transfer_message_modifier_S(n_S, n_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, unacked_modifier_S(n_S, n_S, k, dummy_val, s, True, True))
    formula_S_preserved = And(formula_S_preserved, ack_msg_modifier_S(n_S, n_S, s, True, True))
    formula_S_preserved = And(formula_S_preserved, seqnum_recvd_modifier_S(s, True, True))

    formula = And(formula, If(And(k == faulting_key, Or(v == v1, v == v2)), formula_S, formula_S_preserved))

    return formula

k = Const('k', key)
v = Const('v', value)
seq = Const('seq', seqnum)
src = Const('src', node_L)
dst = Const('dst', node_L)
s.add(Not(src == dst))
s.add(Not(v == owner_val))
s.add(ForAll(K, K == faulting_key))

action = Const('action', IntSort())
step_formula = And(reshard(src, dst, k, v, seq), action == 1)
step_formula = Xor(step_formula, And(drop_transfer_msg(src, dst, k, v, seq), action == 2))
step_formula = Xor(step_formula, And(retransmit(src, dst, k, v, seq), action == 3))
step_formula = Xor(step_formula, And(recv_transfer_msg(src, dst, k, v, seq), action == 4))
step_formula = Xor(step_formula, And(send_ack(src, dst, k, v, seq), action == 5))
step_formula = Xor(step_formula, And(drop_ack_msg(src, dst, k, seq), action == 6))
step_formula = Xor(step_formula, And(recv_ack_msg(src, dst, k, seq), action == 7))
step_formula = Xor(step_formula, And(put(src, k, v), action == 8))
s.add(step_formula)

print(s.check())

failure = Const('failure', IntSort())
# assert negation of simulation relation
negation = And(And(tableP_L(N, faulting_key, V), Or(V == v1, V == v2)) == True, tableP_S(simulate(N), faulting_key, V) == False, failure == 1)
negation = Or(negation, And(And(transfer_messageP_L(N, N1, faulting_key, V, S), Or(V == v1, V == v2)) == True, transfer_messageP_S(simulate(N), simulate(N1), faulting_key, V, S) == False, failure == 2))
negation = Or(negation, And(And(unackedP_L(N, N1, faulting_key, V, S), Or(V == v1, V == v2)) == True, unackedP_S(simulate(N), simulate(N1), faulting_key, V, S) == False, failure == 3))
negation = Or(negation, And(Not(seqnum_sentP_L(S)) == True, Not(seqnum_sentP_S(S)) == False, failure == 5))
negation = Or(negation, And(Not(seqnum_recvdP_L(S)) == True, Not(seqnum_recvdP_S(S)) == False, failure == 6))

s.add(negation)
print(s.check())

if str(s.check()) == 'sat' : 
    print(s.model())