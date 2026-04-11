from py_ecc.bn128 import G1, multiply, add, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
import numpy as np
from functools import reduce
import random

def random_element():
    return random.randint(0, p)

def add_points(*points):
    return reduce(add, points, Z1)

def vector_commit(points, scalars):
    return reduce(add, [multiply(P, i) for P, i in zip(points, scalars)], Z1)

def fold(scalar_vec, u):
    n = len(scalar_vec)
    half = n // 2
    u_inv = pow(u, -1, p)
    return [(scalar_vec[i] * u + scalar_vec[i + half] * u_inv) % p for i in range(half)]

def fold_points(point_vec, u):
    n = len(point_vec)
    half = n // 2
    u_inv = pow(u, -1, p)
    return [add(multiply(point_vec[i], u), multiply(point_vec[i + half], u_inv)) for i in range(half)]

G_vec = [
    (FQ(6286155310766333871795042970372566906087502116590250812133967451320632869759), FQ(2167390362195738854837661032213065766665495464946848931705307210578191331138)),
    (FQ(6981010364086016896956769942642952706715308592529989685498391604818592148727), FQ(8391728260743032188974275148610213338920590040698592463908691408719331517047)),
    (FQ(15884001095869889564203381122824453959747209506336645297496580404216889561240), FQ(14397810633193722880623034635043699457129665948506123809325193598213289127838)),
    (FQ(6756792584920245352684519836070422133746350830019496743562729072905353421352), FQ(3439606165356845334365677247963536173939840949797525638557303009070611741415))
]

H_vec = [
    (FQ(13728162449721098615672844430261112538072166300311022796820929618959450231493), FQ(12153831869428634344429877091952509453770659237731690203490954547715195222919)),
    (FQ(17471368056527239558513938898018115153923978020864896155502359766132274520000), FQ(4119036649831316606545646423655922855925839689145200049841234351186746829602)),
    (FQ(8730867317615040501447514540731627986093652356953339319572790273814347116534), FQ(14893717982647482203420298569283769907955720318948910457352917488298566832491)),
    (FQ(419294495583131907906527833396935901898733653748716080944177732964425683442),  FQ(14467906227467164575975695599962977164932514254303603096093942297417329342836))
]

Q = (FQ(11573005146564785208103371178835230411907837176583832948426162169859927052980),
     FQ(895714868375763218941449355207566659176623507506487912740163487331762446439))

a = [4, 2, 42, 420]
b = [1, 3, 7, 13]

# v = <a, b>
v = sum(ai * bi for ai, bi in zip(a, b)) % p

# P = vQ + <a,G> + <b,H>
P = add_points(
    multiply(Q, v),
    vector_commit(G_vec, a),
    vector_commit(H_vec, b)
)

# L and R as defined in the document:
# L = (a1b2 + a3b4 + ...)Q + (a1G2 + a3G4 + ...) + (b2H1 + b4H3 + ...)
# R = (a2b1 + a4b3 + ...)Q + (a2G1 + a4G3 + ...) + (b1H2 + b3H4 + ...)
def compute_LR(G_vec, H_vec, Q, a, b):
    n = len(a)
    half = n // 2
    a_L, a_R = a[:half], a[half:]
    b_L, b_R = b[:half], b[half:]
    G_L, G_R = G_vec[:half], G_vec[half:]
    H_L, H_R = H_vec[:half], H_vec[half:]

    L = add_points(
        multiply(Q, sum(a_L[i] * b_R[i] for i in range(half)) % p),
        vector_commit(G_R, a_L),
        vector_commit(H_L, b_R)
    )
    R = add_points(
        multiply(Q, sum(a_R[i] * b_L[i] for i in range(half)) % p),
        vector_commit(G_L, a_R),
        vector_commit(H_R, b_L)
    )
    return L, R

# Round 1
L1, R1 = compute_LR(G_vec, H_vec, Q, a, b)
u1 = random_element()

aprime      = fold(a, u1)
bprime      = fold(b, pow(u1, -1, p))
Gprime      = fold_points(G_vec, pow(u1, -1, p))
Hprime      = fold_points(H_vec, u1)
Pprime      = add_points(multiply(L1, pow(u1, 2, p)), P, multiply(R1, pow(u1, -2, p)))

# Round 2
L2, R2 = compute_LR(Gprime, Hprime, Q, aprime, bprime)
u2 = random_element()

aprimeprime = fold(aprime, u2)
bprimeprime = fold(bprime, pow(u2, -1, p))
Gprimeprime = fold_points(Gprime, pow(u2, -1, p))
Hprimeprime = fold_points(Hprime, u2)
Pprimeprime = add_points(multiply(L2, pow(u2, 2, p)), Pprime, multiply(R2, pow(u2, -2, p)))

# Base case n=1: verifier checks P == aG + bH + abQ
assert len(aprimeprime) == 1 and len(bprimeprime) == 1, "final vectors must be length 1"

a_final = aprimeprime[0]
b_final = bprimeprime[0]

assert eq(
    Pprimeprime,
    add_points(
        multiply(Gprimeprime[0], a_final),
        multiply(Hprimeprime[0], b_final),
        multiply(Q, a_final * b_final % p)
    )
), "invalid proof"

print("Proof verified successfully!")