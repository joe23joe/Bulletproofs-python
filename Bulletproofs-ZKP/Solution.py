from py_ecc.bn128 import G1, multiply, add, FQ, eq, Z1
from py_ecc.bn128 import curve_order as p
from functools import reduce
import random
import hashlib

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def random_element():
    return random.randint(1, p - 1)

def add_points(*points):
    return reduce(add, points, Z1)

def vector_commit(points, scalars):
    return reduce(add, [multiply(P, int(s) % p) for P, s in zip(points, scalars)], Z1)

def inner_product(a, b):
    return sum(ai * bi for ai, bi in zip(a, b)) % p

def fold(scalar_vec, u):
    n = len(scalar_vec)
    half = n // 2
    u_inv = pow(u, -1, p)
    return [(scalar_vec[i] * u + scalar_vec[i + half] * u_inv) % p for i in range(half)]

def fold_points(point_vec, u):
    n = len(point_vec)
    half = n // 2
    u_inv = pow(u, -1, p)
    return [
        add(multiply(point_vec[i], u), multiply(point_vec[i + half], u_inv))
        for i in range(half)
    ]

# ---------------------------------------------------------------------------
# Random elliptic curve basis
# ---------------------------------------------------------------------------

def hash_to_curve(seed: int):
    """
    Deterministically map an integer seed to a curve point on BN128.
    Uses the try-and-increment method: hash seed → x candidate, check if
    y^2 = x^3 + 3 has a solution (BN128 has b=3), take the square root.
    """
    Fq_order = 21888242871839275222246405745257275088696311157297823662689037894645226208583
    seed_bytes = seed.to_bytes(32, "big")
    for nonce in range(1000):
        h = hashlib.sha256(seed_bytes + nonce.to_bytes(4, "big")).digest()
        x_candidate = int.from_bytes(h, "big") % Fq_order
        rhs = (pow(x_candidate, 3, Fq_order) + 3) % Fq_order
        y_candidate = pow(rhs, (Fq_order + 1) // 4, Fq_order)
        if pow(y_candidate, 2, Fq_order) == rhs:
            pt = (FQ(x_candidate), FQ(y_candidate))
            if eq(multiply(pt, p), Z1):
                return pt
    raise ValueError(f"hash_to_curve failed for seed {seed}")

def gen_basis(n: int, tag: int):
    """Generate n independent basis points deterministically from tag."""
    return [hash_to_curve(tag * 10000 + i) for i in range(n)]

# ---------------------------------------------------------------------------
# Proof data structures
# ---------------------------------------------------------------------------

class Proof:
    def __init__(self, A, Ls, Rs, us, T_blind, s_hat, t_hat, rho_hat, mu):
        self.A       = A        # commitment
        self.Ls      = Ls       # folding L points (log n)
        self.Rs      = Rs       # folding R points (log n)
        self.us      = us       # folding challenges (log n)
        self.T_blind = T_blind  # ZK blinding commitment (base case)
        self.s_hat   = s_hat    # masked scalar a'
        self.t_hat   = t_hat    # masked scalar b'
        self.rho_hat = rho_hat  # masked blinding scalar
        self.mu      = mu       # masked product for ZK base case

    def transmission_size(self):
        # EC points: A + len(Ls) + len(Rs) + T_blind
        # Scalars: s_hat, t_hat, rho_hat, mu + challenges (log n)
        n_points  = 1 + len(self.Ls) + len(self.Rs) + 1
        n_scalars = 4 + len(self.us)
        return n_points, n_scalars

# ---------------------------------------------------------------------------
# Prover
# ---------------------------------------------------------------------------

def prove(a, b, G_vec, H_vec, B, Q):
    """
    Prove knowledge of (a, b, α) such that A = <a,G> + <b,H> + α·B.

    Protocol:
      1. Commit:  A = <a,G> + <b,H> + α·B
      2. Embed v = <a,b> into A via Q:  P = v·Q + A  (inner commitment)
      3. Run log(n) folding rounds, keeping α updated
      4. ZK base case: blind the n=1 witness using μ to hide the product
    """
    assert len(a) == len(b) == len(G_vec) == len(H_vec), "dimension mismatch"
    n = len(a)

    # --- Step 1: Commit ---
    alpha = random_element()
    A_commit = add_points(vector_commit(G_vec, a), vector_commit(H_vec, b), multiply(B, alpha))

    # --- Step 2: Inner product commitment ---
    v = inner_product(a, b)
    P = add_points(multiply(Q, v), A_commit)

    # --- Step 3: Logarithmic folding ---
    cur_a, cur_b   = list(a), list(b)
    cur_G, cur_H   = list(G_vec), list(H_vec)
    cur_alpha      = alpha
    cur_P          = P
    Ls, Rs, us     = [], [], []

    log_n = n.bit_length() - 1
    for _ in range(log_n):
        m    = len(cur_a)
        half = m // 2
        a_L, a_R = cur_a[:half], cur_a[half:]
        b_L, b_R = cur_b[:half], cur_b[half:]
        G_L, G_R = cur_G[:half], cur_G[half:]
        H_L, H_R = cur_H[:half], cur_H[half:]

        v_L = inner_product(a_L, b_R)
        v_R = inner_product(a_R, b_L)
        r_L = random_element()
        r_R = random_element()

        L = add_points(
            multiply(Q, v_L),
            vector_commit(G_R, a_L),
            vector_commit(H_L, b_R),
            multiply(B, r_L)
        )
        R = add_points(
            multiply(Q, v_R),
            vector_commit(G_L, a_R),
            vector_commit(H_R, b_L),
            multiply(B, r_R)
        )
        Ls.append(L)
        Rs.append(R)

        # Verifier challenge (interactive)
        u = random_element()
        us.append(u)
        u2    = pow(u, 2, p)
        u2inv = pow(u2, -1, p)

        cur_a     = fold(cur_a, u)
        cur_b     = fold(cur_b, pow(u, -1, p))
        cur_G     = fold_points(cur_G, pow(u, -1, p))
        cur_H     = fold_points(cur_H, u)
        cur_alpha = (cur_alpha + r_L * u2 + r_R * u2inv) % p
        cur_P     = add_points(multiply(L, u2), cur_P, multiply(R, u2inv))

    # --- Step 4: ZK base case (n = 1) ---
    s, t, rho = cur_a[0], cur_b[0], cur_alpha
    G_f, H_f  = cur_G[0], cur_H[0]

    # Random masks
    r_s   = random_element()
    r_t   = random_element()
    r_rho = random_element()
    r_st  = random_element()      # blinding for the product s*t

    # Blinding commitment T
    T_blind = add_points(
        multiply(Q, r_st),
        multiply(G_f, r_s),
        multiply(H_f, r_t),
        multiply(B, r_rho)
    )

    # Challenge
    c = random_element()

    s_hat   = (r_s   + c * s) % p
    t_hat   = (r_t   + c * t) % p
    rho_hat = (r_rho + c * rho) % p
    mu      = (r_st  + c * s * t) % p

    proof = Proof(A_commit, Ls, Rs, us, T_blind, s_hat, t_hat, rho_hat, mu)

    # Attach final folded points for the verifier (needed to recompute the same state)
    proof._cur_P = cur_P   # final P after folding
    proof._G_f   = G_f
    proof._H_f   = H_f
    proof._c     = c

    return proof

# ---------------------------------------------------------------------------
# Verifier
# ---------------------------------------------------------------------------

def verify(proof, A, G_vec, H_vec, B, Q, v_claim=None):
    """
    Verify the proof.

    The verifier:
      1. Reconstructs P = v·Q + A  (if v is claimed)
      2. Replays the folding using the stored challenges to obtain P', G', H'
      3. Checks the ZK base case equation:
            c·P' + T == μ·Q + ŝ·G' + t̂·H' + ρ̂·B
    """
    n = len(G_vec)

    # Step 1: build P from commitment and claimed inner product
    if v_claim is not None:
        P = add_points(multiply(Q, v_claim), A)
    else:
        P = A

    # Step 2: replay folding using Ls, Rs, us
    cur_P = P
    cur_G = list(G_vec)
    cur_H = list(H_vec)

    for L, R, u in zip(proof.Ls, proof.Rs, proof.us):
        u2    = pow(u, 2, p)
        u2inv = pow(u2, -1, p)
        cur_G = fold_points(cur_G, pow(u, -1, p))
        cur_H = fold_points(cur_H, u)
        cur_P = add_points(multiply(L, u2), cur_P, multiply(R, u2inv))

    # Final folded points
    G_f = cur_G[0]
    H_f = cur_H[0]

    # Step 3: ZK base-case check
    c     = proof._c      # challenge stored from prover
    T     = proof.T_blind
    s_hat = proof.s_hat
    t_hat = proof.t_hat
    rho_hat = proof.rho_hat
    mu    = proof.mu

    lhs = add_points(multiply(cur_P, c), T)
    rhs = add_points(
        multiply(Q, mu),
        multiply(G_f, s_hat),
        multiply(H_f, t_hat),
        multiply(B, rho_hat)
    )
    return eq(lhs, rhs)

# ---------------------------------------------------------------------------
# Test runner
# ---------------------------------------------------------------------------

def run_test(label, a, b):
    print(f"\n{'='*60}")
    print(f"  Test: {label}")
    print(f"  a = {a}")
    print(f"  b = {b}")
    n = len(a)
    assert (n & (n - 1)) == 0 or n == 1, "n must be a power of two"

    G_vec = gen_basis(n, tag=1)
    H_vec = gen_basis(n, tag=2)
    B     = gen_basis(1, tag=9)[0]
    Q     = gen_basis(1, tag=99)[0]

    v = inner_product(a, b)
    print(f"  ⟨a, b⟩ = {v}")

    proof = prove(a, b, G_vec, H_vec, B, Q)
    result = verify(proof, proof.A, G_vec, H_vec, B, Q, v_claim=v)

    n_pts, n_sca = proof.transmission_size()
    log_n = max(1, n.bit_length() - 1)
    print(f"  Transmission: {n_pts} EC points + {n_sca} scalars  (O(log n) = O({log_n}))")
    print(f"  Verification: {'PASS ✓' if result else 'FAIL ✗'}")
    assert result, f"Proof failed for {label}"

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    # test cases
    run_test("a1 · b1  (n=4)",
             a=[808, 140, 166, 209],
             b=[88,  242, 404, 602])

    run_test("a2 · b2  (n=2)",
             a=[433, 651],
             b=[282, 521])

    run_test("a3 · a4  (n=1, now ZK works)",
             a=[222],
             b=[313])

    # Additional random n=4 case
    rng_a = [random.randint(1, 10**6) for _ in range(4)]
    rng_b = [random.randint(1, 10**6) for _ in range(4)]
    run_test("random  (n=4)", a=rng_a, b=rng_b)

    print("\n" + "="*60)
    print("  All proofs verified successfully.")
    print("="*60)