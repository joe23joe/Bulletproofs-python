# https://rareskills.io/post/pedersen-commitment

from py_ecc.bn128 import is_on_curve, FQ
from py_ecc.fields import field_properties
from hashlib import sha256
from libnum import has_sqrtmod_prime_power, sqrtmod_prime_power

field_mod = field_properties["bn128"]["field_modulus"]
b = 3  # curve equation: y^2 = x^3 + b

seed = "RareSkills"
n = 5  # number of points we want to generate
vector_basis = []

x = int(sha256(seed.encode('ascii')).hexdigest(), 16) % field_mod
entropy = 0

for _ in range(n):
    # Find a valid y for the curve
    while not has_sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1):
        x = (x + 1) % field_mod
        entropy += 1

    # Choose upper/lower point depending on entropy
    y_candidates = list(sqrtmod_prime_power((x**3 + b) % field_mod, field_mod, 1))
    y = y_candidates[entropy % 2]
    point = (FQ(x), FQ(y))

    assert is_on_curve(point, b), "sanity check failed"
    vector_basis.append(point)

    # Generate new x for the next point using hash of the current one
    x = int(sha256(f"{x}{y}".encode('ascii')).hexdigest(), 16) % field_mod
    entropy += 1

print("Generated points:")
for p in vector_basis:
    print(p)
