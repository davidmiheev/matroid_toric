"""Exhaustive confirmation for specific candidate pairs, plus sanity checks on
the Shareshian-Wachs Poincare formula used in sweep.py."""
from itertools import permutations, combinations
from sweep import edges, rank, poincare

def indep_sets(n, E):
    return {frozenset(A) for k in range(len(E) + 1)
            for A in combinations(E, k) if rank(n, A) == k}

def matroid_iso(h1, h2):
    n1, n2 = len(h1), len(h2)
    E1, E2 = edges(h1), edges(h2)
    if len(E1) != len(E2):
        return False, None
    I1, I2 = indep_sets(n1, E1), indep_sets(n2, E2)
    for perm in permutations(E2):
        f = dict(zip(E1, perm))
        if {frozenset(f[e] for e in A) for A in I1} == I2:
            return True, f
    return False, None

def connected(h):
    n = len(h)
    return all(h[j - 1] > j for j in range(1, n))

def report(name, h1, h2):
    iso, f = matroid_iso(h1, h2)
    p1, p2 = poincare(h1), poincare(h2)
    print(f"--- {name}")
    for h in (h1, h2):
        print(f"    h = {h}  n = {len(h)}  dim_C = {len(edges(h))}  "
              f"connected = {connected(h)}  G_h edges = {edges(h)}")
    print(f"    local weight matroids isomorphic (exhaustive) : {iso}")
    print(f"    Poincare X1 = {p1}")
    print(f"    Poincare X2 = {p2}")
    print(f"    Betti numbers differ                          : {p1 != p2}")
    print(f"    => witness valid                              : {iso and p1 != p2}")

print("== sanity checks on the Poincare formula ==")
for n in (3, 4, 5):
    full = tuple([n] * n)
    p = poincare(full)
    qfact = [1]
    for k in range(1, n + 1):                      # [n]_q! coefficients
        blk = [1] * k
        new = [0] * (len(qfact) + k - 1)
        for i, a in enumerate(qfact):
            for j, b in enumerate(blk):
                new[i + j] += a * b
        qfact = new
    print(f"  Fl(C^{n}): computed {p}")
    print(f"           [{n}]_q! {tuple(qfact)}   match = {p == tuple(qfact)}")
    print(f"           total = {sum(p)} = {n}! = {__import__('math').factorial(n)}")

print()
print("== candidate witnesses ==")
report("MINIMAL (disconnected, free local matroid): Fl(C^4), dim 2",
       (2, 3, 3, 4), (2, 2, 4, 4))
report("MINIMAL CONNECTED: Fl(C^5), dim 5, local matroid U_{2,3} + 2 coloops",
       (2, 3, 5, 5, 5), (2, 4, 4, 5, 5))
report("W1 as written in PLAN.md: Fl(C^6), dim 6",
       (3, 3, 3, 6, 6, 6), (3, 3, 5, 5, 5, 6))
report("CONNECTED at n=6: Fl(C^6), dim 6, U_{2,3} + 3 coloops",
       (2, 3, 4, 6, 6, 6), (2, 3, 5, 5, 6, 6))
