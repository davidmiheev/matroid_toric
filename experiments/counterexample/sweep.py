"""Track A sweep: matroid-matched / Betti-mismatched pairs of regular semisimple
Hessenberg varieties Hess(M,h) in Fl(C^n).

Facts used:
 * tangent weights at the fixed point w are e_{w(i)} - e_{w(j)} over the edges
   (j,i), j < i <= h(j), of the indifference graph G_h, so the local weight
   matroid is the cycle matroid M(G_h) at EVERY fixed point;
 * (Shareshian-Wachs / Tymoczko) Poin(Hess(M,h), q) = sum_w q^{2 inv_{G_h}(w)}.
   Summing over all of S_n makes the statistic's w-vs-w^{-1} convention
   irrelevant: w -> w^{-1} is a bijection, so the generating function is the
   same either way.
Matroids are compared by Tutte polynomial first (fast, strong), then candidate
pairs are confirmed by an exhaustive ground-set bijection check.
"""
from itertools import permutations, combinations
from collections import defaultdict
import sys

def hessenberg_functions(n):
    def rec(j, lo):
        if j > n:
            yield ()
            return
        for v in range(max(j, lo), n + 1):
            for rest in rec(j + 1, v):
                yield (v,) + rest
    return list(rec(1, 1))

def edges(h):
    n = len(h)
    return [(j, i) for j in range(1, n + 1) for i in range(j + 1, h[j - 1] + 1)]

def rank(n, A):
    parent = list(range(n + 1))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    r = 0
    for (a, b) in A:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
            r += 1
    return r

def poincare(h):
    """coefficients c_k of sum_w q^{2k}, indexed by k."""
    n = len(h)
    E = edges(h)
    c = defaultdict(int)
    for w in permutations(range(1, n + 1)):
        inv = sum(1 for (j, i) in E if w[j - 1] > w[i - 1])
        c[inv] += 1
    return tuple(c[k] for k in range(len(E) + 1))

def tutte(h):
    """T(x,y) as a dict {(i,j): coeff} via the rank-generating expansion."""
    n = len(h)
    E = edges(h)
    rE = rank(n, E)
    coeff = defaultdict(int)
    for size in range(len(E) + 1):
        for A in combinations(E, size):
            rA = rank(n, A)
            coeff[(rE - rA, size - rA)] += 1   # in (x-1),(y-1) basis
    return tuple(sorted(coeff.items()))

def matroid_iso(n1, E1, n2, E2):
    """exhaustive check that the cycle matroids are isomorphic."""
    if len(E1) != len(E2) or rank(n1, E1) != rank(n2, E2):
        return False
    ind1 = {frozenset(A) for size in range(len(E1) + 1)
            for A in combinations(E1, size) if rank(n1, A) == size}
    for perm in permutations(E2):
        f = dict(zip(E1, perm))
        if all(frozenset(f[e] for e in A) in
               {frozenset(B) for size in range(len(E2) + 1)
                for B in combinations(E2, size) if rank(n2, B) == size}
               for A in ind1):
            return True
    return False

def sweep(n):
    print(f"=== n = {n} ===")
    buckets = defaultdict(list)
    for h in hessenberg_functions(n):
        buckets[tutte(h)].append(h)
    found = []
    for _, hs in buckets.items():
        if len(hs) < 2:
            continue
        by_poin = defaultdict(list)
        for h in hs:
            by_poin[poincare(h)].append(h)
        if len(by_poin) > 1:
            found.append((hs, dict(by_poin)))
    if not found:
        print("  no matroid-matched, Betti-mismatched pair")
    for hs, by_poin in found:
        print(f"  matroid class shared by {len(hs)} Hessenberg functions:")
        for p, hl in by_poin.items():
            print(f"    Poincare (coeffs of q^2k) = {p}")
            for h in hl:
                print(f"        h = {h}   edges = {edges(h)}")
    return found

if __name__ == "__main__":
    for n in (4, 5, 6):
        sweep(n)
        sys.stdout.flush()
