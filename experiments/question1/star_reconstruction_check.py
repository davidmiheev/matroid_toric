"""Check the star lemma behind the Whitney-free proof of Theorem A (PROOF.md, §2).

Claim: if a bijection phi of the edges of a simple graph preserves adjacency of edges and the
property "three edges form a triangle", then phi is induced by a permutation of the
non-isolated vertices. (Without the triangle condition this fails for K_3, K_{1,3}+e, K_4-e and
K_4, the exceptions to Whitney's theorem in Jung's form.)

For every graph with at most N vertices (nauty-geng), all such edge permutations are found by
backtracking, and each one is checked to be induced by a vertex permutation. We also count the
edge permutations that preserve adjacency only, to show that the triangle condition matters.

Usage: python3 star_reconstruction_check.py N
"""
import subprocess, sys
from itertools import combinations, permutations


def graphs(n):
    out = subprocess.run(["nauty-geng", "-q", str(n)], capture_output=True, text=True,
                         check=True).stdout
    for line in out.split():
        data = [ord(c) - 63 for c in line[1:]]
        bits = [(b >> (5 - i)) & 1 for b in data for i in range(6)]
        E, k = [], 0
        for j in range(1, n):
            for i in range(j):
                if bits[k]: E.append(frozenset((i, j)))
                k += 1
        yield E


def edge_maps(E, use_triangles):
    m = len(E)
    adj = [[bool(E[a] & E[b]) and a != b for b in range(m)] for a in range(m)]
    tri = {frozenset(t) for t in combinations(range(m), 3)
           if len(E[t[0]] | E[t[1]] | E[t[2]]) == 3}
    img = [None] * m; used = [False] * m
    def ok(a):
        for b in range(a):
            if adj[a][b] != adj[img[a]][img[b]]: return False
        if use_triangles:
            for b, c in combinations(range(a), 2):
                if (frozenset((a, b, c)) in tri) != (frozenset((img[a], img[b], img[c])) in tri):
                    return False
        return True
    def rec(a):
        if a == m:
            yield list(img); return
        for x in range(m):
            if not used[x]:
                img[a] = x; used[x] = True
                if ok(a): yield from rec(a + 1)
                used[x] = False
    yield from rec(0)


def induced(E, phi, n):
    V = sorted(set().union(*E)) if E else []
    target = [E[phi[i]] for i in range(len(E))]
    for p in permutations(V):
        pm = dict(zip(V, p))
        if all(frozenset(pm[v] for v in E[i]) == target[i] for i in range(len(E))):
            return True
    return False


N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
bad = 0
for n in range(1, N + 1):
    count = with_tri = adj_only_not_induced = 0
    for E in graphs(n):
        count += 1
        for phi in edge_maps(E, True):
            with_tri += 1
            if not induced(E, phi, n):
                bad += 1; print("  NOT INDUCED:", n, sorted(map(sorted, E)), phi)
        if len(E) <= 6:
            adj_only_not_induced += sum(1 for phi in edge_maps(E, False)
                                        if not induced(E, phi, n))
    print(f"n={n}: {count} graphs, {with_tri} adjacency+triangle preserving edge maps, all induced;"
          f" edge maps preserving adjacency only and not induced (graphs with <= 6 edges):"
          f" {adj_only_not_induced}", flush=True)
print(f"counterexamples to the star lemma: {bad}")
