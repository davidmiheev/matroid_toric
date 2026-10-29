"""Finite check for the Whitney exceptions in the partial-Hessenberg reconstruction argument.

A connected component of an inflated graph G = Gamma_h(kbar), with its partition P into parts,
is itself an inflated graph of a connected Hessenberg graph. From the face poset one can read,
for every set S of edges (= atoms above a fixed point), the rank of the join of S and the number
N(S) of fixed points below that join (a product of multinomial coefficients over the blocks).

Whitney's theorem makes an edge bijection preserving adjacency come from a vertex isomorphism,
except when a component has <= 4 vertices (K3, K_{1,3}, K_{1,3}+e, K4-e, K4). This script
covers those: for all connected (G, P) with at most 4 vertices it checks that any edge bijection
preserving rank and N on all edge sets comes from an isomorphism of graphs-with-partition.

Usage: python3 partial_small_components.py
"""
from itertools import combinations, permutations
from math import factorial
import partial_hessenberg as ph


def inflated(kbar, h):
    part = [a for a in range(1, len(kbar) + 1) for _ in range(kbar[a - 1])]
    n = len(part)
    Eh = ph.graph(h)
    E = [(i, j) for i, j in combinations(range(n), 2) if frozenset((part[i], part[j])) in Eh]
    return n, part, E


def is_connected(n, E):
    adj = {v: set() for v in range(n)}
    for a, b in E: adj[a].add(b); adj[b].add(a)
    seen, st = {0}, [0]
    while st:
        for w in adj[st.pop()]:
            if w not in seen: seen.add(w); st.append(w)
    return len(seen) == n


def blocks(n, edges):
    parent = list(range(n))
    def f(x):
        while parent[x] != x: x = parent[x]
        return x
    for a, b in edges: parent[f(a)] = f(b)
    out = {}
    for v in range(n): out.setdefault(f(v), []).append(v)
    return list(out.values())


def data(n, part, E):
    """(rank, N) of the join of every edge subset, indexed by bitmask over E."""
    D = []
    for mask in range(1 << len(E)):
        S = [E[i] for i in range(len(E)) if mask >> i & 1]
        bl = blocks(n, S)
        N = 1
        for B in bl:
            counts = {}
            for v in B: counts[part[v]] = counts.get(part[v], 0) + 1
            m = factorial(len(B))
            for c in counts.values(): m //= factorial(c)
            N *= m
        D.append((n - len(bl), N))
    return D


def partitioned_iso(c1, c2):
    (n1, p1, E1), (n2, p2, E2) = c1, c2
    if n1 != n2 or len(E1) != len(E2): return False
    S2 = {frozenset(e) for e in E2}
    for pi in permutations(range(n1)):
        if {frozenset((pi[a], pi[b])) for a, b in E1} != S2: continue
        if all((p1[u] == p1[v]) == (p2[pi[u]] == p2[pi[v]]) for u in range(n1) for v in range(n1)):
            return True
    return False


comps = []
for n in range(2, 5):
    for kbar in ph.compositions(n):
        if len(kbar) < 2: continue
        for h in ph.hessenberg_functions(len(kbar)):
            c = inflated(kbar, h)
            if is_connected(c[0], c[2]): comps.append(c)
classes = []
for c in comps:
    if not any(partitioned_iso(c, d) for d in classes): classes.append(c)
print(f"{len(comps)} connected inflated components with <= 4 vertices, "
      f"{len(classes)} up to isomorphism of graphs-with-parts")
bad = 0
for c1, c2 in combinations(classes, 2):
    if len(c1[2]) != len(c2[2]): continue
    D1, D2 = data(*c1), data(*c2)
    m = len(c1[2])
    for phi in permutations(range(m)):
        if all(D1[mask] == D2[sum(1 << phi[i] for i in range(m) if mask >> i & 1)]
               for mask in range(1 << m)):
            bad += 1
            print("  INDISTINGUISHABLE:", c1, c2)
            break
print(f"non-isomorphic pairs with matching (rank, N) data: {bad}")
