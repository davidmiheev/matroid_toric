"""Betti numbers of the order complex of Cl(G) minus its top element, for the
cluster-permutohedra of Примеры 19-20 (thesis v1) = Examples in the English v2.

Cl(G) (Ayzenberg-Buchstaber, arXiv:2203.14133, Def. 2.14): pairs (C, A) where C is
a clustering of V(G) (blocks induce connected subgraphs; = flats of the graphic
matroid) and A is an assignment, i.e. a class of bijections p: V -> [n] modulo
permutations inside clusters.  We encode A by the map  cluster -> p(cluster).
(C',A') <= (C,A) iff every cluster of C' lies in a cluster of C and the label sets
nest accordingly.

Betti numbers are computed over F_p for two large primes (they must agree) and
checked against the Euler characteristic, which is exact.
"""
from itertools import permutations, combinations
import sys

def connected(vs, edges):
    vs = set(vs)
    if len(vs) <= 1:
        return True
    start = next(iter(vs)); seen = {start}; stack = [start]
    while stack:
        a = stack.pop()
        for (x, y) in edges:
            for (u, v) in ((x, y), (y, x)):
                if u == a and v in vs and v not in seen:
                    seen.add(v); stack.append(v)
    return seen == vs

def set_partitions(s):
    s = list(s)
    if not s:
        yield []
        return
    first, rest = s[0], s[1:]
    for p in set_partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [p[i] | {first}] + p[i+1:]
        yield p + [{first}]

def cluster_permutohedron(n, edges):
    V = range(1, n + 1)
    clusterings = [tuple(frozenset(b) for b in p) for p in set_partitions(V)
                   if all(connected(b, edges) for b in p)]
    elems = set()
    for C in clusterings:
        for p in permutations(range(1, n + 1)):
            elems.add(frozenset((b, frozenset(p[v - 1] for v in b)) for b in C))
    rank = {e: n - len(e) for e in elems}
    return list(elems), rank

def leq(a, b):
    return all(any(c <= d and s <= t for (d, t) in b) for (c, s) in a)

def order_complex(elems, rank, top_rank):
    P = [e for e in elems if rank[e] < top_rank]           # drop the top element 1^
    up = {e: [f for f in P if rank[f] > rank[e] and leq(e, f)] for e in P}
    simplices = []
    def extend(chain):
        simplices.append(tuple(chain))
        for f in up[chain[-1]]:
            extend(chain + [f])
    for e in P:
        extend([e])
    return simplices

def betti(simplices, p):
    by_dim = {}
    for s in simplices:
        by_dim.setdefault(len(s) - 1, []).append(s)
    idx = {d: {s: i for i, s in enumerate(L)} for d, L in by_dim.items()}
    top = max(by_dim)
    ranks = {}
    for d in range(1, top + 1):                               # rank of boundary d -> d-1
        rows = []
        for s in by_dim[d]:
            row = {}
            for i in range(len(s)):
                face = s[:i] + s[i+1:]
                row[idx[d-1][face]] = (-1) ** i % p
            rows.append(row)
        pivots = {}
        r = 0
        for row in rows:
            row = dict(row)
            while row:
                c = min(row)
                if c in pivots:
                    prow = pivots[c]
                    f = row[c] * pow(prow[c], p - 2, p) % p
                    for k, v in prow.items():
                        nv = (row.get(k, 0) - f * v) % p
                        if nv: row[k] = nv
                        else: row.pop(k, None)
                else:
                    pivots[c] = row; r += 1
                    break
        ranks[d] = r
    f = [len(by_dim[d]) for d in range(top + 1)]
    b = [f[d] - ranks.get(d, 0) - ranks.get(d + 1, 0) for d in range(top + 1)]
    return f, b

if __name__ == "__main__":
    CASES = {
        "C_3 (cycle = K_3)": (3, [(1,2),(2,3),(1,3)]),
        "claw S_3 = K_{1,3}": (4, [(1,2),(1,3),(1,4)]),
        "C_4 (cycle)": (4, [(1,2),(2,3),(3,4),(1,4)]),
        "C_5 (cycle)": (5, [(1,2),(2,3),(3,4),(4,5),(1,5)]),
    }
    for name, (n, edges) in CASES.items():
        elems, rank = cluster_permutohedron(n, edges)
        top_rank = max(rank.values())
        simp = order_complex(elems, rank, top_rank)
        f, b1 = betti(simp, 1_000_000_007)
        _, b2 = betti(simp, 998_244_353)
        chi_f = sum((-1) ** i * x for i, x in enumerate(f))
        chi_b = sum((-1) ** i * x for i, x in enumerate(b1))
        counts = [sum(1 for e in elems if rank[e] == k) for k in range(top_rank + 1)]
        print(f"{name}: n={n}, |Cl| by rank = {counts}")
        print(f"   order complex of Cl minus top: f-vector {f}")
        print(f"   Betti (mod p1) {b1}   (mod p2) {b2}   agree={b1 == b2}   chi: {chi_f} == {chi_b}")
        sys.stdout.flush()
