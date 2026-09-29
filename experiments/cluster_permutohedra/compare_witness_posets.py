"""Global face posets of the Track A witness pair (thesis v2, Section 4.5, last remark).

By Ayzenberg-Buchstaber (twins), S(Hess(M,h)) is the cluster-permutohedron Cl(Gamma_h).
If the two posets had equal rank counts they might be isomorphic, which would bear on
Question 1; they do not, so they are not isomorphic.
"""
from cl_homology import cluster_permutohedron

PAIR = {
    "h1 = (2,3,5,5,5)": (5, [(1, 2), (2, 3), (3, 4), (3, 5), (4, 5)]),
    "h2 = (2,4,4,5,5)": (5, [(1, 2), (2, 3), (2, 4), (3, 4), (4, 5)]),
}
counts = {}
for name, (n, edges) in PAIR.items():
    elems, rank = cluster_permutohedron(n, edges)
    counts[name] = [sum(1 for e in elems if rank[e] == k) for k in range(max(rank.values()) + 1)]
    print(f"Cl(Gamma_{name}): elements by rank = {counts[name]}")
a, b = counts.values()
print("rank counts equal:", a == b, "=> face posets", "may coincide" if a == b else "are NOT isomorphic")
