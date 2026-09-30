"""Export the order complex of Cl(Gamma) minus its top as maximal simplices (facets),
vertices numbered 0..N-1, for an independent homology computation in polymake/topaz."""
import json
from cl_homology import cluster_permutohedron, leq

CASES = {
    "C3": (3, [(1,2),(2,3),(1,3)]),
    "claw": (4, [(1,2),(1,3),(1,4)]),
    "C4": (4, [(1,2),(2,3),(3,4),(1,4)]),
    "C5": (5, [(1,2),(2,3),(3,4),(4,5),(1,5)]),
}
out = {}
for name, (n, E) in CASES.items():
    elems, rank = cluster_permutohedron(n, E)
    top = max(rank.values())
    P = [e for e in elems if rank[e] < top]
    idx = {e: i for i, e in enumerate(P)}
    up = {e: [f for f in P if rank[f] == rank[e] + 1 and leq(e, f)] for e in P}   # covers only (Cl is graded)
    facets = []
    def extend(chain):
        nxt = up[chain[-1]]
        if not nxt:                      # chain can't be extended upward from its top
            facets.append(sorted(idx[x] for x in chain)); return
        for f in nxt: extend(chain + [f])
    for e in P:
        if rank[e] == 0: extend([e])     # maximal chains start at rank 0 (Cl is graded)
    out[name] = facets
    print(name, "vertices", len(P), "facets", len(facets))
json.dump(out, open("facets.json", "w"))
