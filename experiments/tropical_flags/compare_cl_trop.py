"""Track C: compare the face poset S(Fl(C^n)) = Cl(K_n) with the face poset of the
tropical flag variety trop Fl_n (= flag Dressian for n <= 5, Brandt-Eur-Zhang), as
computed by gfan (trop_fl{n}.out, from fl{n}_letters.gfan)."""
import re, sys
sys.path.insert(0, "../cluster_permutohedra")
from cl_homology import cluster_permutohedron
from itertools import combinations

def gfan_fvector(path):
    t = open(path).read()
    f = list(map(int, re.search(r"F_VECTOR\n([\d ]+)", t).group(1).split()))
    lin = int(re.search(r"LINEALITY_DIM\n(\d+)", t).group(1))
    dim = int(re.search(r"\nDIM\n(\d+)", t).group(1))
    return f, lin, dim

for n in (3, 4):
    edges = list(combinations(range(1, n + 1), 2))
    elems, rank = cluster_permutohedron(n, edges)
    cl = [sum(1 for e in elems if rank[e] == k) for k in range(max(rank.values()) + 1)]
    fan, lin, dim = gfan_fvector(f"trop_fl{n}.out")
    print(f"n={n}:  Cl(K_{n}) elements by rank {cl}  (rank {len(cl)-1} = torus rank n-1)")
    print(f"      trop Fl_{n}: dim {dim}, lineality {lin}; cones by dim mod lineality {fan}"
          f"  (length {len(fan)-1} = complexity (n-1)(n-2)/2 = {(n-1)*(n-2)//2})")
    if len(cl) != len(fan):
        print("      -> different lengths: no rank-preserving map in either direction or orientation")
        continue
    op = cl[::-1]
    for name, P in (("Cl", cl), ("Cl^op", op)):
        inj = all(p <= q for p, q in zip(P, fan))
        surj = all(p >= q for p, q in zip(P, fan))
        print(f"      {name:5s} -> fan: rank-preserving injection possible by counts: {inj}; "
              f"surjection onto whole fan possible by counts: {surj}")
