"""Track D / Question 1 on regular semisimple Hessenberg varieties, n <= 7.

S(Hess(M,h)) = Cl(Gamma_h) (thesis v2, Example 4.26), and H^odd = 0 always.
(a) group h by the isomorphism class of Gamma_h: Betti numbers must agree inside a class
    for Question 1 to survive in this family;
(b) group h by invariants of Cl(Gamma_h) and look for classes containing non-isomorphic
    graphs: those are the candidates for Cl(G1) = Cl(G2) with G1 != G2.

Invariants are computed on the lattice of flats (clusterings) C, using that in Cl_Gamma
  #elements over C          = n! / prod |V_i|!
  #lower covers of (C, A)   = sum over flats C' covered by C of prod|V_i|! / prod|V'_j|!
  #upper covers of (C, A)   = number of flats covering C
all independent of the assignment A. The invariant is, per rank, the multiset of
(lower, upper) cover counts with multiplicities. (This replaces a direct computation on
Cl, which was quadratic in its size and too slow at n = 6.)
"""
import sys
from math import factorial, prod
from itertools import permutations
from collections import defaultdict, Counter
sys.path.insert(0, "../counterexample"); sys.path.insert(0, "../cluster_permutohedra")
from sweep import hessenberg_functions, edges, poincare
from cl_homology import set_partitions, connected

def canon(n, E):
    best = None
    for p in permutations(range(1, n + 1)):
        f = tuple(sorted(tuple(sorted((p[a - 1], p[b - 1]))) for a, b in E))
        if best is None or f < best:
            best = f
    return best

def cl_invariant(n, E):
    flats = [frozenset(frozenset(b) for b in P) for P in set_partitions(range(1, n + 1))
             if all(connected(b, E) for b in P)]
    rk = {C: n - len(C) for C in flats}
    refines = lambda A, B: all(any(a <= b for b in B) for a in A)
    covers = {C: [D for D in flats if rk[D] == rk[C] - 1 and refines(D, C)] for C in flats}
    ups = Counter(D for C in flats for D in covers[C])
    sym = lambda C: prod(factorial(len(b)) for b in C)
    inv = defaultdict(Counter)
    for C in flats:
        lower = sum(sym(C) // sym(D) for D in covers[C])
        inv[rk[C]][(lower, ups[C])] += factorial(n) // sym(C)
    return tuple(tuple(sorted(inv[k].items())) for k in sorted(inv))

for n in (4, 5, 6, 7):
    hs = hessenberg_functions(n)
    by_graph, by_inv = defaultdict(list), defaultdict(list)
    for h in hs:
        E = edges(h); P = poincare(h); g = canon(n, E)
        by_graph[g].append((h, P))
        by_inv[cl_invariant(n, E)].append((h, P, g))
    bad_a = [v for v in by_graph.values() if len({P for _, P in v}) > 1]
    cand_b = [v for v in by_inv.values() if len({g for _, _, g in v}) > 1]
    print(f"n={n}: {len(hs)} Hessenberg functions, {len(by_graph)} graph classes, {len(by_inv)} Cl-invariant classes")
    print(f"   (a) graph classes with differing Betti numbers: {len(bad_a)}")
    for v in bad_a: print("       ", v)
    print(f"   (b) Cl-invariant classes containing non-isomorphic graphs: {len(cand_b)}")
    for v in cand_b:
        print(f"        Betti {'EQUAL' if len({P for _, P, _ in v}) == 1 else 'DIFFER'}:")
        for h, P, _ in v: print(f"           h={h} edges={edges(h)} P={P}")
    sys.stdout.flush()
