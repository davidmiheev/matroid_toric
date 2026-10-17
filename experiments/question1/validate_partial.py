"""Validation of partial_hessenberg.py against facts known independently."""
import sys
from collections import Counter
from itertools import combinations
sys.path.insert(0, "../cluster_permutohedra"); sys.path.insert(0, "../counterexample")
import partial_hessenberg as ph
from cl_homology import cluster_permutohedron
import sweep

ok = True
def check(name, got, want):
    global ok
    good = got == want; ok &= good
    print(f"[{'PASS' if good else 'FAIL'}] {name}: got {got}" + ("" if good else f", want {want}"))

def rank_counts(n, kbar, h):
    c = Counter(n - len(f) for f in ph.faces(n, kbar, h)); return [c[r] for r in range(max(c) + 1)]

# 1. Gr(2,4) = kbar (2,2), h = (2,2): faces 6,12,11,1 (12 = edges of the octahedron J(4,2));
#    Poincare polynomial of Gr(2,4) is 1 + q^2 + 2q^4 + q^6 + q^8.
check("Gr(2,4) faces by rank", rank_counts(4, (2, 2), (2, 2)), [6, 12, 11, 1])
check("Gr(2,4) Betti", ph.poincare(4, (2, 2), (2, 2)), (1, 1, 2, 1, 1))
# 2. Gr(2,5): Betti 1,1,2,2,2,1,1 (Gaussian binomial [5 choose 2]_q).
check("Gr(2,5) Betti", ph.poincare(5, (2, 3), (2, 2)), (1, 1, 2, 2, 2, 1, 1))
# 3. full-flag case kbar = (1,...,1) must reproduce Cl(Gamma_h) and the DPS Betti numbers.
for n in (3, 4, 5):
    for h in sweep.hessenberg_functions(n):
        E = sweep.edges(h)
        el, rk = ph_cl = cluster_permutohedron(n, E)
        cl = Counter(rk.values()); cl = [cl[r] for r in range(max(cl) + 1)]
        mine = rank_counts(n, (1,) * n, h)
        if mine != cl or ph.poincare(n, (1,) * n, h) != sweep.poincare(h):
            check(f"full case n={n} h={h}", (mine, ph.poincare(n, (1,)*n, h)), (cl, sweep.poincare(h)))
print("[info] full-flag case n=3,4,5: rank counts vs Cl(Gamma_h) and Betti vs DPS checked for all h")
# 4. local posets: faces above each fixed point must be Flats(Gamma_h(kbar)) of the inflated graph.
def inflated_flats_by_rank(kbar, h):
    E = ph.graph(h); verts = [(a, i) for a, k in enumerate(kbar, 1) for i in range(k)]
    edges = [(u, v) for u, v in combinations(verts, 2) if frozenset((u[0], v[0])) in E]
    def conn(B):
        B = set(B); s = next(iter(B)); seen = {s}; st = [s]
        while st:
            x = st.pop()
            for u, v in edges:
                for p, q in ((u, v), (v, u)):
                    if p == x and q in B and q not in seen: seen.add(q); st.append(q)
        return seen == B
    c = Counter(len(verts) - len(P) for P in ph.set_partitions(verts) if all(conn(b) for b in P))
    return [c[r] for r in range(max(c) + 1)]
for n, kbar, h in [(4, (2, 2), (2, 2)), (5, (2, 3), (2, 2)), (5, (1, 2, 2), (2, 3, 3)), (5, (2, 1, 2), (3, 3, 3)), (6, (2, 2, 2), (2, 3, 3))]:
    F = ph.faces(n, kbar, h); want = inflated_flats_by_rank(kbar, h)
    bad = 0
    for J in ph.fixed_points(n, kbar):
        x = frozenset((frozenset([v]), tuple(1 if v in J[a] else 0 for a in range(len(kbar)))) for v in range(1, n + 1))
        up = Counter(n - len(f) for f in F if ph.leq(x, f))
        if [up[r] for r in range(max(up) + 1)] != want: bad += 1
    check(f"local posets = Flats(inflated graph), n={n} kbar={kbar} h={h}", bad, 0)
# 5. cover counts from splitting/merging agree with brute force on the order relation.
for n, kbar, h in [(4, (2, 2), (2, 2)), (5, (1, 2, 2), (2, 3, 3))]:
    E = ph.graph(h); F = ph.faces(n, kbar, h); rk = {f: n - len(f) for f in F}
    bad = sum(1 for f in F
              if ph.lower_covers(f, E) != sum(1 for g in F if rk[g] == rk[f] - 1 and ph.leq(g, f))
              or ph.upper_covers(f, E) != sum(1 for g in F if rk[g] == rk[f] + 1 and ph.leq(f, g)))
    check(f"cover counts vs brute force, n={n} kbar={kbar}", bad, 0)
print("ALL PASS" if ok else "SOME CHECKS FAILED")
