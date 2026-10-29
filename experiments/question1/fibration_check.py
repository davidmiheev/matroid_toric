"""Check the fibration identity used in the proof of Question 1 for partial Hessenberg varieties.

For a composition kbar = (k_1,...,k_s) of n and a Hessenberg function h on [s], let h~ be the
Hessenberg function on [n] with h~(i) = K_{h(a)} for i in part a, where K_b = k_1 + ... + k_b.
Then Hess(X, h~) -> Hess_kbar(X, h) is the restriction of Fl_n -> Fl_kbar, a bundle with
fibre prod_a Fl(k_a), and the Poincare polynomials satisfy

    P(h~) = P(kbar, h) * prod_a [k_a]_q!       (q = t^2).

Both sides are computed from the Bialynicki-Birula statistic (partial_hessenberg.poincare),
for every (kbar, h) with n <= N. Also checks that the graph of h~ is the inflated graph
Gamma_h(kbar) with every part made a clique.

Usage: python3 fibration_check.py N
"""
import sys
from itertools import accumulate
import partial_hessenberg as ph


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def qfact(k):
    p = [1]
    for m in range(1, k + 1):
        p = pmul(p, [1] * m)
    return p


def h_tilde(kbar, h):
    K = [0] + list(accumulate(kbar))
    return tuple(K[h[a]] for a in range(len(kbar)) for _ in range(kbar[a]))


def part_of(kbar):
    return [a for a in range(1, len(kbar) + 1) for _ in range(kbar[a - 1])]


N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
total = 0
for n in range(1, N + 1):
    cases = 0
    for kbar in ph.compositions(n):
        for h in ph.hessenberg_functions(len(kbar)):
            ht = h_tilde(kbar, h)
            lhs = list(ph.poincare(n, (1,) * n, ht))
            rhs = list(ph.poincare(n, kbar, h))
            for k in kbar:
                rhs = pmul(rhs, qfact(k))
            assert lhs == rhs, (n, kbar, h, lhs, rhs)
            # graph of h~ = inflated graph + cliques on parts
            part = part_of(kbar)
            Eh = ph.graph(h)
            want = {frozenset((i, j)) for i in range(1, n + 1) for j in range(i + 1, n + 1)
                    if part[i - 1] == part[j - 1] or frozenset((part[i - 1], part[j - 1])) in Eh}
            assert set(ph.graph(ht)) == want, (n, kbar, h)
            cases += 1
    total += cases
    print(f"n={n}: {cases} (kbar, h) cases, identity holds", flush=True)
print(f"all {total} cases with n <= {N}: P(h~) = P(kbar,h) * prod [k_a]_q!")
