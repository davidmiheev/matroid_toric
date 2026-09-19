-- Independent recomputation of H*_T(Hess(M,h)) from the GKM presentation.
-- Uses no Shareshian-Wachs input: builds the ring of graph functions
--    ker ( +_{w in S_n} R  ->  +_{edges (p,q)} R/(alpha_pq) )
-- and reads the Betti numbers off its Hilbert series.
--
-- Fixed points: w in S_n.  Tangent weights at w: t_{w(j)} - t_{w(i)}, j < i <= h(j).
-- The edge in that direction joins w to w*(j i) (swap of positions j,i).
-- Variables have degree 1, so the Hilbert series variable T corresponds to
-- cohomological degree 2: H*_T is free of rank n! over R and
--    Hilb = ( sum_k beta_{2k} T^k ) / (1-T)^n.

gkmBetti = (n, h) -> (
    R := QQ[t_1..t_n];
    perms := permutations n;
    N := #perms;
    idx := new HashTable from apply(N, a -> perms#a => a);
    rows := {};
    wts  := {};
    for a from 0 to N-1 do (
        w := perms#a;
        for j from 1 to n do (
            for i from j+1 to h#(j-1) do (
                v := new MutableList from w;
                tmp := v#(j-1); v#(j-1) = v#(i-1); v#(i-1) = tmp;
                b := idx#(toList v);
                if a < b then (
                    rows = append(rows, (a, b));
                    wts  = append(wts, R_(w#(j-1)) - R_(w#(i-1)));
                );
            );
        );
    );
    E := #rows;
    << "  fixed points = " << N << ", GKM edges = " << E << endl;
    Tgt := directSum apply(wts, al -> coker matrix {{al}});
    M := matrix apply(E, e -> (
            (a, b) := rows#e;
            apply(N, c -> if c == a then 1_R else if c == b then -1_R else 0_R)));
    phi := map(Tgt, R^N, M);
    K := kernel phi;
    hs := reduceHilbert hilbertSeries K;
    num := numerator hs;
    << "  Hilbert numerator = " << num << endl;
    << "  denominator       = " << denominator hs << endl;
    num);

-- extract the coefficient list of the numerator in T
coeffList = (num, top) -> (
    S := ring num;
    T := S_0;
    apply(top + 1, k -> coefficient(T^k, num)));

doCase = (label, n, h) -> (
    << "=== " << label << ": n = " << n << ", h = " << toString h << endl;
    num := gkmBetti(n, h);
    << "  Betti (coeffs of T^k, T ~ q^2) = "
       << toString coeffList(num, first degree num) << endl << endl;);

-- 1. pipeline validation: full flag varieties must give [n]_q!
doCase("Fl(C^3)", 3, {3,3,3});
doCase("Fl(C^4)", 4, {4,4,4,4});
-- 2. the minimal (disconnected) witness pair in Fl(C^4)
doCase("witness X1", 4, {2,3,3,4});
doCase("witness X2", 4, {2,2,4,4});
