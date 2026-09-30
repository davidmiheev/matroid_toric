-- Plücker ideal of the complete flag variety Fl(C^n): kernel of p_S |-> minor of the
-- first |S| rows, columns S, of a generic n x n matrix. Written in gfan's input format.
flagIdeal = n -> (
    subs := flatten apply(toList(1..n-1), k -> subsets(toList(1..n), k));
    names := apply(subs, S -> concatenate("p", apply(S, toString)));
    P := QQ[apply(names, s -> getSymbol s)];
    A := QQ[x_(1,1)..x_(n,n)];
    X := transpose genericMatrix(A, x_(1,1), n, n);
    f := map(A, P, apply(subs, S -> det submatrix(X, toList(0..#S-1), apply(S, j -> j-1))));
    I := trim ker f;
    (P, I, names));
for n in {3, 4} do (
    (P, I, names) := flagIdeal n;
    << "n=" << n << ": " << #names << " variables, " << numgens I << " generators, dim " << dim I << endl;
    fn := "fl" | toString n | ".gfan";
    fn << "Q[" << demark(",", names) << "]" << endl
       << "{" << demark(",\n", apply(flatten entries gens I, g -> toExternalString g)) << "}" << endl << close;
);
