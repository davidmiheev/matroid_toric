use application "topaz";
use JSON::PP;
open my $fh, "<", "facets.json" or die; local $/; my $data = decode_json(<$fh>); close $fh;
for my $name (qw(C3 claw C4 C5)) {
    my $K = new SimplicialComplex(FACETS => $data->{$name});
    print "$name: f-vector ", $K->F_VECTOR, "  integral homology: ", $K->HOMOLOGY, "\n";
}
