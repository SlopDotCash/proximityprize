# G87V threshold and rank reporting correction

The displayed fence inequality is `s*log(p) <= (n/2)*log(6)`, but the printed threshold divided by `2*log(p)`. The extra factor two is removed. The reporting now distinguishes full modular rank, which certifies full rational rank, from deficient modular ranks, which alone supply no rational upper bound. Coverage is computed for the full census, not a selected maximal-rank subfamily.

The empty-census path now uses the same rank-tuple shape as nonempty cases, avoiding mixed integer/tuple sorting. Its common coverage is all roots by vacuous truth, consistent with the helper's semantics. A controlled empty-census execution of all six configured cells passes and reports coverage 16 or 32 as appropriate. Python compilation and whitespace checks pass.

The full enumerations and archived outputs have not been replayed here; this correction does not certify their ranks or complete their retention reviews. Coverage remains 58/92.
