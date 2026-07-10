# Issue #466 G84S: core/padding slot partition

Date: 2026-07-10

G84S supplies the ordered-position substrate for the factorial-corrected padding decoder.  Given an
embedding `e : Fin s ↪ Fin r` with `s ≤ r`, it defines:

- `coreRange e`, the occupied endpoint slots;
- `padSlots e`, the increasing enumeration of the complementary `r-s` slots;
- `slotEquiv e : Fin s ⊕ Fin (r-s) ≃ Fin r`.

Lean proves the core and padding maps are cross-disjoint, jointly injective, and—by exact finite
cardinality—bijective.  The explicit `s ≤ r` hypothesis prevents truncated natural subtraction from
silently accepting malformed sector depths.

This result is axiom-clean (`[propext]`) and composes directly with:

- G83M for canonical core/common-padding profiles;
- G81D for the relative ordering of equal padding multisets;
- G81C for the corrected code cardinality;
- G81/G82 for full-Wick absorption.

The next theorem can now define

```text
assemble e core pad = Sum.elim core pad ∘ (slotEquiv e).symm
```

and prove restriction and multiset laws.  The final decoder-surjectivity proof then extracts the
two embeddings from G83M's reconstructed endpoint profiles and uses G81D for the relative padding
permutation.  Production delta-star remains open.
