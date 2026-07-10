# Issue #466 G86: occurrence-correct decoder extraction

Date: 2026-07-10

G86 closes the repeated-value/position-matching part of the factorial-corrected padding decoder.
Given ordered words `core`, `padding`, and `word` with

```text
(core.toList ++ padding.toList).Perm word.toList,
```

`List.Perm.idxBij` matches individual occurrences, including repeated values. Restricting this
bijection to the initial core block gives `e : Fin s ↪ Fin r`. Lean proves

```text
coreAt e word = core
assemble e core (paddingAt e word) = word.
```

The second equation uses the complementary padding order read from the endpoint itself, avoiding
the need to match core and padding positions independently. A multiset-facing corollary accepts
exactly the reconstruction equation produced by G83M.

G86 also proves the function-level relative-order theorem

```text
multiset(left) = multiset(right)
  → ∃ σ : Perm (Fin t), right = left ∘ σ,
```

so one relative permutation suffices even with repeated padding values. This is precisely the
coordinate counted by G81C.

## Honest residual

The remaining assembly theorem must package G83M's canonical `leftCore`, `rightCore`, and
`commonPart` into fixed-depth ordered representatives, invoke G86 twice, and package the resulting
data into the corrected `PaddingCode`. The occurrence matching itself is no longer an assumption.

Production delta-star remains open; primitive depths four and above retain the analytic residual.

## Verification

`scripts/pg-iterate.sh` passes. The declarations use only `propext`, `Classical.choice`, and
`Quot.sound`.
