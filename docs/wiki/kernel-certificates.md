# Large numeric kernel proofs

Use ordinary kernel-checked certificates for finite arithmetic and explicit prime witnesses.
Mathlib's `norm_num` primality extension can produce very deep proof terms above 25 bits.
Increasing a global recursion limit can hide the shape of the problem without making the
certificate shallower.

For a closed natural-number primality goal, use:

```lean
import ArkLib.ToMathlib.NatPrimeCheckpoint

example : Nat.Prime 4294968833 := by
  prime_checkpoint
```

The tactic uses Mathlib's `MinFacHelper` steps and stores a proved checkpoint every 128 steps.
The kernel checks every auxiliary theorem, including its divisibility and remainder evidence.
Meta-level factor search supplies candidate certificates; it does not supply an axiom or invoke
`native_decide`. Composite candidates are rejected. Arithmetic expressions supported by
`norm_num`, such as `2 ^ 8 + 1`, are accepted as well as numeral literals.

When one theorem contains many large prime witnesses, prove their primality as separate private
theorems and reuse those proofs in the finite-set argument. This keeps each declaration's
elaboration budget bounded. The numerical witnesses and mathematical conclusion stay explicit.
For modular congruences, `norm_num [Nat.ModEq]` produces arithmetic evidence without a long
recursive `decide` reduction.

For closed arithmetic comparisons, `decide +kernel` can avoid the elaborator's large-numeral
simplification path while checking the full decision in the kernel. Use it only for decidable
goals with explicit numerical data; unfold a named predicate if instance search cannot expose
its decision procedure. The production moment and subset-count diagnostics use this mode
without changing their numbers or conclusions. Large primality searches still need the
checkpoint tactic above.

After the imports are built, check the file with `scripts/pg-iterate.sh <file>` and print the
axioms of the public result. Follow the shared build rules in [quickstart.md](quickstart.md).

Large finite index types have a separate issue: reducing a polynomial coefficient can expand
an entire specialized finite sum. Prove coefficient, evaluation, and degree facts with a
symbolic length first. If specialization still forces that reduction, package the explicit
construction into a proved existence specification, including equality to the construction,
and select its witness with `Classical.choose`. The specification then supplies the public
facts while the kernel keeps the large finite sum behind the choice boundary. This uses only
the standard choice principle and preserves a proved equality to the original polynomial;
see the difference-polynomial construction in
[`ScaleBracketFull.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean).
