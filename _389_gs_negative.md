## Negative result (logged): Guruswami–Sudan over the cyclotomic ideal adds ZERO beyond-Johnson freedom

Tested the one interpolation lever not yet examined for the floor (`PrizeFloorStatement` = worst-case
list ≤ B above Johnson): does the cyclic structure `X^n−1` of the smooth domain give the GS
bivariate interpolation extra freedom?

**The genuine fact.** For RS[μ_n,k], every interpolation point `(ζ^a, w_a)` satisfies `(ζ^a)^n−1=0`,
so **`X^n−1 ∈ ⟨interpolation ideal⟩`** — the GS interpolation lives in the cyclic quotient
`F[X,Y]/(X^n−1)`.

**Why it's vacuous (negative).** The quotient only identifies `X`-degrees `≥ n`. But GS for an `[n,k]`
code never uses weighted `X`-degree `≥ n` (agreement `≤ n` caps it). So the cyclotomic ideal adds no
freedom in the operative regime; `deg_Y Q` is unchanged and the bound still stops at Johnson
`t=√(kn)`. Same shape as the HOMDS finding (19:49): the cyclic symmetry annihilates the Schur
determinants yet is *harmless to the code* — the smooth structure is **invisible to every
linear-algebraic interpolation certificate**.

**Structural conclusion.** This is the unifying reason ALL methods stall identically: GS-ideal (this),
HOMDS/Schur (19:49), BGK character sums (the "irreducibly o(n)" trap — bounds the generic stratum, not
the structured worst case), Kong–Tamo, finite-field LO, deep-holes, dyadic-tower (lower bound only,
tightness refuted). Beyond-Johnson for smooth RS is NOT certifiable by any linear/analytic object; the
floor is the **combinatorial optimality** of the antipodal subset-sum fibre (no word beats it), i.e.
exactly BCHKS25 Conj 1.12. A genuine solution must be a combinatorial extremality argument on the
fibre, not a character-sum or interpolation bound. Logged so this lever isn't re-attempted.
