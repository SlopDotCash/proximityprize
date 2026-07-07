# #444 — Concrete shallow rungs of the reduction spine (2026-06-16)

**Scope.** Honest synthesis of a 4-rung propose→verify sweep on the shallow end of the
#444 reduction spine: the char-p validity of the DC-subtracted Wick bound
`A_r = E_r − n^{2r}/q ≤ (2r−1)‼·n^r` at the rungs `r ≤ rMax ≈ 2β ≈ 8` (clean regime),
where `E_r = zeroSumCount(μ_n, 2r)` is the order-`r` additive energy of the proper
order-`n` subgroup `μ_n ⊂ F_p*` (`n = 2^μ`, prize `p ≈ n·2^128`, `m = 2^128`,
`r_opt = log m ≈ 128`). The prize wall is char-p validity at **deep** `r ≈ 89–128`;
this sweep touches only `r ≤ 3`. Honesty contract enforced: "proven" = axiom-clean Lean
(`axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`, `scripts/pg-iterate.sh`);
"refuted" = machine-checked countermodel. No char-p clean-regime closure is claimed by any
of the four files.

---

## (a) Per-rung verdicts and exact theorem names

| Rung | Final verdict | File (gitignored scratch, `_`-prefix) |
|---|---|---|
| E₃ closed form | **proven mod 2 named char-0 inputs** | `Frontier/_E3ClosedForm2Power.lean` |
| Wmax(6) | **proven mod 1 named (incorrect) hyp** — NOT axiom-clean discharge | `Frontier/_Wmax6Bound.lean` |
| dyadic recursion D* | **REFUTED** (countermodel) | `Frontier/_DyadicRecursionDstar.lean` |
| c_r shallow (r=1,2) | **DISCHARGED axiom-clean** | `Frontier/_CrMonotonicityShallow.lean` |

### E₃ closed form — `_E3ClosedForm2Power.lean`
Axiom-clean theorems (`decide` over real Fin-6 → ZMod n tuple enumeration, maxRecDepth/
maxHeartbeats raised for n=4): `matchableCount_two` (=20), `matchableCount_four` (=400),
`e3Cubic_two`, `e3Cubic_four`, `matchableCount_two_eq_cubic`, `matchableCount_four_eq_cubic`,
`E3_closed_form_of_inputs` (the non-vacuous bridge: `MatchableCountClosedForm ∧
Z = matchableCount n ⟹ (Z:ℤ) = 15n³−45n²+40n`, proof `rw [hLL]; exact hcomb n hn`
consuming BOTH inputs), `E3_closed_form_two`, `E3_closed_form_four` (bridge fires at n=2,4
modulo ONLY the Lam–Leung input).
**Status: genuine reduction, not a closure.** Reduces to two NAMED OPEN inputs:
(1) `MatchableCountClosedForm` — a finite, field-independent combinatorial identity over even n,
base cases n=2,4 landed axiom-clean, tower n=2..32 machine-checked; the general case is a
Lean-formalization-effort gap (`decide` overflows the kernel at n≥8), **not** the deep wall;
(2) `LamLeungAntipodalMatchable` — the standing char-0 Lam–Leung antipodal-matchability
transport, Mathlib-absent, named only for 2-power n. Probes verified
`zeroSumCount(μ_n,6) = 15n³−45n²+40n` EXACTLY for n=8 (5120), 16 (50560), 32 (446720) and
**FAILS for 3|n** (n=12: 23160≠19920; n=24: 200400≠182400, inflates) — so this is correctly
**2-power-restricted**, never general n, exactly as the E₃ hazard warns.

### Wmax(6) — `_Wmax6Bound.lean`  ⚠️ DOES NOT discharge the r=3 resultant rung
Eight axiom-clean `decide` theorems prove a correct combinatorial fact about the object the
file defines: `wmax6_eq`, `genuine_content_le_26`, `content_table`
(spectrum `[36,26,20,18,18,14,12,12,10,8,6]`), `only_singleton_exceeds_26`, `wmax6_attained`,
`two_wmax6` (=52), `threshold_clears_at_n16` (52⁴ < 2²⁴). The constant
`Wmax(6) = max Σmᵢ² over ≥2-part partitions of 6 = 26`, attained uniquely at `[5,1]`.
**Verdict downgraded `discharged → proven-mod-named-hyp`: the object is mis-identified
relative to its in-tree consumer.** The actual r=3 resultant substrate is
`KKH26SumsOfRootsOfUnity.lean`: the collision polynomial `sumPoly U₁ T₁ − sumPoly U₂ T₂`
has coefficients in {−1,0,+1} (`l2SqOn_sumPoly`), content
`l2SqOn_collisionPoly_le_four_r ≤ 4r = 12` at r=3, and the resultant runs off the ℓ¹-norm
`natAbs_resultant_cyclotomic_le` with `‖R‖₁ ≤ 2r = 6`. The `[5,1]` pattern
(single exponent of multiplicity 5) is **unrealizable** in this ±1-coefficient mechanism —
collisions of two ±1 sumPolys cap single-exponent multiplicity at 2, never 5. The correct
in-tree r=3 constant is therefore **12** (content) / **6** (ℓ¹), matching the brief's anchor
`SixTermResultantImproved (r=3, 12^{φ(n)})` — **not 52**. The rung's threshold `p > 52^{n/4}`
overstates the constant ~4× (but is harmless: both `12^{n/4}` and `52^{n/4}` clear ≪ prize
prime, so the QUALITATIVE "shallow r=3 clears above threshold" survives). The energy/Wick
route (sibling `_CrMonotonicityShallow.lean`) and the resultant-content route are also distinct
objects and were conflated.

### dyadic recursion D* — `_DyadicRecursionDstar.lean`  REFUTED
Five axiom-clean theorems: `symmetric_dyadic_halving` (re-export of the proven exact halving
on the symmetric stratum from `SymmetricTowerBracket`), `bindingDeepCount_values`,
`bindingDeepCount_strictMono_at`, `dyadic_recursion_REFUTED`
(`bindingDeepCount 32 ≠ bindingDeepCount 16`), `dyadic_recursion_growth_ge`
(`8·D*16 < D*32`). The binding far line `(x^{n/2}, x^{n/2−1})` at the r=3 deep band gives
`#bad = n·C(n/4,2)+1 = 9, 97, 897, 7681` (digit-for-digit the proven CONJ.md closed form);
a value-preserving recursion `D*_{2n}(m) = D*_n(m−1)` would force
`bindingDeepCount(2n) = bindingDeepCount(n)`, FALSE already at n=16 (897 ≠ 97, ratio 9.25,
quadratic-ish growth). The exact `n→2n` halving holds ONLY on the symmetric/even sub-family,
which is **empty at the window radii** and carries none of the binding mass; the fiber
identity `agreement = 2|B| + s(S)` (`_S2NonSymTower`) is the mechanism — the singleton defect
`s(S)` of the binding (odd) lines breaks the factor-2 weighting. This resolves only the
far-line window-LOCATION proxy; the prize floor is untouched.

### c_r shallow (r=1,2) — `_CrMonotonicityShallow.lean`  DISCHARGED axiom-clean
Axiom-clean theorems: `cStep_one_lt` (c₁<1), `cStep_two_lt` (c₂<1),
`shallow_rungs_cr_lt_one` (r=1,2 cross-step + r=1,2,3 Wick bound), `recursion_holds`,
`aRatio_one/two/three`, `cStep_one/two`. Closed forms (verified n=2..2048):
`a₁=1, a₂=(n−1)/n, a₃=1−3/n+8/(3n²), c₁=1−3/(2n), c₂=1−(21n−20)/(6n²)`. Load-bearing
(tamper test breaks them), imports nothing, bakes E₂,E₃ in as def literals.
**Two honest framing corrections (neither breaks the rung):** (1) the cited anchor
`GaussianEnergyThreeRepThree` for E₃ **does not exist as a declaration** anywhere in the tree
(verified: only a docstring string-mention at `_CrMonotonicityShallow.lean:45,74`); the real
E₃ artifact is the CONDITIONAL `E3_closed_form_of_inputs`, so "in-tree anchor gives E₃"
overstates the unconditional status (E₂=3n²−3n IS genuinely in-tree via
`additiveEnergy_eq_of_sidonModNeg`, verified at `AdditiveEnergySidonModNeg.lean:113`).
(2) `recursion_holds` is an algebraic identity TRUE BY CONSTRUCTION (cStep is defined by
solving the recursion for a_{r+1}); it certifies the cross-step SHAPE, it does not
independently derive the orchestrator. The named orchestrator decls `M3CrossStepBound`,
`CrossStepRungOne`, `CrossStepCeilingInsufficient` likewise **do not exist** as declarations
in the tree.

---

## (b) K_eff(n) extrapolation verdict — SATURATE, not grow

**Verdict: K_eff(n) saturates at 1 from below in char-0; never crosses 1.** The earlier
apparent monotone climb `0.55→0.62→0.66` was a brute-force **artifact** of `n^r ≫ p`
wraparound at small (β≈1.1–2.1) primes — irrelevant to the prize (β≈128). The p-free
char-0 anchor is decisive: at fixed shallow r, `K_eff(n)` grows toward 1 strictly FROM BELOW
as n:4→8→16→32 (r=2: 0.866→0.935→0.968→0.984; gap `1−a₂ = 1/n` exactly), and `a_r ≤ 1` is
the Lam–Leung Wick theorem. So `a_r → 1⁻` as `n → ∞` but **never exceeds 1**.

**What this means for the prize floor.** The "grow past 1" floor danger — the inflation that
would FALSIFY the prize bound — is **invisible in char-0**. It can only ever be a **char-p
DC-defect at deep r** (`A_r = E_r − n^{2r}/q`: the subtracted `n^{2r}/q` term and char-p
sparse-sum coincidences are what the char-0 calculation cannot see). This is consistent with
and **mildly supportive of** the prize floor being TRUE: every char-0 signal saturates exactly
at the Wick value with the right one-sided sign, the only mechanism for violation is the
mod-q defect, and that defect is one-sided (energy excess `E_r − E_r^{c0} ≥ 0` always — known
from the broader programme). But it is **not evidence of closure**: char-0 saturation is
exactly what you'd see whether or not the deep char-p rungs hold, so this rung relocates the
entire remaining risk onto the deep mod-q defect without reducing it.

---

## (c) How much more of the M3CrossStepBound spine is now proven

The brief states r=0,1 of `M3CrossStepBound` were already discharged (via `CrossStepRungOne`,
from r≤2 energy ceilings). **Caveat on substrate:** in THIS checkout, `M3CrossStepBound`,
`CrossStepRungOne`, and `CrossStepCeilingInsufficient` do **not** exist as named declarations
(verified by grep over the whole cone — only string-mentions in scratch docstrings). So the
"r=0,1 already proven" baseline lives in a checkout/branch not present here, and the rungs
below are proven against **reconstructed local def literals**, not wired to a live orchestrator.

- **r=2 rung: advanced to proven-mod-2-named-char-0-inputs.** `_CrMonotonicityShallow.lean`
  proves `c₂ < 1` axiom-clean over baked-in E₂,E₃ literals. The standalone arithmetic is
  axiom-clean, but the E₃ literal it consumes is unconditionally established in-tree ONLY at
  n=2,4 (`_E3ClosedForm2Power.lean`); for general 2-power n it rests on `MatchableCountClosedForm`
  + `LamLeungAntipodalMatchable`. So r=2 is **discharged as an arithmetic rung but inherits the
  two named char-0 E₃ inputs** — net new ground: the r=2 cross-step shape and `c₂<1` bound,
  reduced to the same char-0 Lam–Leung input the programme already names.
- **r=3 rung: NOT discharged.** The `_Wmax6Bound.lean` attempt targets the wrong combinatorial
  object (Σmᵢ²=26 vs the in-tree ±1-coefficient resultant content `≤ 4r = 12`); the Wick-side
  r=3 bound appears in `shallow_rungs_cr_lt_one` but only as the char-0 `a₃ ≤ 1` inequality,
  not a char-p discharge of the r=3 resultant rung. The qualitative "r=3 clears above
  threshold" survives with the corrected constant 12, but axiom-clean discharge of r=3 does
  **not** hold.

**Net:** the spine advances from r=0,1 to a **conditional r=2** (arithmetic axiom-clean,
modulo the two named char-0 E₃ inputs). r=3 remains open; its in-tree constant is corrected
to 12 (content)/6 (ℓ¹).

---

## (d) What stays at the deep-r wall (r ≈ 89–128)

Everything that matters for the prize. The four rungs collectively cover only `r ≤ 3` (clean
regime `r ≤ rMax ≈ 2β ≈ 8`). Untouched:

1. **char-p validity of `A_r ≤ (2r−1)‼·n^r` at deep `r ≈ log m ≈ 89–128`** — the BGK / deep-
   moment / mod-q DC-defect wall. Char-0 (Lam–Leung) gives `a_r ≤ 1` for all r, but the
   subtracted `n^{2r}/q` defect and char-p sparse-sum coincidences are invisible to every char-0
   rung above. K_eff saturation (b) localizes the ENTIRE residual risk here without reducing it.
2. **General-n `MatchableCountClosedForm`** (E₃) — finite & field-independent, but a Lean
   `decide`-overflow gap above n=4; only a formalization-effort gap, not the deep wall.
3. **`LamLeungAntipodalMatchable`** — the standing Mathlib-absent char-0 Lam–Leung transport,
   FALSE for 3|n, correctly named only for 2-power n.
4. **Wiring** — `M3CrossStepBound` / `CrossStepRungOne` / `CrossStepCeilingInsufficient` /
   `GaussianEnergyThreeRepThree` / `SixTermResultantImproved` are absent from this checkout, so
   the shallow rungs are not connected to a live orchestrator here.

**No fabrication.** Three of four rungs land real axiom-clean Lean for the objects they define;
the fourth (Wmax6) is axiom-clean but mis-targeted and does NOT discharge the r=3 resultant
rung. No char-p clean-regime closure, and no deep-prize-wall closure, is claimed.
