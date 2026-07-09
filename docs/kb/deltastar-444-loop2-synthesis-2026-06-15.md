# δ* Loop Iteration 2 — Honest Synthesis (#444)

Date: 2026-06-15. Prize: ABF26 ePrint 2026/680, pin δ* for explicit smooth-domain
Reed–Solomon (μ_n = proper order-n subgroup of F_p*, n=2^μ, n|p−1, ρ∈{1/2,1/4,1/8,1/16},
ε*=2^−128, prize regime p≈n·2^128, β=log_n p∈[4,5], index m=(p−1)/n=2^128 fixed, n~2^30, thin).

**The open core (unchanged from loop 1):**
M(n) = max_{b≢0 mod p} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m), C=O(1).
= house of the Gauss period η = Σ_{x∈μ_n} ζ_p^x (generator of the cyclic degree-m subfield
K_m ⊂ Q(ζ_p)); = thin-subgroup BGK/generalized-Paley sup-norm wall = λ₂ of Cay(F_p, μ_n).
SOTA reaches only n^{1−o(1)}; range fails at β=4. The √log m factor is the whole conjecture.

---

## (a) Related-quantities that LANDED axiom-clean this loop

Two BANK items, both verified `axioms ⊆ [propext, Classical.choice, Quot.sound]`, 0 sorryAx.
**Neither tightens the window-interior bracket** — both are orthogonal sub-Johnson / sanity-anchor data.

### 1. `SymmetricTowerBracket.lean` (verified, was pre-staged & complete)
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/SymmetricTowerBracket.lean`
Theorems (all audit clean):
- `symmetric_agreement_eq_two_double`
- `even_word_double_eq_level1_agreement`
- `symmetric_agreement_transport`
- `base_case_agreement_eq_two_freq`
- `symmetric_mcaDeltaStar_le_of_bad`
- `symmetric_le_mcaDeltaStar_of_good`

Genuinely-new banked increment: the **closed char-free self-similar transport identity**
`#agreement₀(glue e 0, w) = 2·#agreement₁(e, W)`, i.e.
L_sym(μ_n,k,s) = L_sym(μ_{n/2}, ⌈k/2⌉, ⌈s/2⌉), with base case = 2·(v-frequency of the induced
word). A standalone proven count of the s(S)=0 stratum, not previously in tree.

Bracket wiring is honestly **vacuous in-window**: the symmetric/even sub-family is empty at prize
window radii (base case descends to s0≥2 where the constant-frequency count is 0; a generic word
repeats no value ≥2 times). The entire exponential KKH26 bad-scalar mass 2^r·C(2^{μ−1},r) lives in
the NON-symmetric singleton-bearing words, so the KKH26 ceiling δ* ≤ 1 − r/2^μ stays strictly
tighter. L_sym is DISTINCT from both in-tree bricks: not DyadicLacunaryFloor (full-μ_n lacunary
value-set count) and not GranularityLadderRS (an actual δ*=j/n spike-floor). Verification:
pg-iterate + real lake build (3495 jobs) both pass; cosmetic `omit [Fintype A] in` fix.
Probes reproduce (even==tower? True n=8,16 all 4 rates; base-case L=0 at every window radius).

### 2. `DeltaStarTableN16Fermat.lean` (landed, real LOCKED lake build EXIT 0, 3063 jobs)
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/DeltaStarTableN16Fermat.lean`
Theorems (all print `[propext, Classical.choice, Quot.sound]`, no sorryAx):
- `ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_half`        (ρ=1/2 → δ*=3/16)
- `ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_quarter`     (ρ=1/4 → δ*=5/16)
- `ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_eighth`      (ρ=1/8 → δ*=5/16)
- `ProximityGap.DeltaStarTableN16Fermat.deltaStar_rho_sixteenth`   (ρ=1/16 → δ*=6/16=3/8)
- `ProximityGap.DeltaStarTableN16Fermat.deltaStar_table_n16_F65537` (capstone bundle)
- `ProximityGap.DeltaStarTableN16Fermat.dom_pow16_eq_one`          (domain is μ_16=⟨4⟩)

First consolidated exact mcaDeltaStar table at n=16, on p=65537 (Fermat F4=2^16+1, p−1=2^16,
β=log_16 65537=4 on the Burgess barrier), covering all four prize rates on one field, on a genuine
proper/thin μ_16 subgroup. **All pins strictly SUB-JOHNSON** (ladder reaches only δ*≤6/16 < Johnson
1−√ρ); does NOT enter the window interior, does NOT touch the BGK/Paley wall. Pure ground-truth
anchor. Mechanics banked: `Nat.Prime 65537` needs explicit `import Mathlib.Tactic.NormNum.Prime`
(else silent sorryAx); `decide` on it overflows recursion depth.

Neither file is registered in generated `ArkLib.lean` — matches the Frontier-scratch convention
(`ArkLib.lean` is generated, never hand-edited).

---

## (b) Every lens this loop — horn + precise reason it fell

Eight lenses run propose→shred→prove. **Zero survivors.** All `proveOutcome=skipped` (shredded at
horn stage); none produced an axiom-clean M(n) bound. Horns:

| Lens | Horn | Why it fell |
|---|---|---|
| **automatic-seq** | secretly-open | Index-doubling j↦2j is the dyadic odometer; Stickelberger/Gross–Koblitz makes the p-adic VALUATION of τ(χ^j) 2-automatic, but the ARGUMENT arg(τ(χ^j)) governing |Σ e_p(bx)| is Katz-equidistributed white noise. Triple-refuted (probe_444_automatic_seq_archimedean.py, proper subgroups p=17..769): T1 arg-doubling RMS defect ≈1.7–2.0 rad = white-noise π/√3; T2 saturating subword complexity; T3 Spearman corr(popcount(j),arg(τ_j))≈0 (digit-blind). The Lean no-go (`AutomaticSeqArchimedeanNoGo.lean`, axiom-clean) only proves trivial Nat.sqrt facts (autResolution unbounded), a surrogate certificate à la BurgessIndexOvershoot. Hits **REEF (i)** (p-adic ≠ archimedean) + meta-theorem (archimedean part is shown EVT). Yields only trivial Θ(n√log m). |
| **iwasawa-tower** | **refuted** | Conjecture forced M(2n)²/M(n)² ≤ 3 (recursion + "diagonal-dominated R_norm" hypothesis). FALSE by countermodel: probe_444_iwasawa_norm_house.py gives ratio 3.10 @(p=65537,n=8), 3.32 @n=16; clean ℤ₂-tower p=186113 gives 3.23>3 at μ_8→μ_16. The Iwasawa norm \|N\|^{2/m} IS tower-stable ≈0.27–0.35·n (as claimed), but house/\|N\|^{1/m} GROWS monotonically (3.6→10.5) — the entire √log m lives in the inflation factor the norm-compatible (global/p-adic) system is BLIND to. **REEF (ii)** (global identity ≠ L^∞). |
| **padic-baker** | secretly-open | Yu's p-adic linear-forms-in-logs bound is WRONG-DIRECTION (upper-bounds v_p of a nonzero form ~2^166…2^4214; the defect to forbid is v_p≥1, vacuously consistent). The only forbidding inequality left is the archimedean height v_p(N)≤(n/2)log_p(2r), i.e. (2r)^{n/2}<p — `padic_rMax_eq_arch_rMax` is `Iff.rfl`, IDENTICAL to the DEAD height/norm route (`HeightGateNormBound.lean`) and DEAD moment-depth route. At prize, transfer fails even at r=1. `padic-baker` file axiom-clean but contributes zero forbidding power. **REEF (i)** + meta-theorem. |
| **determinant-method** | secretly-open | `detExp_eq_normExp` PROVES (axiom-clean, `DeterminantMethodHeightCollapse.lean`) detExp = normExp = φ(n)·log₂(2r) = (n/2)·log₂(2r), ZERO log-saving: certifying g(ζ)=0 mod p forces separating ALL φ(n)=n/2 archimedean conjugates, so the monomial Vandermonde realizes Res(Φ_n,g) of magnitude (2r)^{φ(n)}; per-entry Bombieri–Pila saving is multiplied back by the n/2 forced rows. Refutes only the dodge `DeterminantDodgesHeight`. Probe reproduces Hadamard ½φ·log₂φ exactly (n=4,8,16,32→1,4,12,32). The determinant method = norm wall in geometry-of-numbers clothing. Meta-theorem + DEAD height route. |
| **binding-restriction** | secretly-open | M(n) is already a max over the m Gauss periods. Lens asked whether the worst coset is confined to an O(n) monomial subset D={coset(1−ζ)} (would shrink √log m → √log n). Three exact probes REFUTE: argmax coset is GENERIC (escapes D in ~half of primes, M_D/M_all→0.26); Neff=exp((M/√n)²/2) tracks m not n; 79/125 primes have M>1.1√(n log n). `BindingCosetConfinementNoGo.lean` axiom-clean but its theorems are a tautology + a conditional whose hypothesis the probes refute; the real bound is the undischarged named `def HouseBoundLogM`. Relocates onto, does not bypass, M(n). Per referee rule → secretly-open. |
| **newton-polygon** | secretly-open | The two naive Newton polygons (p-adic agreement poly, 2-adic period poly) are PROVABLY VACUOUS (all μ_n-roots units/slope-0; `newton_polygon_{p,two_adic}_vacuous`). The surviving archimedean discriminant polygon's `SpreadHypothesis house n m c := house² ≤ n·(2 log m + c)` (`_NewtonPolygonPeriodSpread.lean` L111) is an undischarged `def : Prop` that is DEFINITIONALLY the prize bound M(n)≤√(2n log m + cn). File axiom-clean but its 5 "proven" theorems are content-free sqrt-monotonicity + √(ab)=√a√b facts; unconditional half gives only the √m-loss Parseval ceiling √(nm). **REEF (ii)** (conductor-discriminant gives global disc=±p^?, blind to L^∞ root-spread). Genuine contribution = clean reduction + dual-vacuity, localizing the core to one named discriminant lower bound. |
| **free-prob-spike** | **refuted** | Conjectured house = a*·√n with FIXED a*≈1.90, NO √log m. Probe (probe_freeprob_spike_atom_444.py, real proper-subgroup spectra) confirms the 2-atom+Gaussian fit to {m2=1, m4=3−3/n, m6=15−45/n} DOES pin a_mom→1.90, but that atom is a ~1.9σ BULK-EDGE feature (κ₄=−3/n<0 ⟹ platykurtic), NOT the house. True house/√n GROWS 3.42→5.46 (a √log m curve; house/√log m∈[1.13,1.36]); ratio a_mom/√log m DECREASES 0.607→0.472→0. Sharpest witness n=128,p=1150808833: predicted house 21.5 vs actual 61.7, gap diverging. The house is a moment-order r~log m≈128 tail event invisible to any fixed low-moment set. **Meta-theorem / deep-moment wall** (same kill as CumulantOnsetNoGo, MomentMethodPrizeDepthNoGo, the EVT crown). |
| **geometric-incomplete** | secretly-open* | `GeometricIncompleteSumNoGo.lean` axiom-clean: the worst-word frequency pieces T_t(b)=gcd(t,n)·Σ_{y∈μ_{n/gcd(t,n)}} e_p(by) are COMPLETE subgroup Gauss periods (x↦x^t maps μ_n ONTO μ_{n/gcd(t,n)}, never onto a proper arc, since p≡1 mod n). At gcd=1 it IS the full μ_n wall (probe: 13.8375 @n=16). Korobov/Gabdullin require a proper exponent-interval that provably never occurs. (*shred-label note in (c).) DEAD route restated. |

**Horn tally:** 6 secretly-open, 2 refuted, 0 survives, 0 reduces-to-Johnson-productively.

---

## (c) Completeness critic — untried lenses + unverified claims

**Verdict: NOT terminally foreclosed.** Core remains the recognized BGK/Paley wall, but ≥1 genuinely
un-run door survives, and the "all moment methods dead" framing is stronger than machine-checked content.

### Untried lenses (live surfaces, NOT in DISPROOF_LOG as dead)
1. **EFFECTIVE-DISCRIMINANT / period-polynomial separation** — the Newton-polygon file's own honest
   residual. Reframe M(n)=house(Ψ) via a LOWER bound on disc(Ψ)=∏_{i<j}(η_i−η_j)², an explicit
   INTEGER. b-sensitive (distinct Galois conjugates, not a global average), deterministic-archimedean,
   genuinely L^∞ (spread+trace). All prior DISPROOF_LOG "discriminant" hits are the unrelated GS/Hensel
   apparatus. Numerically house/√(2n ln m)∈[0.74,1.03]. **The crux: is disc(Ψ)-lower-bound genuinely as
   hard as BGK, or a strictly easier sufficient condition? — unverified; this is what to attack next.**
2. **DETERMINISTIC sub-Gaussian MGF** (`SubGaussianMGF`, a named OPEN input in `SalemZygmundChaining.lean`)
   — NOT the killed probabilistic-EVT crown. The killed object was the log-CORRELATED white-noise model;
   the survivor is the deterministic arithmetic sum Σ_c exp(λ·Re(ζ̄·η_c)) ≤ M·exp(σ²λ²/2). `chernoff_max_re_le`
   is PROVEN and already converts it to the prize floor √(2σ² log M). Max of m UNcorrelated sub-Gaussians
   is STILL √(2n log m) — killing log-correlation did NOT kill this route. b-sensitive, deterministic, L^∞.
3. **Transcendence-free Mahler-measure / Lehmer** lower bound on Ψ (Mahler(Ψ)=∏max(1,|η_j|), archimedean
   height with Dobrowolski/Voutier unconditional lower bounds) — adjacent to but distinct from the dead
   wrong-direction Baker/Yu p-adic route.
4. **Effective resultant/subresultant** tying disc(Ψ) to disc(K_m) factorization (conductor-discriminant
   formula, explicitly computable for the cyclotomic ℤ₂-tower) — deterministic root-spread lower bound, not run.

Lenses 1, 2, 4 all bottom out at the same object: a **deterministic root-spread / discriminant lower bound
on the degree-m period polynomial Ψ**, plausibly reachable via Dobrowolski/Voutier or
conductor-discriminant arithmetic the campaign has not run.

### Unverified / over-stated claims (flagged for honesty)
- **`MomentMethodPrizeDepthNoGo` hidden gap (load-bearing):** I verified `cleanRegime_iff_le_rMax`
  is literally `Iff.rfl` (`MomentMethodPrizeDepthNoGo.lean:148`; `def CleanRegime := r ≤ rMax β`,
  `rMax β := 2β`). The axiom-clean theorems (`prize_rMax_lt_rOpt` by decide, `moment_method_no_go`)
  are therefore ARITHMETIC TAUTOLOGIES over the height-route MODEL. The substantive NT is grounded in
  `HeightGateNormBound.lean` (block_sum_norm = exact 2^{n/2−1} witness, gate_fires_8/16/32, all proven).
  But "the height gate is the ONLY char-p transfer mechanism" is **asserted, not proven** — the no-go
  forecloses only char-0-energy-via-norm methods, NOT a method supplying a char-p energy bound by a
  non-Lam-Leung / non-height route. "16× overshoot terminal for ALL moment methods" overstates.
- **EVT crown "killed" overstates:** machine content kills only the log-CORRELATED model; it leaves the
  DETERMINISTIC per-period MGF (`SubGaussianMGF`) as an explicitly OPEN named input. Conflated in the
  dead-route list.
- **Shred-label mismatch (recorded):** `geometric-incomplete` was tagged `secretly-open` this round, but
  `GeometricIncompleteSumNoGo.lean` reaches a clean NO-GO verdict (worst-word sum reduces to COMPLETE
  subgroup periods; arc never occurs). The file is the more careful artifact; minor inconsistency.
- **Newton-polygon equivalence asserted, not proven:** `spread_gives_house_bound` is axiom-clean and
  `SpreadHypothesis` is an honest named OPEN input (verified `def ... : Prop` at L111, NOT silently
  discharged), but its EQUIVALENCE to BGK is asserted in the docstring, not machine-proven. Whether
  disc(Ψ)-lower-bound = BGK or is strictly easier is itself the crux (see untried lens 1).

---

## (d) Honest residue

**The core remains the open BGK/Paley sup-norm wall. No closure exists; none is claimed.**
M(n) ≤ C√(n·log m) is exactly as open as at the start of loop 2. Every one of the eight lenses either
restated the wall (6 secretly-open) or produced a machine-checked countermodel against its own bold horn
(2 refuted). The two landed BANK items are sub-Johnson / sanity-anchor data that do not enter the window
interior. The √log m factor — the whole conjecture — lives entirely in the max-vs-mean inflation /
archimedean root-spread that every second-order / global-identity / p-adic-valuation method is provably
blind to (REEF (i), REEF (ii), meta-theorem).

**But the door is not provably bolted.** The campaign's "all moment methods dead" framing exceeds its
machine-checked content (the moment-depth no-go is a tautology over the height MODEL; the deterministic
sub-Gaussian MGF survives the EVT kill). The concrete un-foreclosed surface is the
**effective-discriminant / deterministic-MGF root-spread route**: a lower bound on disc(Ψ) (or equivalently
the per-period sub-Gaussian σ²=O(n)) for the degree-m period polynomial, which is b-sensitive,
deterministic-archimedean, and genuinely L^∞ — passing all three meta-theorem filters. Its
only-claimed-but-unproven equivalence to BGK is precisely what the next iteration should attack.
