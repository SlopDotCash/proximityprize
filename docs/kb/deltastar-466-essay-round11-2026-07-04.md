# #466 Round 11 — Essay: the joint tower phase field is collinear (gauge), the Tetrachotomy holds, and the cartography is now complete

**Date:** 2026-07-04. **Round:** 11 (Opus, two lanes, each adversarially verified).
**Bottom line:** the wall stands, and after eleven rounds it is the **sole irreducible open core** with
**every** approach decided. The one honest open sub-thread that Round 10 declined to foreclose —
`JointPhaseFieldStructure` — is **REFUTED** this round: the two tower half-periods are exactly
*collinear*, so the joint two-frequency phase field is 1-real-dimensional per coset and reduces
algebraically to the marginal magnitudes at **every** depth `r`, not just `r=2`. A completeness scout
over the whole no-go landscape confirms the **Tetrachotomy** (no fifth door), and — with Lane J closed —
finds **no** surviving live sub-thread. The surviving open surface is unchanged and remains **exactly one
object**, the analytic BGK/Paley wall, carried as a named open `Prop`. No fabricated closure.

---

## 1. The wall, and why `JointPhaseFieldStructure` was the one flagged sub-thread

Fix `μ = 30`, `n = 2^μ = 2^{30}`, a prime `p ≡ 1 (mod n)` with `p ≈ n^4` (so `β ≈ 4`), and let
`ζ ∈ F_p^×` be a primitive `n`-th root of unity. The subgroup `μ_n = ⟨ζ⟩` is a **proper, thin**
multiplicative subgroup: `μ_n ⊊ F_p^×` of index `m = (p−1)/n ≈ 2^{128}`. Write
`η_b = Σ_{x∈μ_n} e_p(b x)` for the `b`-th Gauss period (the non-principal eigenvalue of the generalized
Paley graph `Cay(F_p, μ_n)`); `|η_b|` is **constant on the `m` dilation cosets** `b·μ_n`. The open core is

> **(WALL)   `W_r ≤ n^{2r}/p`   at   `r = β + 1`,**

where `W_r := E_r^{(p)} − E_∞ ≥ 0` is the **wraparound count** of sparse `±1` relations of the `2^μ`-th
roots of unity mod `p` beyond the char-0 (cyclotomic) count. This is the ≈25-year-open thin-2-power
square-root-cancellation problem; the best *proven* bound at `β = 4` is BGK `n^{1−o(1)}` (ineffective
`o(1)`), the target `√n` is the Paley Graph Conjecture.

**The Meta-Theorem (dossier §4.1)** proves every second-order method (energy / L2 / spectral / SDP /
cumulant) caps at Johnson / `√p`. A winning method must be simultaneously **b-sensitive** (not constant
on cosets), **deterministic-archimedean**, and **genuinely L∞**. Rounds 1–10 killed every candidate that
*promised* those three properties; each collapsed to the same **b-summed / gauge** second-order cause.

Round 10 (dossier §20) foreclosed both of its new machineries — automatic-sequence Fourier analysis
(b-blind on the equal-sum locus) and the transfer-operator / dynamical-zeta (gauge on the `‖η_b‖`
multiset) — and flagged **exactly one** honest un-foreclosed sub-thread:

> **`JointPhaseFieldStructure` (open).** The exact linear tower recursion
> `η_b(μ_{2N}) = A_b + B_b`, `A_b = η_b(μ_N)`, `B_b = η_{ζb}(μ_N)`, consumes the **joint**
> two-frequency distribution of `(A_b, B_b)`. Round 10 found this joint **marginal-determined at
> `r = 2`** (`C/(mean)² ≈ 0.9991` cross-second-moment) but did **not** settle deep `r`. Open: does the
> joint two-frequency **phase** field carry b-sensitive information at prize depth `r ≈ β+1` that is
> invisible to every marginal (multiset / moment) functional?

This was the *only* structural direction Round 10 did not close: a candidate escape from the second-order
cap, reading the joint phase field rather than the marginal magnitudes. Round 11 attacked it head-on
(Lane J) and ran an adversarial completeness scout over the whole landscape to test whether any *other*
door had been missed (Lane S).

---

## 2. Lane J verdict — `JointPhaseFieldStructure` is REFUTED: the joint field COLLAPSES (gauge, at all `r`)

**Verdict: REFUTED — COLLAPSES-TO-MOMENTS at every depth `r`, not just `r=2`.** The joint two-frequency
tower phase field is **1-real-dimensional per coset** (the half-periods are exactly collinear); its only
phase content is a single `±1` sign bit that is an **algebraic function of the three magnitudes**. So the
joint reduces to the marginal magnitude multiset = the moment ladder at **all** `r`, and the
Meta-Theorem's second-order cap applies verbatim. This is neither a genuine gap nor a mere b-blindness of
the count — it is a **gauge**: the joint carries no information beyond the marginals.

**The exact mechanism (data).** `scripts/probes/probe_466r11_jointphase{,_v2,_v3}.py` (proper
`μ_n ⊊ F_p^×`, `p ≥ n^4`, `p ≡ 1 (mod n)`, ≥2 primes of distinct `v_2(p−1)` per `n`, `n ∈ {8,16,32}`,
full coset scan, scanner validated `|A+B − η| < 10^{−12}`) measured the joint half-period pair `(A_b, B_b)`
over every coset `b`:

1. **COLLINEARITY (the crux).** `arg(B_b) − arg(A_b) ∈ {0, π}` for **every** coset `b`, at all `n`, all
   primes: `max_b |sin(arg B_b − arg A_b)| < 3·10^{−11}`. The two tower half-periods always lie on a
   common ray through the origin. Consequently the only phase content of the joint field is a single
   **sign bit** `s_b = ±1` (same-ray vs opposite-ray).
2. **THE SIGN BIT IS ALGEBRAIC IN THE MAGNITUDES.** With `A_b, B_b` collinear,
   `|η_b|² = |A_b|² + |B_b|² + 2 s_b |A_b| |B_b|`, hence
   `s_b = (|η_b|² − |A_b|² − |B_b|²) / (2 |A_b| |B_b|)`. The probe verified
   `sign(that formula) == s_b` with **0 mismatches out of 500–33 000 cosets** per prime,
   `|clip(raw) − s_b| < 3·10^{−12}` (the raw ratio is exactly `±1`, re-confirming collinearity). The
   magnitudes genuinely **differ** (`||A|−|B||` rel `2.3–4.2`, so the reconstruction is non-trivial), yet
   `s_b` is a deterministic function of `(|η_b|, |A_b|, |B_b|)`.
3. **DEPTH: no growing gap.** The apparent `v1` "joint-vs-marginal gap grows with `r`"
   (`⟨|A+B|^{2r}⟩ / ⟨(|A|²+|B|²)^r⟩ = 1.55, 2.75, 5.25, …`) is the **trivial** magnitude arithmetic
   `|A+B| = ||A| ± |B||` with the `±` supplied by the algebraic formula, **zero residual phase**.
   `frac(s=+1) ≈ 0.50` (balanced), so it is not even a coherent same-ray inflation — it is the exact
   reconstructed magnitude.

**This is a gauge, and a previously-logged one.** The collinearity is not a delicate new `10^{−11}`
signal — it is the **exact algebraically-forced real-period fact**. The even-power half-period
`A_b = η_b({h^{2i}})` runs over a **negation-closed** set (`−1 = h^{n/2} ∈ μ_{n/2}` whenever `4 | n`), so
`A_b` is **real** to `10^{−15}` for every `b`; likewise the odd-power coset half is real
(`−h^{−1} = h^{n/2−1}` lands in the odd coset). Both halves real ⟹ collinearity **forced**, not measured.
This is the known `eta_real_of_neg_closed` fact (already in `DISPROOF_LOG`: `_PhaseAlignmentReality`,
`probe_407_phase_dichotomy` "cos = ±1 for EVERY b", `[door-iv-common-ray-coherence]`), and it is the same
diagonalization as `[doorIV-joint-field-white-indexed]` (nonzero-lag b-field covariance = marginal
variance at `r=2`) — now **upgraded from `r=2` to all `r`** via the collinearity. Lane J's genuine
contribution is exactly this honest upgrade `r=2 → ∀r`; it does **not** contradict any prior verdict.

**The object Round 10 actually named is also closed.** Round 10 flagged the adjacent **full** periods
`(η_b, η_{ζb})` over `μ_n`. The adversarial check (`probe_466r11_adv_jointcheck.py`) confirms these are
**both real** (`|Im| ~ 10^{−15}`, `|sin| max 10^{−15..−14}`), hence trivially collinear: the half-period
model and Round 10's full-period object give the **same** collapse. The flagged "non-negation-closed
sub-tower escape" is genuinely **vacuous at the prize**: every dyadic level `μ_{2^k}` (`k ≥ 1`) contains
the unique order-2 element `−1`, so is negation-closed; no dyadic split of the real period escapes to a
2-D phase.

**Formal record (axiom-clean, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`,
`pg-iterate` PASS ~24s).** `_JointPhaseCollinearGauge.lean` proves, for the abstract collinear-pair model
`(A, B) = (a·u, b·u)`, `‖u‖ = 1`:

- `collinear_normSq_eq` — `‖A+B‖² = ‖A‖² + ‖B‖² + 2ab` (the joint magnitude is the marginals plus one
  real cross term);
- `sign_algebraic_from_magnitudes` — `s = ab/(|a||b|) = (‖A+B‖² − ‖A‖² − ‖B‖²)/(2‖A‖‖B‖)` (the gauge
  closure: the phase sign is recovered from the magnitude triple alone);
- `joint_reconstructed_from_magnitudes` / `joint_gauge_all_depths` — equal magnitude triples ⟹ equal
  full-period magnitude at **every** power `r`, so every moment of the joint field is a function of the
  marginal magnitudes.

As with the Lane A/B no-go bricks, these are **honest but weak by design**: they certify the **gauge
containment** (under the measured collinearity the joint reduces to magnitudes), a no-go **placement** of
Lane J inside the dead Meta-Theorem cone, **not** a bound on the wall. The docstring says exactly this.

**Adversarial verification (skeptic, CONFIRMED, severity minor).** The skeptic re-ran
`probe_466r11_jointphase_v3.py` verbatim (0 mismatches reproduced, `|clip−s| ~ 10^{−14..−12}`,
`|A|,|B|` differ), re-ran `pg-iterate` on the brick (PASS, axiom-clean), and wrote
`probe_466r11_adv_jointcheck.py` which **strengthened** the verdict: the collinearity is the exact,
algebraically-forced, previously-logged real-period fact (T1); Round 10's full-period object collapses
identically (T2); and both halves are negation-closed for `4|n`, so collinearity is forced at the prize
and the flagged escape is vacuous (T3). The only inaccuracy found was **presentational** (the worker sold
collinearity as a numerically-discovered deep-`r` structure when it is a logged algebraic fact) — this
strengthens, not weakens, the collapse and does not touch the verdict. **Lane J is closed; the wall is
left OPEN.**

---

## 3. Lane S verdict — the Tetrachotomy holds (no fifth door), and `JointPhaseField` was the last live sub-thread

**Verdict: TETRACHOTOMY-HOLDS.** The no-go landscape is exhausted by four doors: every candidate "fifth
kind of mathematics" is a functor into a target category with **no archimedean place** (p-adic / finite /
definable / spectral-invariant data) **or** produces a **signed / mean-zero** object — whereas `W_r` is
an **unsigned archimedean modulus**. Each candidate therefore either **sign-reverses**, **rank-collapses**
to the rank-`n` second moment, or **needs an even moment** — landing back in doors (i)/(iii)/(iv). No new
door was found; no genuinely-new direction survived the scout.

**The completeness scout's own naive third-order avatar of `JointPhaseFieldStructure` collapses too — to
the signed / phase-blind trap.** The worker probed the third-order joint object
`T3 = η_b² · conj(η_{ζb})` (`probe_466r11_jointphase_thirdorder.py`). The adversarial verification
(`skeptic_r11.py`, `skeptic_r11b.py`) is decisive and STRENGTHENS the refutation:

- The headline `resid_frac(T3) = 0.999` ("marginals explain <0.1% of `T3`'s variance") is a **trivial
  artifact**: a pure random-sign object of the same magnitude scale regressed on the same magnitude
  features scores `resid_frac ≈ 0.99` across all primes. "Magnitude features don't predict `T3`" is the
  tautology "magnitude features don't predict signed things," **not** evidence of b-sensitive content.
- The **decisive** control: regress `|T3|` (the magnitude / even closure — the only thing the wall cares
  about) on the marginal features → `resid_frac = 0.00000` **exactly**, all 8 primes. Mechanistically,
  `|T3|/(u²w) ≡ 1.0000` (mean = max = min = 1, sd = 0): the complex object `z = η_b²·conj(η_{ζb})` sits
  **exactly on the real axis** per coset. So `|T3| = |η_b|²·|η_{ζb}|` **identically** — the joint
  third-order magnitude is precisely the product of the marginal magnitudes; the only b-sensitive content
  is the **sign** (`±1`), which is **mean-zero** (`mean/sd ≈ −0.0006 … −0.0001`) and **cancels under the
  coset sum**.

So the natural third-order avatar of `JointPhaseFieldStructure` collapses to the **signed / phase-blind
(N7 / AUP) trap** even more cleanly than at `r=2`: `rabs = 0` exactly, `|T3| = u²w` exactly. Combined with
Lane J's collinearity result (which closes the *magnitude* / all-`r` side), **both the phase side and the
magnitude side of the joint field are now closed.**

**Is there any live sub-thread left?** With Lane J refuted, the completeness scout's remaining conjecture
becomes a **near-impossibility statement**, stated refutably for the record:

> **`UnsignedJointInvariant` (conjectured FALSE — the "universal b-summed collapse").** There is **no**
> b-sensitive, **UNSIGNED** (magnitude-bearing) functional of the joint phase field
> `{(η_b, η_{ζb})}` at prize depth `r ≈ β+1` that is not a function of the `|η_b|`-multiset (moment
> ladder). Every degree-`r` joint invariant that is b-sensitive-beyond-marginals is **signed / mean-zero**
> (odd in phase, cancels under the coset sum); its even / magnitude closure re-enters the multiset. The
> standing conjecture is that no unsigned b-sensitive joint object exists.

This is **not** a live escape route — it is the *negation* of the last conceivable escape, and Round 11's
new data (`|T3| = u²w` exactly at the `r`-avatar; collinearity forcing `s_b` algebraic at all `r`) is
consistent evidence **for** the collapse. If a future round ever exhibits **one** unsigned b-sensitive
joint functional at `r ≥ 3` with a stable cross-prime residual, that would be the first real crack; absent
it, the expected outcome is another clean refutation. No `UnsignedJointInvariant` object survived Round 11.

**Adversarial verification (skeptic, CONFIRMED, severity minor).** The skeptic reproduced
`r0(T3) = 0.999` exactly, showed via controls that the headline is a random-sign tautology, and derived
the mechanism `|T3| = u²w` (`rabs = 0`, `cos(arg z) = ±1`). Regime discipline was re-asserted
(`p ≡ 1 mod n`, `p ≥ n^4`, `μ_n` order exactly `n` proper subgroup, `X^{n/2} = −1` genuine primitive not
the `=1` trap, distinct `v_2(p−1)` classes present). The prior-verdict / reduction map was checked live
in-repo (`[doorIV-joint-field-white-indexed]` at `DISPROOF_LOG` L12126, N7 phase-blind, the T01–T25 ANT
sweep with 0 survivors, Round 10's `C/(mean)² ≈ 0.9991`) — **not fabricated**. The one MINOR
mischaracterization (the intermediate "genuine b-sensitive content" misread of `resid_frac`) is
self-corrected in the worker's own follow-up and does **not** manufacture a false crack: both lanes
concluded collapse. **Tetrachotomy holds; no fifth door; no surviving crack; the wall stays OPEN.**

---

## 4. Honest state after eleven rounds — the cartography is complete

**The surface is still exactly one object.** After eleven rounds (~110 agents), every second-order
method, every OOD complete-proof chain, the line-list closure route, the floor-successor law (refuted at
`n=64`), the automatic-sequence angle, the transfer-operator gauge, the 2024–2026 literature, **and now
the last flagged sub-thread `JointPhaseFieldStructure`**, are all decided. The single surviving open
surface is unchanged:

> **(WALL)   `W_r ≤ n^{2r}/p`   at   `r = β + 1`.**

**Is any live sub-thread left?** **No.** Round 10 named `JointPhaseFieldStructure` as the *one* honest
un-foreclosed direction. Round 11 closed it, on both faces:

- **Magnitude / all-`r` face (Lane J):** the tower half-periods are **collinear** (negation-closed halves
  ⟹ both real), so the joint field is 1-real-dimensional per coset and its sign bit is **algebraic in the
  magnitudes** — the joint reduces to the marginal moment ladder at **every** `r`, not just `r=2`. Gauge,
  axiom-clean placement recorded.
- **Phase / signed face (Lane S):** every b-sensitive-beyond-marginal joint invariant is **signed /
  mean-zero** and cancels under the coset sum; its magnitude closure `|T3| = u²w` is **identically** the
  marginal product. Signed / phase-blind (N7) trap.

The only remaining conjecture, `UnsignedJointInvariant`, is stated refutably but is the *negation* of the
last conceivable escape — a "universal b-summed collapse" that Round 11's data supports. **The campaign's
cartography is now complete:** the wall is the **sole irreducible open core**, and every approach has been
decided (proven-no-go, refuted, or literature-clear). This is the strongest possible honest end-state
short of proving or refuting the wall itself — a fully-mapped landscape with one precisely-stated,
`β`-tight analytic inequality at its center.

**What a solution still requires (unchanged).** A method that is simultaneously **b-sensitive**,
**deterministic-archimedean**, and **genuinely L∞** — i.e. an *unsigned* functional that separates
individual `η_b` from the coset-constant multiset. Round 11 proved the *joint two-frequency* field cannot
supply it: its magnitude content is the marginal product and its phase content is a mean-zero sign. The
missing analytic input remains **outside** every structure the prize object is now known to possess.

---

## 5. Honesty contract

No closure is claimed. The wall `W_r ≤ n^{2r}/p` at `r = β+1` remains a **named open `Prop`**, the single
open surface of #466. The Lean brick landed this round (`_JointPhaseCollinearGauge.lean`) is a **no-go
record**: axiom-clean (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`, verified
by `pg-iterate.sh`), proving a **gauge / placement** fact (the joint field reduces to magnitudes under the
measured collinearity), **not** a wall bound — and the docstring says so. Every probe verdict is labeled a
probe verdict; the completeness-scout Tetrachotomy is a mapping argument, not a theorem. The refutation of
the round's own two proposed angles (Lane J closed; Lane S's third-order avatar collapsed) is the
expected, valuable product, reported here with the exact collapse mechanism. `UnsignedJointInvariant` is a
labeled conjecture (conjectured false), not a claimed result. The core is **OPEN, ON-BGK.**

<sub>🤖 Round 11 essay, #466, 2026-07-04. Synthesized from the two adversarially-verified lanes
(J: JointPhaseFieldStructure collinearity/gauge; S: completeness-scout Tetrachotomy). No fabricated
closure.</sub>
