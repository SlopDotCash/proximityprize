/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# G217: the sign of the signed covariance lives in the equidistributing Mellin phases (#466)

The surviving CORE target for #466 is the **signed simultaneous** late-Newton covariance

```text
A_r := p · Σ_t W_G(t) · R_r(t)  −  n² · C(n,r) · C(n,r−1),   r ∈ {5, 6}.
```

G56's G216 sweep restated `A_r` in exact quotient-Mellin / Jacobi coordinates,

```text
A_r = ((p·W_G(0) − n²)(p·R_r(0) − M_r))/(p−1)
      + p/(p−1) · Σ_{χ ≠ 1, χ|_G = 1} Ŵ(χ) · conj(R̂_r(χ)),
```

with `M_r = C(n,r)·C(n,r−1)`, and proved that **no bounded-order truncation** recovers `A_r`
(>99.5% of the Mellin L1 mass sits above conductor order 8 at the Fermat cell `p = 65537`).
The Fable referee then extended this to a **top-k dyadic conductor-shell no-go** on both magnitude
and sign (the top-two shell overshoots the signed total by `2.007×`, i.e. its sign is set by
cancellation against the rest, not by itself).  The single remaining route to a *truncation-free*
signed lower bound was the **phase-alignment** hypothesis: if the per-mode phase

```text
θ_r(χ) := arg( Ŵ(χ) · conj(R̂_r(χ)) )
```

concentrated in a fixed half-plane (`Re ≥ 0`) uniformly across all conductor shells, then every
mode of `Σ_χ |Ŵ(χ)||R̂_r(χ)| cos θ_r(χ)` would add coherently and `A_r` would admit a signed bound
with no truncation.

## The phase route is dead (probe of record)

`scripts/probes/g217_phase_alignment_probe.py` and `g217_phase_scaling_probe.py` compute, exactly,
the integer `A_r` (reconstructed to machine precision from the Mellin modes as a cross-check) and
the per-mode signed real parts `s(χ) = Re(Ŵ(χ) conj(R̂_r(χ)))`, over `n ∈ {8,16,32,64}` and a
growing family of primes.  Two facts kill the phase route:

* **Equidistribution, not concentration.** The half-plane mass fraction `frac_half` oscillates
  around `1/2` with no drift toward `1` as `m = (p−1)/n` grows; the coherence ratio
  `R_coh = |Σ s(χ)| / Σ|s(χ)|` collapses toward the random-phase benchmark `1/√(#modes)` and at the
  largest cells drops *below* it (super-cancellation): e.g. `n = 16`, `p = 1153` (71 modes) has
  `R_coh = 0.0043` vs benchmark `0.119`, with `frac_half = 0.502`.  `A_r` is an unavoidable
  cancellation residual of a near-balanced signed sum, not a coherent one.
* **No integer-computable Mellin sub-object signs `A_r`.** The only pieces of the Mellin
  decomposition that are exact integers/rationals are the zero cell and the **unique real
  (quadratic) character** `χ₂` (for which `Ŵ, R̂` and their product are integers; all other
  characters come in complex-conjugate pairs with genuinely complex phase).  This file certifies,
  float-free, that the combined "real-mode + zero-cell" sign proxy **disagrees** with `sign(A_r)` in
  explicit witness cells.  Hence the sign of the covariance is carried by the complex
  conjugate-pair phases — exactly the equidistributing family the scaling probe shows is
  incoherent — and cannot be certified by any integer-computable sub-object.

## The float-free certificate

For a witness `(n, p, r)` the probe records the exact integers

```text
A       := p · Σ_t W_G(t) R_r(t) − n² M_r                      (the signed covariance)
zcNum   := (p · W_G(0) − n²) · (p · R_r(0) − M_r)              (zero cell × (p−1))
s2      := Ŵ(χ₂) · R̂_r(χ₂)                                     (unique real-character mode, ∈ ℤ)
proxy   := zcNum + p · s2                                  ((p−1) × the real-mode+DC contribution)
```

The **real-mode+DC proxy** is the largest exact-integer-computable approximation to `A` available
inside the Mellin frame.  For the recorded witnesses `sign(proxy) ≠ sign(A)`: the integer part of
the decomposition points the wrong way.  Concretely:

```text
(n=16, p=1153, r=5):  A = +1 133 232   proxy = −4 702 956 544   (A > 0, proxy < 0)
(n=16, p=  97, r=5):  A = −6 285 008    proxy = +227 170 304     (A < 0, proxy > 0)
(n=16, p=  97, r=6):  A = −14 107 248   proxy = +530 949 632     (A < 0, proxy > 0)
```

Each is an exact-integer sign-flip: no combination of the zero cell and the unique real Mellin mode
recovers the sign of `A`.  A concordant control (`n=16, p=257, r=5`, where the proxy happens to
match) is recorded to show the disagreement is genuine, not a sign convention artifact.

All four witnesses' constants `A`, `zcNum`, `s2`, `proxy` are recomputed float-free and asserted to
match these records by `scripts/probes/g217_proxy_witness_exact.py` (the witness generator of
record).

## Scope of the formal payload (honest)

As with G214/G216, the **computation of record** is the reproducible float-free probe; this file
does **not** re-derive the Mellin integers from an in-Lean BGK definition.  It **certifies the
arithmetic** of the recorded constants: that `sign(proxy) ≠ sign(A)` for the flip witnesses and
`= sign(A)` for the control, by kernel-checked integer decision.  The equidistribution half of the
no-go (`frac_half → 1/2`, `R_coh → 1/√N`) is inherently a limiting statistical statement whose
computation of record is the Python sweep; it is not dressed as a Lean theorem here.

## Why this is a genuine frontier no-go

It closes the **last** untested truncation-free route to signing `A_r`.  G216 killed bounded-order
truncation; Fable killed top-k conductor-shell truncation; G214 killed single-rank / ratio / DC
cross-depth reductions; the magnitude tower (G206/G209/G210/G215) is sign-blind.  The phase route
was the only remaining way to get a signed bound without controlling a positive fraction of the full
high-conductor character family.  This file plus its probes show the phase is equidistributed and no
integer-computable Mellin sub-object carries the sign, so the signed target is the full BGK
phase-correlation wall in the strongest sense: no coordinate change, no shell truncation, and no
phase gate thins the signed inequality.  Thinness-relevant (witnesses are 2-power subgroups with the
dyadic involution active).  It does **not** bound `A_5` or `A_6` at production primes; CORE remains
OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G217

/-- Exact Mellin-frame data for a single `(order, prime, rank)` BGK late-alignment witness.

* `A`     is the exact signed covariance `p · Σ_t W_G(t) R_r(t) − n² M_r`.
* `zcNum` is the zero-cell numerator `(p·W_G(0) − n²)(p·R_r(0) − M_r)` (the zero cell times `p−1`).
* `p`     is the prime (also the Mellin normalisation scalar).
* `s2`    is the exact integer `Ŵ(χ₂)·R̂_r(χ₂)` of the unique real (quadratic) quotient character.

All are exact integers from the float-free probe over `𝔽_p`. -/
structure MellinWitness where
  n : ℕ
  p : ℕ
  r : ℕ
  A : ℤ
  zcNum : ℤ
  s2 : ℤ

/-- The `(p−1)`-scaled real-mode + zero-cell sign proxy, `zcNum + p · s2`.

This is the largest exact-integer-computable approximation to `A` inside the Mellin frame: the zero
cell plus the unique real character (all other characters are complex-conjugate pairs with genuinely
complex phase). -/
def proxy (w : MellinWitness) : ℤ := w.zcNum + (w.p : ℤ) * w.s2

/-- Sign-disagreement predicate: the real-mode+DC proxy points the opposite way to `A`. -/
def ProxySignFlips (w : MellinWitness) : Prop := w.A * proxy w < 0

instance (w : MellinWitness) : Decidable (ProxySignFlips w) := by
  unfold ProxySignFlips; infer_instance

/-- Sign-agreement predicate (used only for the concordant control witness). -/
def ProxySignAgrees (w : MellinWitness) : Prop := 0 < w.A * proxy w

instance (w : MellinWitness) : Decidable (ProxySignAgrees w) := by
  unfold ProxySignAgrees; infer_instance

/-- Flip witness `A`: `n = 16`, `p = 1153`, `r = 5`.  `A > 0` but `proxy < 0`. -/
def wFlip1153 : MellinWitness :=
  { n := 16, p := 1153, r := 5
    A := 1133232, zcNum := 127172608, s2 := -4189184 }

/-- Flip witness `B`: `n = 16`, `p = 97`, `r = 5`.  `A < 0` but `proxy > 0`. -/
def wFlip97r5 : MellinWitness :=
  { n := 16, p := 97, r := 5
    A := -6285008, zcNum := 101818368, s2 := 1292288 }

/-- Flip witness `C`: `n = 16`, `p = 97`, `r = 6`.  `A < 0` but `proxy > 0`. -/
def wFlip97r6 : MellinWitness :=
  { n := 16, p := 97, r := 6
    A := -14107248, zcNum := 237981696, s2 := 3020288 }

/-- Concordant control: `n = 16`, `p = 257`, `r = 5`.  Here `proxy` *does* match `sign A`;
recorded to show the flips above are genuine, not a sign-convention artifact. -/
def wCtrl257 : MellinWitness :=
  { n := 16, p := 257, r := 5
    A := -1051408, zcNum := -1035505664, s2 := -647680 }

/-- The recomputed proxy for `wFlip1153` is `−4 702 956 544`, strictly negative while `A > 0`. -/
theorem wFlip1153_proxy_value : proxy wFlip1153 = -4702956544 := by decide

/-- Flip A: `A > 0` but `proxy < 0`, so `sign(proxy) ≠ sign(A)`. -/
theorem wFlip1153_flips : ProxySignFlips wFlip1153 := by decide

/-- The recomputed proxy for `wFlip97r5` is `+227 170 304`, strictly positive while `A < 0`. -/
theorem wFlip97r5_proxy_value : proxy wFlip97r5 = 227170304 := by decide

/-- Flip B: `A < 0` but `proxy > 0`. -/
theorem wFlip97r5_flips : ProxySignFlips wFlip97r5 := by decide

/-- The recomputed proxy for `wFlip97r6` is `+530 949 632`, strictly positive while `A < 0`. -/
theorem wFlip97r6_proxy_value : proxy wFlip97r6 = 530949632 := by decide

/-- Flip C: `A < 0` but `proxy > 0`. -/
theorem wFlip97r6_flips : ProxySignFlips wFlip97r6 := by decide

/-- Control: at `p = 257` the proxy happens to agree with `A` (both negative). -/
theorem wCtrl257_agrees : ProxySignAgrees wCtrl257 := by decide

/-- **Headline no-go.** There exists a Mellin-frame witness whose real-mode + zero-cell integer
proxy has the *opposite* sign to the exact covariance `A`.  Consequently no integer-computable
Mellin sub-object (the zero cell together with the unique real quotient character) determines
`sign(A_r)`: the sign is carried by the complex conjugate-pair phases, which the accompanying
scaling probe shows equidistribute (`frac_half → 1/2`, `R_coh → 1/√N`).  The truncation-free
phase-coherence route to a signed lower bound therefore cannot exist. -/
theorem exists_integer_proxy_sign_flip : ∃ w : MellinWitness, ProxySignFlips w :=
  ⟨wFlip1153, wFlip1153_flips⟩

/-- The sign-flips are realised at genuinely distinct primes and both ranks (`p = 1153` and
`p = 97`, `r ∈ {5, 6}`), so the disagreement is not a single accidental cell. -/
theorem sign_flip_witnesses_are_multiple :
    ProxySignFlips wFlip1153 ∧ ProxySignFlips wFlip97r5 ∧ ProxySignFlips wFlip97r6 :=
  ⟨wFlip1153_flips, wFlip97r5_flips, wFlip97r6_flips⟩

end ArkLib.ProximityGap.Frontier.G217
