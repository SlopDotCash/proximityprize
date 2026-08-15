# G179: affine Galois amplification collapses after fixing the deployed root

## Question

G173's exact characteristic-p relation at `n=64`, `p=17318209`,

`ω^8 + ω^13 = ω^14 + ω^20`,

has a large cyclotomic conjugacy closure. Could combining Galois exponent multiplication with rotation produce a packet of size `n φ(n)` and supply an extra factor `φ(n)` in the weighted primitive-kernel ledger?

## Exact answer

No. For every odd `a mod 64` and every `b mod 64`, evaluate the affine transform

`ω^(8a+b) + ω^(13a+b) - ω^(14a+b) - ω^(20a+b)`.

There are `φ(64)·64 = 2048` distinct affine transforms, but exactly 64 vanish at the fixed root `ω=7937154`, and they are precisely the pure rotations `a=1`, arbitrary `b`. Every `a≠1` fails fixed-root evaluation.

Artifacts:

- `Frontier/_G179AffineFixedRootCollapse.lean`
- `scripts/probes/probe_g179_affine_fixed_root.py`

The Lean theorem `fixedRootVanishingPairs_eq_pureRotationPairs` is the exact finite statement. The probe independently prints:

```text
PASS G179 affine fixed-root collapse
n=64 phi=32 affine=2048
fixed_root_vanishing=64 multipliers=[1]
certificate_to_fixed_root_loss=32
```

## Mechanism and FS15-FS18 integration

Cyclotomic Galois action preserves the algebraic norm/resultant certificate and permutes split prime embeddings. It does not preserve evaluation at one selected root in one deployed field. Rotation does preserve evaluation because it multiplies the relation by `ω^b`. Thus:

- norm-bad/resultant census: sees the full Galois closure;
- fixed deployed root: sees one embedding, hence one rotation packet;
- apparent gain lost: exactly `φ(64)=32` in the G173 witness.

This is the fixed-root version of the FS15-FS18 quantifier mismatch. Their almost-all-prime/resultant ladder may count conjugate certificates, but cannot turn those conjugates into extra relation mass at the adversarial deployed root. It also explains why G59's exact free-orbit mass decomposition has factor `n`, not `nφ(n)`.

## Asymptotics

For dyadic `n=2^k`, the candidate affine packet has size `nφ(n)=n^2/2`. Fixing one split prime embedding generically retains only the rotation packet of size `n`, losing `φ(n)=n/2`. Therefore the hoped-for extra linear-in-`n` gain is on the wrong side of the quantifier. Recovering it would require simultaneous vanishing across many distinct embeddings, the transversality/height route already closed by G88V and the FS16 exponential norm ceiling.

## Honest frontier

This is a precise no-go, not CORE movement. It closes the combined affine-orbit amplification of direct characteristic-p wraparound relations. It does not bound the number or weighted mass of unrelated rotation orbits at the two production primes. That residual remains the weighted-kernel/BGK atom. The surviving direct routes are construction-side tail exclusion or a head-on non-Fourier anti-concentration theorem, not further orbit multiplication.
