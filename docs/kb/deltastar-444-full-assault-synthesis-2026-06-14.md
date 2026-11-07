## Full-assault synthesis: 8 axiom-clean bricks + convergent residual (workflow `wf_e11770d1`, 41 agents)

Ran an exhaustive 4-phase multi-agent assault (recon → 18-target attack → adversarial verify → synthesize) on every open #407/#444 thread. **8/8 Lean bricks landed and independently re-verified axiom-clean (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, 0 `sorryAx`), 0 overclaims** (each re-built + axiom-audited by a skeptic agent). The campaign now converges, from every angle, on a **single** residual.

### Landed bricks (verified)
| brick | file | commit | what it proves |
|---|---|---|---|
| L1 | `BadPrimeGaloisDivisibility.lean` | `9a45c4de9` | **discharges the Galois-divisibility hypothesis** of the bad-prime bound: `p^r ∣ N(f(ζ))`, `N≠0`, `|N|≤(Σ\|coeff\|)^{[K:ℚ]}` for abstract Galois `K` — the norm core is proved **given** that each of the `r` conjugates is divisible by the principal ideal `p·𝓞_K`; vanishing modulo one prime `P ∣ p` (the finite-field input) does not imply that (e.g. `ℚ(i)`, `p=5`, `f=X−2`), so the finite-field input still needs a prime-ideal/valuation argument (audit 2026-10-28, PG-250) |
| L2 | `Q1ClaimBDegH.lean` | `8dd2727d3` | `deg H = k−1` exactly (char-0 dyadic), completing Q1 Claim A+B |
| L3 | `OrbitCountConsumerBridge.lean` | `13407165a` | wires the orbit-count identity into the `BridgeLoop43/44` consumers |
| L4 | `CharPDeepMomentTail.lean` | `a07b9f98b` | unconditional deep-moment tail (honestly scoped off-prize: reaches floor only `r≳1.36n`) |
| **L5** | `RigidityReductionPrizeScale.lean` | `f414cf059` | **KEYSTONE: char-p incidence = char-0 incidence at prize scale** (`I_p=I_0`), proven for the size gap `(2k)^{2k}<p^{k/2}` (unconditional at prize scale) |
| L6 | `LDLeMCANoGo.lean` | `c0b6fcd92` | `δ*_LD ≥ δ*_MCA` (list-decoding is the weaker challenge; can't bypass MCA) |
| **L7** | `OpenCoreConditionalPin.lean` | `d689f92b7` | **the open core as ONE Prop** `WorstCaseIncidenceBounded`, with the conditional δ\* lower pin **proven from it** via the governing law (3 faces: raw / E·q budget / orbit-count) |
| L8 | `MetaTheoremSecondOrderCap.lean` | `758bdeb1b` | meta-theorem: second-order (energy/Parseval/SDP) methods provably capped at `√S`; only high moments to depth `r≍log m` can reach the floor |

### Convergent residual — every route lands here
**The `r=k/2`-vs-`r=1` reduction:** does a δ\*-*window* bad config require the full `r=k/2` odd power-sum system (⟹ rigid ⟹ via L1+L5 the `(2k)^4<q` bad-prime bound closes δ\* **characteristic-uniformly**) or only the single `r=1` sum (⟹ floppy, q-dependent ⟹ BGK/Paley sup-norm wall)?
- **P6** (action-orbit gates): the `r=1` stratum is **non-empty at prize scale** (192/192 antipodal-free configs violate at `d≥32`) — so it's floppy *unless* the window genuinely needs the full system. Q2/Q3/Q4 all reduce to this same question.
- **P5/Mann** (sparse-poly roots): the inner per-witness Θ(n) agreement is **entirely the single dyadic factor `Φ_n`** (one antipodal-paired coset of `μ_{n/2}`) — exactly Mann/Conway–Jones dyadic prediction (only primitive vanishing relation over `μ_{2^μ}` is the antipodal pair). But `N_pencil > gcd(b−a,n)` already at n=8 deep interior (the naive orbit-count-≤gcd hope fails at the deepest bands).

### Refutations (→ DISPROOF_LOG / dead routes)
- **P7**: relaxed higher-order-MDS / BGM for explicit μ_n **REFUTED** — exact closed form `corank_Fp(μ_a;E) = a − #distinct(e mod a)` grows **Θ(a)** on every sub-subgroup coset (char-faithful, 2400/2400 exact); no O(1)-corank structured family exists for μ_n. The algebraic-HOMDS gap = the analytic BGK wall.
- **P2**: among the *old* candidate closed-forms (Kambiré edge, entropy pin, always-beyond-Johnson, `2(n−a)+1`), **none survive** the exact governing-law δ\* at small n across all 4 rates; only `|δ*−(1−√ρ)| ≤ 1/n` survives.

### NEW candidate (untested by P2; the live lead)
Char-0 (q-free, p≫n³) worst-case incidence crossing budget n gives **`n·(cap−δ*) = w_δ* − k = log₂(n)` exactly** for ρ=1/8 at n=16,32 ⟹ candidate **`δ* = (1−ρ) − log₂(n)/n`** (a Θ(log n/n) gap — *much closer to capacity* than the standing `Θ(1/log n)`). 3 small-n points; needs n=64 + Mann-count confirmation (in progress). `docs/kb/deltastar-407-char0-logn-over-n-candidate-2026-06-14.md`.

### Reading lists added
`deltastar-407-reading-list-{gaussperiods,crossdomain,listdecode}.md` (S1/S2/S3, papers verified to exist).

### Honest bottom line
The reduction is now **machine-checked down to one explicit Prop** (L7) and **one finite-shaped sub-question** (the `r=k/2`-vs-`r=1` window reduction, L5's scope boundary). No closure is claimed — the Prop is the recognized-open BGK/Paley sup-norm wall (`max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log p)`, SOTA `n^{1−o(1)}`, prize β>4 outside every explicit theorem). The bricks are genuine *pieces*; the convergence + the rigidity reduction make the open core sharper than it has ever been.
