## LANDED: exact δ* at the boundary-row codes (`mcaDeltaStar_eq_boundary`, in `CosetCliqueBoundary.lean`, `7b4e74b61`) + the consolidated closing-readiness audit

**The pin:** for `b ∣ n`, `b ≤ 4`, `k = n − 2b + 2`, every `ε* ∈ [(b−1)/q, n/q)`:
> **δ*(RS[F, μ_n, k], ε*) = (b−1)/n** — good below by the master collapse at bands 1..b−1 (the b ≤ 4 condition is exactly where the collapse hypothesis 3(b−2)+k ≤ n clears at the boundary dimension), bad at the edge by the clique certificate (n/q). At b = 3 the pinned band `[2/q, n/q)` spans **n − 2 granularity steps** — the widest exactly-pinned ε*-window in the tree, and a proof that the staircase at these codes jumps from 2/q **directly to ≥ n/q** with no intermediate steps. Plus `mcaDeltaStar_le_of_undersized_boundary`: the δ* cap family at every divisor radius whenever ε* < n/q.

---

### The closing-readiness audit (per the standing directive — where the issue actually stands)

Having tracked all ~210 comments through today, the honest closure inventory is:

**Fully proven, nothing left to do:** the sub-Johnson staircase (three regimes, both sides where sup-side theorems exist); the granularity-ladder and boundary-row closed-form δ*; the strip-edge pins; the census architecture (4 circuit families closed-form at all 2-power scales, char-0 ↔ mod-p transfers above explicit thresholds, the towers); the LD⇔MCA dictionary both directions; the equivariance/syndrome/step-function assembly frames; interleaving exactness; the fold tower.

**Provable with current mathematics (active or claimable):**
1. Johnson-with-no-Props — down to ONE statement (V1 successor orders, `Λ(α_t) ≤ 1` monic; E1′ a–d landed today). When it lands, the Johnson floor becomes fully in-tree and the unconditional bracket becomes `1−√ρ − o(1) ≤ δ* ≤ KKH26 rows`.
2. The slanted exactness converse (matching frame is kernel-decidable per scale).
3. `MonomialBoundaryBound` (my surface): finite kernel route documented (coreJ device × 28 live pairs), deliberately not run — pure compute.
4. Sub-Johnson sup-exactness (are n/(b−1) and n the exact strip/boundary values?): the incidence-capacity question — bounded, new-but-plausible mathematics.

**Blocked on genuinely new mathematics (the irreducible cores — the issue cannot close until one of these falls):**
- **The window's sup side** (census-band extremality): equivalent via the in-tree CS25 coupling to beyond-Johnson list decoding of explicit RS codes — the 25-year wall. Every campaign reduction (deviation-sup split, census crossing, collision matroid, monomial-then-v4 domination) terminates here.
- **The window's floor side past Johnson**: same wall, other face.
- `TZPrimeSupply` (s ≥ 128 ceiling rows): deep analytic number theory, correctly quarantined.
- The remaining paper-interface residuals (`CapacityBoundsProofs`, GKL24 covers, CS25 inputs): each a standalone porting project, none δ*-decisive.

**Verdict:** an *unconditional exact pin of δ\* in the open window is not achievable by any amount of in-session work* — it requires solving a problem the literature has held open for 25 years, and the tracker's own acceptance criteria (its §1 coupling paragraph) say so. What "100% done" can honestly mean — every value determinable with current mathematics determined, every conjectural surface either proven, refuted, or named-and-priced — is now within sight: items 1–4 above are the complete remaining list outside the walls. The campaign's structural contribution stands: δ* is machine-checked exactly on every regime below Johnson, bracketed with named certificates inside the window, and the open core is isolated behind verified interfaces such that any future mathematical breakthrough lands as a one-lemma instantiation.

