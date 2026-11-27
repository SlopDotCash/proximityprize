# Algebraic Stack-Lift Gate for F1 Middle-Slot and Region-Syzygy Witnesses

## Summary and Honesty Classification (`DOSSIER.md` §6)

This note documents the machine-checked algebraic stack-lift gate in
[`CarbonSYZMiddleSlotLiftGate.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonSYZMiddleSlotLiftGate.lean)
and companion verification script
[`probe_carbon_syz_middle_lift_gate.py`](../../../scripts/probes/probe_carbon_syz_middle_lift_gate.py).

Per `DOSSIER.md` §6, the theorems in `CarbonSYZMiddleSlotLiftGate.lean` are **unconditional
structural components and route-obstruction theorems** on the F1 region-to-stack lift gate
(`_SYZ50WitnessRealizability.lean` Question D, `_F1RegionSyzygyInterface.lean`, `SYZ70–SYZ72`):
they prove exact universal algebraic bounds on the in-budget syzygy window and on the `mcaBadCount`
of any 3-core pair-degenerate stack lift over **every** finite field $F$ (requiring no prime-size
heuristic and avoiding all G84/SYZ53 small-field artifacts), while honestly leaving 4-plus-core and
non-pair-degenerate channels outside this 3-core cocycle gate.

## Main Results

### 1. Universal Syndrome-Rank-1 Collapse (`mcaBadCount_le_one_of_collinear_syndrome`)

Let $C \le F^\iota$ be any linear code over a finite field $F$, $\delta \in \mathbb{R}_{\ge 0}$ any
proximity radius, and $(u_0, u_1)$ any two-word stack. If the syndrome cosets
$C.\mathrm{mkQ}(u_0), C.\mathrm{mkQ}(u_1) \in F^\iota / C$ lie in a subspace $M \le F^\iota / C$ of
dimension $\dim_F M \le 1$, then
$$\mathrm{mcaBadCount}(C, \delta, u_0, u_1) \le 1.$$

**Proof:**
- If $u_1 \in C$, then whenever $w \in C$ agrees with $u_0 + \gamma u_1$ on $S$, the codeword pair
  $(w - \gamma u_1, u_1) \in C \times C$ jointly agrees with $(u_0, u_1)$ on $S$, contradicting
  $\neg \mathrm{pairJointAgreesOn}$; hence $\mathrm{mcaBadCount} = 0$
  (`mcaBadCount_eq_zero_of_snd_mem`).
- Otherwise $C.\mathrm{mkQ}(u_1) \ne 0$ spans $M$, so $u_0 + \gamma_0 u_1 \in C$ for a unique scalar
  $\gamma_0 \in F$. For any $\gamma \ne \gamma_0$, if $w \in C$ agrees with $u_0 + \gamma u_1$ on
  $S$, subtracting $c_0 := u_0 + \gamma_0 u_1 \in C$ shows $(\gamma - \gamma_0)^{-1}(w - c_0) \in C$
  agrees with $u_1$ on $S$, and $c_0 - \gamma_0 v_1 \in C$ agrees with $u_0$ on $S$, again
  violating $\neg \mathrm{pairJointAgreesOn}$ (`mcaEvent_eq_of_combo_mem`). Thus at most $\gamma_0$
  can fire `mcaEvent` (`mcaBadCount_le_one_of_finrank_quotient_le_one`).

### 2. Exact In-Budget Syzygy Window Dimension Formula (`finrank_windowKD_bandStack`)

For **every** field $K$ and **every** pairwise-coprime triple $(W_{AB}, W_{AC}, W_{BC})$ of degrees
$(a, b, c)$ satisfying `F1RegionSyzygy.BandStack a b c t k` and
`F1RegionSyzygy.MinimalSyzygyDegree WAB WAC WBC δ₁`, combining `SYZ65.degree_sum_unconditional`
($n_1 + n_2 = a + b + c$, $n_1 \le n_2$) with `SYZ64.finrank_windowKD` proves:

1. The minimal $\mu$-basis generator degree equals $\delta_1$ ($n_1 = \delta_1$,
   $n_2 = a + b + c - \delta_1$).
2. At the SYZ37 $t$-loaded budget $B = k - 1 - t$, G172 interior slack
   $2k + 1 \le a + b + c + 2t \le 2n_2 + 2t$ **always** forces $B + 1 = k - t < n_2$, killing the
   second $\mu$-basis ramp identically.
3. Consequently, the in-budget syzygy window has **exact $K$-dimension**
   $$\dim_K \mathrm{windowKD}_{![a,b,c]}\!\bigl(\ker \mathrm{syzygyMap}(W_{AB}, W_{AC}, W_{BC}),\, k - 1 - t\bigr) = (k - t) - \delta_1.$$
4. Whenever $k - t \le \delta_1$, the in-budget window vanishes and
   `SYZ38.SylvesterInjective WAB WAC WBC (k - 1 - (b + t)) (k - 1 - (c + t))` holds
   unconditionally (`sylvesterInjective_of_budget_le_minSyzygy`).

### 3. Resolution of Both F1 Middle-Band Families on 3-Core Pair-Degenerate Lifts

Let $(\Omega, S_{AB}, S_{AC}, S_{BC}, T)$ be any full-partition ($a + b + c + t = 2k$)
`VennRegions` + `BandStack` + `MinimalSyzygyDegree ... δ₁` witness over a finite field $F$, with
cores $C_A = S_{AB} \cup S_{AC} \cup T$, $C_B = S_{AB} \cup S_{BC} \cup T$, and
$C_C = S_{AC} \cup S_{BC} \cup T$. By `BandStack`, each core has cardinality $\ge k + 2$, so local
degree-$< k$ interpolants $(p_A, p_B, p_C)$ on $(C_A, C_B, C_C)$ are unique. Sending a locally
degree-$< k$ word $w \in \mathrm{ThreeCoreGluedSubmodule} \le F^\Omega$ to its reduced mismatch
cocycle
$$r_{AB} = \frac{p_B - p_A}{V_T W_{AB}}, \qquad
  r_{AC} = \frac{p_A - p_C}{V_T W_{AC}}, \qquad
  r_{BC} = \frac{p_C - p_B}{V_T W_{BC}}$$
descends to an **injective** $F$-linear map from
$(\mathrm{ThreeCoreGluedSubmodule} \bmod \mathrm{RS}[\Omega, k])$ into
$\mathrm{windowKD}_{![a,b,c]}(\ker \mathrm{syzygyMap}, k - 1 - t)$, proving
$$\dim_F \bigl(\mathrm{ThreeCoreGluedSubmodule} \bmod \mathrm{RS}[\Omega, k]\bigr) \le (k - t) - \delta_1.$$

Combining this cocycle bound with Syndrome-Rank-1 Collapse yields two unconditional consequences for
every 3-core pair-degenerate stack $(u_0, u_1)$ (`pairJointAgreesOn` on $C_A, C_B, C_C$):

| Witness family | $(a,b,c,t,k,\delta_1)$ | $(k - t) - \delta_1$ | `SylvesterInjective`? | 3-core stack `mcaBadCount` (all $F$, all $\delta$) |
| :--- | :--- | :---: | :---: | :---: |
| PR #528 / `_F1RegionMiddleCounterexample` ($d \ge 6$, incl. $\mathbb{F}_{23}$) | $(d, d, d, d-2, 2d-1, d+1)$ | $0$ | **Holds** | **`= 0`** (`u₀, u₁ ∈ C`) |
| `SYZ70–SYZ72` first middle slot (incl. `SYZ72` $\mathbb{F}_{41}$ & $\mathbb{F}_{181}$) | $(6, 6, 6, 2, 10, 7)$ | $1$ | Fails (dim $1$) | **`≤ 1`** ($< 19 = 2k - 1$) |
| `SYZ50` Question-C balanced floor witness (incl. $\mathbb{F}_{29}$) | $(4, 4, 4, 2, 7, 4)$ | $1$ | Fails (dim $1$) | **`≤ 1`** ($< 13 = 2k - 1$) |

In particular:
- **`pr528_family_sylvesterInjective` & `pr528_family_threeCore_mcaBadCount_eq_zero`:** Although
  the PR #528 family occupies `SYZ59.middleBand d d d (d + 1)`, its large triple overlap
  $t = d - 2$ pushes the actual budget $B = k - 1 - t = d$ strictly below $\delta_1 = d + 1$, so
  `SylvesterInjective` **holds** across the entire family and every 3-core pair-degenerate stack
  lift is a global codeword pair with $\mathrm{mcaBadCount} = 0$.
- **`middleSlot_666_threeCore_mcaBadCount_le_one` & `zmod41_middleSlot_no_overBudget_threeCore_lift`:**
  Every $(6, 6, 6, 2, 10, 7)$ witness over **every** finite field $F$ (specialized to
  `SYZ72.zmod41_regionSyzygyRealizable`) has window dimension $(10 - 2) - 7 = 1$, forcing collinear
  syndromes and $\mathrm{mcaBadCount} \le 1$ at every radius $\delta$. Hence **no** $(6,6,6,2,10,7)$
  middle-slot witness can lift to a multi-scalar ($\ge 2$) or over-budget ($> 19$) 3-core
  pair-degenerate MCA stack; achieving $\mathrm{mcaBadCount} \ge 2$ on a 3-core full-partition lift
  algebraically requires the strict window-slack gate $(k - t) - \delta_1 \ge 2$
  (`threeCore_multiScalar_requires_window_slack_two`).
