## Red-team on the floor: "core is irreducibly `B(μ_n)=o(n)`" is a TRAP — the floor is structured optimality, not a character-sum bound

Reconciling `PrizeEntropyDeltaStar.lean` (ceiling proven, `PrizeFloorStatement` open) with the
25-agent workflow's slogan *"the core is irreducibly `B(μ_n)=o(n)`."* That slogan invites a false
close, and it's worth stating why precisely, because `B(μ_n)=o(n)` is **known**.

**The tempting (wrong) close.** For `n = p^{0.16}` (the prize: `n=2^25`, `q=2^153`), Bourgain–
Glibichuk–Konyagin gives `B(μ_n) = max_{b≠0}|η_b| ≤ n^{1−δ} = o(n)` *unconditionally* — subgroups of
size `> p^ε` always have a power-saving. If the floor were `B=o(n)`, the prize would already be
closed by a 2006 theorem.

**Why it isn't.** I read the exact `PrizeFloorStatement`: `∀ word, list at δ<prizeDeltaStar is ≤ B`.
That is the **worst-case** list bound. Its extremizer is the **structured** antipodal ladder, whose
list is the maximal subset-sum fibre `N_fib(s,r)=C(s/2−r%2,⌊r/2⌋)` — which is `≫` the generic list.
BGK bounds the **generic / average** direction's character sum; it says nothing about the structured
worst case. Concretely, in the Shaw-operator language: `B=o(n)` is a bound on the *gap* (the second
eigenvalue), which controls the **generic stratum** of the floor; but `N_fib` is the **top moment**
`E_{ρn}` of the same operator, and the floor's open content is the *optimality of that top moment*
(no word beats the antipodal fibre) — `shaw_offdiag_moment_le` shows the gap does NOT pin a single
high moment from below, so `o(n)` on the gap cannot bound `N_fib`'s dominance. The gap and the top
moment are different statistics of `𝖲_D`; the floor lives at the top, not the gap.

**Net.** `floor ⟺ BCHKS25 Conj 1.12 ⟺ antipodal-ladder optimality` — a combinatorial extremality, not
a character-sum cancellation. The known `o(n)` closes only the generic stratum; the structured
optimality is the irreducible open core, and any genuine solution must prove *that*, not a `B`-bound.
(Workbench §8b updated with the structured entropy law `δ*=1−ρ−H(ρ)/log₂B`, the proven ceiling, the
open floor, and this trap; `lake env lean` EXIT 0, axiom-clean.)
