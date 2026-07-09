#!/usr/bin/env python3
"""Merge _frag*.json, rank, select top 100, emit JSON sidecar + Markdown master."""
import json, os, glob

ROOT = r"C:\Users\Administrator\arklib"
CONNDIR = os.path.join(ROOT, "scripts", "probes", "_407_conn")
MD = os.path.join(ROOT, "ArkLib", "Data", "CodingTheory", "ProximityGap",
                  "RESEARCH_SYNTHESIS_407_CONNECTIONS.md")
JSON_OUT = os.path.join(CONNDIR, "connections_100.json")

# Paths confirmed MISSING by Glob — strip from any code_files list.
MISSING = {
    "ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumRawMoment.lean",
    "ArkLib/Data/CodingTheory/ProximityGap/RootSumNormBound.lean",
}

items = []
for fp in sorted(glob.glob(os.path.join(CONNDIR, "_frag*.json")),
                 key=lambda p: int(os.path.basename(p)[5:-5])):
    with open(fp, encoding="utf-8") as f:
        items.extend(json.load(f))

# Re-grade filter: keep only >=7 on all three axes.
kept = [c for c in items
        if c["scores"]["insight"] >= 7
        and c["scores"]["research"] >= 7
        and c["scores"]["relevance"] >= 7]
dropped = len(items) - len(kept)

# Strip missing code files; normalize.
for c in kept:
    c["code_files"] = [p.replace("\\", "/") for p in c.get("code_files", [])]
    c["code_files"] = [p for p in c["code_files"] if p not in MISSING]

def total(c): return sum(c["scores"].values())

# Rank: total desc, then relevance, then insight.
kept.sort(key=lambda c: (-total(c), -c["scores"]["relevance"], -c["scores"]["insight"]))

# Dedup guard: drop exact-title duplicates if any slipped in.
seen, uniq = set(), []
for c in kept:
    key = c["title"].strip().lower()[:60]
    if key in seen:
        continue
    seen.add(key); uniq.append(c)
kept = uniq

top = kept[:100]
shortfall = max(0, 100 - len(top))

# Assign id + rank.
out = []
for i, c in enumerate(top, start=1):
    out.append(dict(
        id=f"C{i:03d}", rank=i, total=total(c),
        scores=c["scores"], multiform=bool(c["multiform"]),
        forms=c["forms"], walls=c["walls"], code_files=c["code_files"],
        title=c["title"], connection=c["connection"],
        why_insightful=c["why_insightful"], attack_plan=c["attack_plan"]))

with open(JSON_OUT, "w", encoding="utf-8") as f:
    json.dump(out, f, ensure_ascii=False, indent=1)

# Histogram of totals.
hist = {}
for c in out:
    hist[c["total"]] = hist.get(c["total"], 0) + 1

# ---- Markdown ----
FORMS = {
 "F1":"δ* = sup{δ : I(δ) ≤ q·ε* ≈ n} (the prize threshold / governing law)",
 "F2":"M(n) = max worst incomplete char sum (Gauss-period sup-norm), target ≲ C√(n·log(p/n))",
 "F3":"I(δ) = max far-line incidence = #bad scalars (γ : u0+γu1 δ-close to RS[k])",
 "F4":"sub-Johnson list size of RS[k+1] / SuperCodeListBridge (list-decoding grand challenge)",
 "F5":"E_r(μ_n) additive energy / deep moments / cumulant κ_r sub-Wick",
 "F6":"T_h tangent sum = (1/m)Σ_i J(χ^i,χ^h) average of Jacobi sums",
 "F7":"Gauss-period family {η_i} decorrelation / joint sub-Gaussian variance n",
 "F8":"2-adic descent / parallelogram tower M(n)²≤2M(n/2)² ; cocycle ∏r_j, r_j∈[√2,2]",
 "F9":"Action-orbit count K (Chai-Fan): bad-α = union of ⟨g^{b-a}⟩-orbits",
 "F10":"Half-Sum Lemma / DyadicLacunaryFloor: #lacBad coset-quantized in units n/gcd(t,n)",
 "F11":"cross-parity leak A≡−g·B mod q / fully-split N(𝔮)=q ideal-SVP (Pan-Xu open split case)",
 "F12":"e₂=0 algebraic rigidity / char-p resultant threshold c≈n³ (no BGK wall)",
 "F13":"Bessel even-moment law E_r=(2r)![x^r]I₀(2√x)^{n/2}; odd-moment Ση^{2k+1}=−n^{2k}",
 "F14":"sparse-support cyclic code list size (BCH/Hartmann-Tzeng/Roos)",
 "F15":"Schur / complete-homogeneous vanishing: bad ⟺ ∃(k+1)-subset with h_{b-k}(x_S)=0",
 "F16":"N₀(G,r) additive relation count = Σ_b η_b^r/q ; Salem-Zygmund flatness",
 "F17":"NVM / Chebotarev nonvanishing-minors of the compressed Fourier matrix of μ_n",
 "F18":"autocorrelation flatness: max Fourier coeff of r(h)=|μ_n∩(μ_n+h)| ≤ n·log(p/n)",
 "F19":"effective Katz/Rojas-León equidistribution of the coset Gauss-sum family (GL(1)^f monodromy)",
 "F20":"constant-index √-cancellation lane (QR index-2; ‖η_b‖≤((m−1)√q+1)/m) and where it stops",
}
WALLS = {
 "W-BGK":"thin-subgroup √-cancellation / Paley graph conjecture (SOTA n^{0.989}, need n^{0.5})",
 "W-Johnson":"L² ceiling / n^{1/2} energy deficit ((pE_r)^{1/2r}≥n)",
 "W-anomaly":"deep-moment char-p anomaly forced positive once qE_r^{char0}<n^{2r}, crossover r*≈β+1",
 "W-Betti":"AG/Deligne Betti/conductor growth caps moment route at r=2",
 "W-subspace":"BCDZ25 subspace-design quality vacuous at s=1 (plain RS) ⟹ folding necessary",
 "W-idealSVP":"Pan-Xu: cyclotomic ideal-SVP poly only for non-split q; fully-split N(𝔮)=q open",
 "W-Mersenne":"BCHKS Conj 1.12 subgroup-sumset lower bound / '2^p−1 has a large prime factor'",
 "W-genericity":"HOMDS/GM-MDS generic vs the FIXED measure-zero μ_n (negation saturates Singleton)",
 "W-largesieve":"effective Deligne needs family dim f=(p−1)/n ≤ √q ⟺ n≥√p, but prize n≪√p",
 "W-LamLeung":"structure of W_p(m) in char p left explicitly open by Lam-Leung",
}

def esc(s): return s.replace("|", "\\|")

lines = []
lines.append("# Proximity-Gap Grand Prize (#407): 100 Ranked δ* Connections\n")
lines.append(
 "This is the master synthesis of **insightful cross-form connections** for the ArkLib "
 "Proximity-Gap Grand Prize (GitHub issue #407 — explicit-RS list-decoding beyond Johnson on a "
 "dyadic FFT subgroup μ_n, n=2^μ ⊊ F_q*, q=n^β with β≈4–5, conjectured pin "
 "δ*=1−ρ−H(ρ)/(β·log₂ n)). It pools **157 candidate connections mined by 24 lens agents**, "
 "deduplicated/merged to corroborated items, re-graded, and ranked by total score "
 "(insight+research+relevance) — the **top 100** are kept here. Each connection is a "
 "non-obvious structural link bridging ≥2 of the forms F1–F20, linking two walls, wiring "
 "in-tree code to an open form, or exposing a hidden symmetry. **Honesty contract:** these are "
 "CANDIDATE connections + attack plans, NOT proofs. Nothing here claims closure; every entry "
 "labels its open residual. Cited Lean files were Glob-verified to exist on this branch "
 "(`claude/113-append-completeness-keystone`); two prose-only paths "
 "(`SubgroupGaussSumRawMoment.lean`, `RootSumNormBound.lean`) were dropped as unverifiable.\n")

lines.append("## Legend\n")
lines.append("**Forms (irreducible δ*-quantities, all the same wall seen many ways):**\n")
for k, v in FORMS.items():
    lines.append(f"- **{k}** — {v}")
lines.append("\n**Walls:**\n")
for k, v in WALLS.items():
    lines.append(f"- **{k}** — {v}")
lines.append("")

lines.append("## Ranked table\n")
lines.append("| rank | id | total | I/R/Rel | multiform | forms | title |")
lines.append("|---:|---|---:|---|:---:|---|---|")
for c in out:
    s = c["scores"]
    mf = "yes" if c["multiform"] else "no"
    forms = " ".join(c["forms"])
    lines.append(
      f"| {c['rank']} | {c['id']} | {c['total']} | "
      f"{s['insight']}/{s['research']}/{s['relevance']} | {mf} | {forms} | {esc(c['title'])} |")
lines.append("")

lines.append("## Connections (rank order)\n")
for c in out:
    s = c["scores"]
    mf = "yes" if c["multiform"] else "no"
    lines.append(
      f"### {c['id']} — {c['title']}   "
      f"[total {c['total']} | insight {s['insight']} research {s['research']} "
      f"relevance {s['relevance']} | multiform {mf}]\n")
    lines.append(f"**Forms:** {', '.join(c['forms'])}  ")
    lines.append(f"**Walls:** {', '.join(c['walls']) if c['walls'] else '(none)'}  ")
    code = ", ".join(f"`{p}`" for p in c["code_files"]) if c["code_files"] else "(none verified)"
    lines.append(f"**Code:** {code}\n")
    lines.append(f"**Connection:** {c['connection']}\n")
    lines.append(f"**Why insightful:** {c['why_insightful']}\n")
    lines.append(f"**Attack:** {c['attack_plan']}\n")
    lines.append("**Verdict:** _pending_\n")

with open(MD, "w", encoding="utf-8") as f:
    f.write("\n".join(lines))

print(f"pooled_input={len(items)}")
print(f"after_filter(>=7 all)={len(kept)}  dropped_below_7={dropped}")
print(f"written={len(out)}  shortfall={shortfall}")
print(f"hist_total={dict(sorted(hist.items(), reverse=True))}")
print(f"md={MD}")
print(f"json={JSON_OUT}")
