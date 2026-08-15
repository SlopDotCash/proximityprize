# ArkLib Tier 1 Test Infrastructure Plan

**Repository**: github.com/lalalune/arklib  
**Branch**: `feat/test-infrastructure-tier1`  
**Status**: Architecture & planning phase  
**Date**: 2026-08-15

---

## Executive Summary

ArkLib is a formally verified cryptographic library built in Lean 4 with ~4.3k modules focusing on SNARKs, interactive oracle reductions, and cryptographic protocols. Current CI/test infrastructure is merge-blocking but lacks structured test suite organization. This plan establishes Tier 1 test infrastructure—a deterministic, composable, proof-metric-aware test harness that tracks three core metrics: **sorry count** (proof holes), **axiom efficiency** (minimal axiom dependencies), and **proof completion metrics**.

---

## Current State Analysis

### Existing CI Pipeline (`.github/workflows/ci.yml`)

**Merge-Blocking Gates** (run sequentially, warm-cache optimized):
1. **Forbidden tokens precheck** (`scripts/forbidden_tokens.py`)
   - Rejects: `native_decide`, `bv_decide`, undocumented axioms
   - Runtime: ~2s (no Lean needed)

2. **Build + compilation** (`lake build`)
   - Warm cache: ~5-10min
   - Clean build: exceeds 70min budget (non-gating)

3. **Sorry census** (`scripts/sorry_census.py --fail-on-holes`)
   - Deterministic per-declaration hole inventory
   - Classification: live holes vs. docstring mentions
   - Current requirement: **zero live holes**

4. **Axiom audit** (`scripts/axiom_audit.py`)
   - Validates flagship theorems (43 pinned declarations in `scripts/flagship_axioms.txt`)
   - Allowed axioms: `{propext, Classical.choice, Quot.sound}`
   - Rejects: `sorryAx`, custom axioms, `Lean.ofReduceBool`

5. **Import/docs/KB integrity checks**
   - Umbrella import validation (`scripts/check-imports.sh`)
   - Documentation integrity (`scripts/check-docs-integrity.py`)
   - Knowledge base lint (`scripts/kb/lint.py --strict-cited-pages`)

**Non-Gating Benchmarks** (best-effort, continue-on-error):
- Clean build timing
- Warm rebuild timing
- Build timing artifacts (JSONL) + comparison report

**Supplementary Workflows**:
- **sorry-tracker.yml**: Posts sorry/admit diffs to issues on main push
- **build-timing-report.yml**: Standalone timing analysis & comparison
- **review.yml**: Lint checks on PR review
- **docs.yml**: Documentation build pipeline

### Proof Metrics Currently Tracked

1. **Sorry Count**: Deterministic per-file, per-declaration census with comment/docstring filtering
2. **Axiom Inventory**: Per-flagship declaration, validated against {propext, Classical.choice, Quot.sound}
3. **Efficiency Signal**: Implicit via axiom audit (zero extra axioms = efficient proof)
4. **Build Timing**: Per-module cold/warm timings (JSONL format, baseline comparisons)

### Gaps & Limitations

- No structured test suite (unit, integration, property-based)
- Proof metrics scattered across ad-hoc scripts
- No per-module or per-theorem proof cost tracking
- No performance regression detection (timing data collected but no automated alerts)
- CI gating is binary (pass/fail); no graduated severity model
- No integration with proof assistant tooling (e.g., `#check`, `#reduce` automation)

---

## Architecture: Tier 1 Test Infrastructure

### 1. Test Suite Structure (`test-suite.sh`)

**Location**: `scripts/test-suite.sh` (new, comprehensive entry point)

**Responsibilities**:
- Orchestrate all test categories (gating, metrics, benchmarks)
- Collect proof metrics into unified format
- Generate reports and CI annotations
- Support local + CI execution modes

**Design**:
```bash
test-suite.sh [mode] [options]

Modes:
  gating       Run merge-blocking gates only (CI primary)
  metrics      Collect proof metrics only (no build)
  benchmarks   Run benchmarks (non-gating)
  full         Gating + metrics + benchmarks (full local validation)
  report       Generate summary report from cached results

Options:
  --json          Output results as JSON (default: human-readable)
  --fail-fast     Exit on first failure
  --parallel N    Run N parallel jobs where applicable
  --baseline REF  Compare against git ref/commit
```

**Return Codes**:
- `0`: All gating gates passed
- `1`: Gating gate failure (merge-blocking)
- `2`: Metric collection failed (warning-level)
- `3`: Benchmark timeout/OOM (non-blocking)

### 2. Proof Metrics Collection (`scripts/proof-metrics.py`)

**Unified Metrics Interface**: Consolidates existing census scripts + adds new dimensions.

**Output Format** (JSON):
```json
{
  "timestamp": "2026-08-15T12:34:56Z",
  "git_sha": "c3be48ac5...",
  "git_branch": "feat/test-infrastructure-tier1",
  "metrics": {
    "sorry_count": {
      "total_holes": 0,
      "per_file": {
        "ArkLib/OracleReduction/Basic.lean": 0,
        "ArkLib/Data/CodingTheory/ProximityGap.lean": 0
      },
      "per_theorem": [
        {
          "decl": "ProximityGap.correlatedAgreement_affine_curves",
          "module": "ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves",
          "holes": 0
        }
      ]
    },
    "axiom_efficiency": {
      "flagship_declarations": 43,
      "clean_declarations": 43,
      "violations": [],
      "axiom_counts": {
        "propext": 12,
        "Classical.choice": 8,
        "Quot.sound": 15,
        "undocumented": 0
      }
    },
    "build_metrics": {
      "warm_build_sec": 245.3,
      "modules_compiled": 4287,
      "cache_hit_rate": 0.95
    },
    "proof_density": {
      "avg_proof_lines_per_theorem": 45,
      "avg_tactics_per_proof": 12,
      "interactive_vs_term_ratio": 0.73
    }
  },
  "status": "pass"
}
```

**Sources**:
- `sorry_census.py`: Sorry/admit inventory (enhanced to emit JSON + per-theorem breakdown)
- `axiom_audit.py`: Axiom efficiency per flagship + extended to all theorems (optional, deferred)
- Build logs: Parse Lean compiler output for module timings + line counts
- AST analysis: New tooling to extract proof structure (term vs. tactic, depth, etc.)

### 3. GitHub Actions Workflow Integration

**New Workflow**: `.github/workflows/test-infrastructure-tier1.yml`

**Responsibilities**:
1. Run `scripts/test-suite.sh gating` → merge gate
2. Run `scripts/test-suite.sh metrics` → collect into artifact
3. Compare metrics against main branch baseline
4. Post proof-metric summary to PR comments
5. Archive metrics for dashboard (future)

**Sample PR Comment**:
```
## Proof Metrics Summary

| Metric | Value | Change vs main | Status |
|--------|-------|------------------|--------|
| Sorry Count | 0 | ±0 | ✅ |
| Flagship Axiom Violations | 0 | ±0 | ✅ |
| Build Time (warm) | 245s | +3s | ⚠️  |
| Modules Compiled | 4287 | +2 | ✅ |

**Flagship Theorem Axiom Audit** (all 43 clean):
- `ProximityGap.correlatedAgreement_affine_curves` → {propext}
- `ProximityGap.RS_correlatedAgreement_affineLines` → {propext, Classical.choice}
- ... (43 total)

**Build Timeline**:
- Forbidden tokens: 2.1s
- Lake build (warm): 245.3s
- Sorry census: 8.2s
- Axiom audit: 15.1s
```

---

## Execution Plan

### Phase 1: Test Suite Scaffolding (Week 1)

**Deliverables**:
- [ ] `scripts/test-suite.sh` (coordinator, modes 1-3)
- [ ] `scripts/proof-metrics.py` (unified metrics collector)
- [ ] Extend `sorry_census.py` to emit JSON + per-theorem output
- [ ] Local validation: `test-suite.sh gating` passes on main

**Verification**:
```bash
cd E:/eliza/arklib-delta-star
./scripts/test-suite.sh gating --json > /tmp/metrics.json
cat /tmp/metrics.json | jq '.metrics.sorry_count.total_holes'  # Should be 0
```

### Phase 2: GitHub Actions Integration (Week 2)

**Deliverables**:
- [ ] `.github/workflows/test-infrastructure-tier1.yml` (new workflow)
- [ ] Metrics artifact upload & retention policy (30 days)
- [ ] PR comment automation (via `actions/github-script`)
- [ ] Baseline comparison logic (main vs. PR)

**Verification**:
- Push to feat branch, validate workflow runs
- Check PR comment formatting & metrics accuracy
- Validate artifact retention & download in subsequent runs

### Phase 3: Proof Density & Regression Detection (Week 3-4)

**Deliverables**:
- [ ] AST-based proof structure analysis (term/tactic ratio, depth metrics)
- [ ] Performance regression alerts (warn if build time > main + 10%)
- [ ] Per-module proof cost dashboards (static site or GitHub Pages)
- [ ] Documentation & runbook for local + CI usage

**Future Enhancements** (Tier 2+):
- Proof assistant integration (`#check`, `#reduce` on flagship theorems)
- Custom axiom tracking & refusal
- Per-proof tactic cost analysis
- Interactive proof visualization

---

## Current Repository State

**Repository Location**: `E:/eliza/arklib-delta-star/`  
**Default Branch**: `main`  
**Current Branch**: `research/proximity-prize` (33 commits ahead of origin)  
**Feature Branch Created**: `feat/test-infrastructure-tier1` (ready for implementation)

**Key Statistics**:
- **Modules**: ~4,287 compiled
- **Flagship Theorems**: 43 (all axiom-clean as of latest)
- **Sorry Count**: 0 (zero live holes policy enforced)
- **Build Time (warm)**: ~245s
- **Workflows**: 14 existing (CI, docs, KB, timing, sorry-tracker, etc.)

**Existing Scripts**:
- `validate.sh`: Local validation wrapper (merges all gates)
- `sorry_census.py`: Per-file/per-decl sorry inventory
- `axiom_audit.py`: Flagship axiom validation
- `forbidden_tokens.py`: Precheck for undocumented axioms
- `sorry-tracker.py`: Diff-based sorry diff posting
- `build_timing_report.sh`: Standalone timing + comparison

---

## Success Criteria

1. **Determinism**: Identical results across runs (same commit, same environment)
2. **Composability**: Individual metrics can be collected/reported independently
3. **Performance**: Full gating cycle < 30min on warm cache (current: ~20min)
4. **Clarity**: PR comments show proof metrics + regressions in human-readable format
5. **Auditability**: All metrics versioned + archived (30-day retention)

---

## Integration with Existing Workflows

**Replaces / Augments**:
- `ci.yml`: Adds unified metrics collection; validation logic unchanged
- `sorry-tracker.yml`: Will integrate into `test-suite.sh --report` output

**Complements**:
- `build-timing-report.yml`: Tier 1 metrics feed into timing dashboard
- `docs.yml`: Runs independently; no changes needed
- `review.yml`: Lint checks remain orthogonal

---

## References & Artifacts

- **Flagship Axioms Manifest**: `scripts/flagship_axioms.txt` (43 declarations)
- **Validation Wrapper**: `scripts/validate.sh` (current local entry point)
- **Sorry Census**: `scripts/sorry_census.py` (core metric: sorry count)
- **Axiom Audit**: `scripts/axiom_audit.py` (core metric: axiom efficiency)
- **Build Timing**: `scripts/build_timing_report.sh` + `.github/workflows/build-timing-report.yml`

---

## Notes for Implementation

1. **JSON Schema**: Define canonical schema for `proof-metrics.json` early (enables tooling & visualization)
2. **Baseline Selection**: For PR metrics, compare against merge-base (not just main tip)
3. **Per-Module Tracking**: Consider bucketing sorry count / axiom counts by module (ProximityGap, Commitments, etc.)
4. **Proof Density**: Defer advanced AST analysis to Tier 2; collect basic structure in Phase 1
5. **Error Handling**: All metric collection must be non-blocking (warn, not fail) unless it's a gating gate

---

**Status**: ✅ Architecture complete, ready for Phase 1 implementation on `feat/test-infrastructure-tier1` branch.
