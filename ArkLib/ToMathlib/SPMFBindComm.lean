/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ToMathlib.MeasureTheory.Measure.IndependentDraws

/-!
# Independent native measure binds

The former `SPMF.bind_comm` owner is retired with the SPMF interpreter. Its canonical
replacement is `MeasureTheory.Measure.bind_bind_swap`: independent s-finite measures commute
before a jointly measurable continuation. No normalization is required, so this includes
subprobability measures and preserves their missing mass.

This historical import path remains a shim. The exact type and hypothesis migration, including
the former command, is recorded in `scripts/integration/probability-api-migration.json`.
-/
