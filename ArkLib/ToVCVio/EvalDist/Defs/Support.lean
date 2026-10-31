/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.Monad.Support

/-!
# Compatibility import for VCV-io's `EvalDist.Defs.Support`

The pinned dependency provides `support_bind_exists` and `eq_of_mem_support_pure`.
Existing clients retain this import path without declaring duplicate constants.
-/
