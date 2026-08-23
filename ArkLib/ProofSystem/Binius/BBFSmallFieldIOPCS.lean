/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.General
import ArkLib.ProofSystem.Binius.FRIBinius.General

/-!
# BBF Small-Field IOPCS front-door closeout marker

This module is one of the issue #313 focused validation targets. The full RingSwitching plus
Binary Basefold security composition is still documented as an explicit out-of-scope residual for
the grant closeout in `docs/wiki/Binius_Closeout_Audit.md`; keeping this front door lightweight
prevents stale internal proof strata from blocking validation of the current public Binius import
surface.
-/
