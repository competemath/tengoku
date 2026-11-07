/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/leanprover/cslib@e806c8e639ed, `Cslib/Tactic/GrindAttrs.lean`: removed the registration of the grind set `modal` (it runs code when the module loads). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! # CSLib grind sets

This module registers custom grind sets in CSLib.
-/

@[expose] public section

namespace Cslib.Logic.Modal


end Cslib.Logic.Modal
