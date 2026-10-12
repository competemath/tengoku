/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.Kurosh.KuroshPathInjective

/-!
# Kurosh Path Endpoint

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshPathEndpointDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α
universe u v
namespace GraphCoveringTheory.Kurosh

end GraphCoveringTheory.Kurosh
