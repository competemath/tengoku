/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Tengoku
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Algebra.Module.Equiv.Basic
public import Tengoku.MeanFourier.MeanFourier.Mathlib.Topology.Algebra.Module.Equiv

public section namespace Tengoku.MeanFourier end Tengoku.MeanFourier open Tengoku.MeanFourier
attribute [local simp] ContinuousLinearEquiv.toLinearEquiv_one LinearEquiv.toLinearMap_one


variable {𝕜 G E : Type*}

section RCLike
variable [RCLike 𝕜] [Group G] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜 G E) in
abbrev _root_.Tengoku.MeanFourier.UnitaryRepresentation : Type _ := G →* E ≃ₗᵢ[𝕜] E

namespace Tengoku.MeanFourier.UnitaryRepresentation

variable (𝕜 G E) in
abbrev trivial : UnitaryRepresentation 𝕜 G E := 1

end Tengoku.MeanFourier.UnitaryRepresentation
end RCLike

section Complex
variable [CommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {ρ : UnitaryRepresentation ℂ G E}

namespace Tengoku.MeanFourier.UnitaryRepresentation

end Tengoku.MeanFourier.UnitaryRepresentation
end Complex
-- Tengoku: root names of this library moved to Tengoku.MeanFourier so they do not collide with other libraries (generated)
