/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Cech.Colimit
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.Gluing
public import Tengoku

/-!
# Forster 12.4: refinement maps are injective on `H¹` (CC8, D8, proof plan §6.7)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.4, §6.7).

* `resH1_injective`: `resH1 D τ hτ : H1Cover D 𝒰 →ₗ H1Cover D 𝒱` is injective — a pure
  sheaf-axiom argument (`MeroGermOn.exists_glue`/`glue_unique`), no analysis.
* `toH1_injective`/`toH1_eq_zero_iff`: every cover-level `H¹` embeds in the colimit `H1 D`
  (via `Module.DirectLimit.of.zero_exact` + `resH1_injective`).
* `subsingleton_H1_iff`: the colimit vanishes iff every cover-level `H¹` vanishes.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X) {Ω : Opens X} {𝒰 𝒱 : FinCover Ω}
variable (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ)

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Any member `A ≤ Ω` is exhausted by its intersections with the members of a cover `𝒱` of `Ω`
(§6.7's covering fact, used both to glue `injPatch` over `𝒰.U i` and to compare cochains over
`𝒰.U i ⊓ 𝒰.U j`). -/
theorem iUnion_inf_eq (A : Opens X) (hA : A ≤ Ω) :
    (⋃ k : Fin 𝒱.n, ((A ⊓ 𝒱.U k : Opens X) : Set X)) = (A : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun k => inf_le_left
  · intro x hx
    obtain ⟨k, hk⟩ := 𝒱.covers x (hA hx)
    exact Set.mem_iUnion.2 ⟨k, hx, hk⟩

/-- The local candidate for the glued section on `𝒰.U i`, restricted to `𝒰.U i ⊓ 𝒱.U k`
(Forster p. 99 / §6.7). -/
noncomputable def injPatch (f : C1 D 𝒰) (g : C0 D 𝒱) (i : Fin 𝒰.n) (k : Fin 𝒱.n) :
    RS.LinSysOn D ((𝒰.U i ⊓ 𝒱.U k : Opens X) : Set X) :=
  LinSysOn.restrictL D (inf_le_inf (le_refl (𝒰.U i)) (hτ k)) (f (i, τ k)) -
    LinSysOn.restrictL D (inf_le_right : 𝒰.U i ⊓ 𝒱.U k ≤ 𝒱.U k) (g k)

end RS.Cech
