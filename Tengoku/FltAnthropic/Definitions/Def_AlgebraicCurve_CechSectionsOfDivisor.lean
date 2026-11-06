import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Repartitions
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def lSpaceOn (S : Set (Place K F)) (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ v ∈ S, v.adicValuation f ≤ exp (D v)}
  add_mem' := fun {f g} hf hg v hv =>
    (Valuation.map_add _ f g).trans (max_le (hf v hv) (hg v hv))
  zero_mem' := fun v _ => by simp
  smul_mem' := fun c f hf v hv => by
    show v.adicValuation (c • f) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hf v hv)

/--
@isnad1 id=le.1h5v.s7.b89ffd755f65 from=translated src=- shape=c5b56a27 vocab=ba50fe2b
-/
theorem lSpaceOn_anti {S₀ S₁ : Set (Place K F)} (h : S₀ ⊆ S₁) (D : Divisor K F) :
    lSpaceOn S₁ D ≤ lSpaceOn S₀ D := fun _ hf v hv => hf v (h hv)

@[reducible] def cechSections (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    TwoChartCech.Sections (TwoChartCech.Cover.trivial K) :=
  TwoChartCech.Sections.ofSubmodules (lSpaceOn S₀ D) (lSpaceOn S₁ D) (lSpaceOn (S₀ ∩ S₁) D)
    (lSpaceOn_anti Set.inter_subset_left D) (lSpaceOn_anti Set.inter_subset_right D)

abbrev cechDiff (S₀ S₁ : Set (Place K F)) (D : Divisor K F) :
    (lSpaceOn S₀ D × lSpaceOn S₁ D) →ₗ[K] lSpaceOn (S₀ ∩ S₁) D :=
  (cechSections S₀ S₁ D).cechDiff

section ToH1

end ToH1

end AlgebraicCurve

end
