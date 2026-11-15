import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CanonicalDivisor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

/--
@isnad1 id=ex.0h3v.s8.ea0c1fef57d3 from=translated src=- shape=b43fe5ce vocab=0bbe6479
-/
theorem exists_ord_eq_one_and_dCoord_eq (v : Place K F) :
    ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

end Place

def regularDifferentials : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord}
  zero_mem' v := ⟨0, v.toValuationSubring.zero_mem, by rw [zero_smul]⟩
  add_mem' {ω η} hω hη v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    obtain ⟨g, hg, hη'⟩ := hη v
    exact ⟨f + g, v.toValuationSubring.add_mem _ _ hf hg, by rw [hη', add_smul]⟩
  smul_mem' c {ω} hω v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    refine ⟨algebraMap K F c * f, v.toValuationSubring.mul_mem _ _ (v.algebraMap_mem' c) hf, ?_⟩
    rw [mul_smul, algebraMap_smul]

variable {K F} in
/--
@isnad1 id=iff.0h3v.s8.4ba15ece1163 from=translated src=- shape=75b47f9c vocab=21ad89e9
-/
theorem mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ regularDifferentials K F ↔
      ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord :=
  Iff.rfl

end AlgebraicCurve

end
