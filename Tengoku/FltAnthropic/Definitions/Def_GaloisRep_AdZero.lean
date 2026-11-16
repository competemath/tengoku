import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Residual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ResidualGaloisRep

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable def adRep (ρbar : ResidualGaloisRep k) : Representation k Γℚ (Module.End k ρbar.V) where
  toFun σ := LinearMap.mulLeft k (ρbar.ρ σ) ∘ₗ LinearMap.mulRight k (ρbar.ρ σ⁻¹)
  map_one' := by
    ext f
    simp
  map_mul' σ τ := by
    ext f
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      Module.End.mul_apply, mul_inv_rev, map_mul, mul_assoc]

/--
@isnad1 id=eq.0h4v.s12.a08af67c8f84 from=translated src=- shape=dfdca13a vocab=8fe01f31
-/
@[simp]
theorem adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    ρbar.adRep σ f = ρbar.ρ σ * f * ρbar.ρ σ⁻¹ := rfl

/--
@isnad1 id=eq.0h4v.s12.72d051c21552 from=translated src=- shape=f34550ae vocab=774b7cf9
-/
theorem trace_adRep_apply (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : Module.End k ρbar.V) :
    LinearMap.trace k ρbar.V (ρbar.adRep σ f) = LinearMap.trace k ρbar.V f := by
  rw [adRep_apply, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/--
@isnad1 id=le.0h3v.s12.f99945651167 from=translated src=- shape=224f1068 vocab=57b29b44
-/
theorem ker_trace_le_comap_adRep (ρbar : ResidualGaloisRep k) (σ : Γℚ) :
    LinearMap.ker (LinearMap.trace k ρbar.V) ≤ (LinearMap.ker (LinearMap.trace k ρbar.V)).comap (ρbar.adRep σ) := by
  intro f hf
  simp only [Submodule.mem_comap, LinearMap.mem_ker] at hf ⊢
  rw [trace_adRep_apply, hf]

noncomputable def adZeroRep (ρbar : ResidualGaloisRep k) :
    Representation k Γℚ (LinearMap.ker (LinearMap.trace k ρbar.V)) :=
  ρbar.adRep.subrepresentation _ ρbar.ker_trace_le_comap_adRep

noncomputable abbrev adZero (ρbar : ResidualGaloisRep k) : Rep k Γℚ :=
  Rep.of ρbar.adZeroRep

/--
@isnad1 id=eq.0h4v.s15.a84b58d7b0d1 from=translated src=- shape=7af7da25 vocab=bc6dd78c
-/
@[simp]
theorem adZeroRep_apply_coe (ρbar : ResidualGaloisRep k) (σ : Γℚ) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    ((ρbar.adZeroRep σ f : LinearMap.ker (LinearMap.trace k ρbar.V)) : Module.End k ρbar.V)
      = ρbar.ρ σ * (f : Module.End k ρbar.V) * ρbar.ρ σ⁻¹ :=
  rfl

def adZeroFil (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) :
    Submodule k (LinearMap.ker (LinearMap.trace k ρbar.V)) where
  carrier := {f | (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0}
  zero_mem' := ⟨fun _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.add_mem (hf1 v) (hg1 v)
    · simp [hf2 v hv, hg2 v hv]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · simpa using L.smul_mem c (hf1 v)
    · simp [hf2 v hv]

/--
@isnad1 id=iff.0h4v.s13.b644d3384403 from=translated src=- shape=9d732982 vocab=c9331459
-/
theorem mem_adZeroFil_iff (ρbar : ResidualGaloisRep k) (L : Submodule k ρbar.V) (f : LinearMap.ker (LinearMap.trace k ρbar.V)) :
    f ∈ ρbar.adZeroFil L ↔ (∀ v, (f : Module.End k ρbar.V) v ∈ L) ∧ ∀ v ∈ L, (f : Module.End k ρbar.V) v = 0 :=
  Iff.rfl

end ResidualGaloisRep
