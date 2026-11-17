import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_ordinaryCondition_of_isEquiv.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/--
@isnad1 id=eq.0h5v.s11.01e149ca589b from=translated src=- shape=8f7d7cb5 vocab=911d72c2
-/
theorem Equiv.conj_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e.map_apply, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h5v.s11.d9b62092f9ff from=translated src=- shape=ee3d17eb vocab=e7930d07
-/
theorem Equiv.det_apply_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (ρ₂.ρ σ) = LinearMap.det (ρ₁.ρ σ) := by
  rw [Equiv.conj_eq e σ, LinearMap.det_conj]

/--
@isnad1 id=detiscyc.2h4v.s5.88364e49f296 from=translated src=- shape=fadfb841 vocab=9eee625c
-/
theorem detIsCyclotomic_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.DetIsCyclotomic p) : ρ₂.DetIsCyclotomic p := by
  obtain ⟨e⟩ := e
  refine ⟨h.1, fun n σ a hσ => ?_⟩
  rw [Equiv.det_apply_eq e σ]
  exact h.2 n σ a hσ

/--
@isnad1 id=isordina.2h4v.s5.678a635e5bf8 from=translated src=- shape=fadfb841 vocab=baefa325
-/
theorem isOrdinaryAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsOrdinaryAt p) : ρ₂.IsOrdinaryAt p := by
  obtain ⟨e⟩ := e
  intro P hP
  obtain ⟨L, ⟨b, hL⟩, hstab, hinert⟩ := h P hP
  refine ⟨L.map (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V), ⟨b.map e.toLinearEquiv, ?_⟩, ?_, ?_⟩
  · rw [hL, Submodule.map_span, Set.image_singleton, Module.Basis.map_apply,
      LinearEquiv.coe_coe]
  · intro σ hσ w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    rw [LinearEquiv.coe_coe, ← e.map_apply]
    exact Submodule.mem_map_of_mem (hstab σ hσ v hv)
  · intro σ hσ w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    rw [← e.map_apply, ← map_sub]
    exact Submodule.mem_map_of_mem (hinert σ hσ v)

/--
@isnad1 id=isunrami.2h4v.s5.4328d4ba96f4 from=translated src=- shape=fadfb841 vocab=2fb060c9
-/
theorem isUnramifiedAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by
  obtain ⟨e⟩ := e
  intro P hP σ hσ
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  rw [← e.map_apply, h P hP σ hσ, Module.End.one_apply, Module.End.one_apply]

/--
@isnad1 id=ordinary.2h6v.s6.d7246093c200 from=translated src=- shape=8d952400 vocab=7c61e837
-/
theorem ordinaryCondition_of_isEquiv (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ₁) : GaloisRep.ordinaryCondition 𝒪 p S ρ₂ := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨detIsCyclotomic_of_isEquiv e h₁, isOrdinaryAt_of_isEquiv e h₂,
    fun q hq hqS => isUnramifiedAt_of_isEquiv e (h₃ q hq hqS)⟩

end GaloisRepAdic.LCSol

/--
@isnad1 id=ordinary.2h6v.s6.d7246093c200 from=translated src=- shape=8d952400 vocab=7c61e837
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ₁) : GaloisRep.ordinaryCondition 𝒪 p S ρ₂ :=
  GaloisRepAdic.LCSol.ordinaryCondition_of_isEquiv 𝒪 e h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
