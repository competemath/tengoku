import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_StrictOrdinary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_strictOrdinaryCondition_of_isEquiv.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_strictOrdinaryCondition_of_isEquiv

set_option autoImplicit false

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (IsStrictOrdinaryAt DetIsCyclotomic IsUnramifiedAt det Equiv IsEquiv ρ V)
namespace S1Aux
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem conj_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e.map_apply, LinearEquiv.apply_symm_apply]

theorem det_apply_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (ρ₂.ρ σ) = LinearMap.det (ρ₁.ρ σ) := by
  rw [conj_eq e σ, LinearMap.det_conj]

theorem detIsCyclotomic_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.DetIsCyclotomic p) : ρ₂.DetIsCyclotomic p := by
  obtain ⟨e⟩ := e
  refine ⟨h.1, fun n σ a hσ => ?_⟩
  rw [det_apply_eq e σ]
  exact h.2 n σ a hσ

theorem isUnramifiedAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by
  obtain ⟨e⟩ := e
  intro P hP σ hσ
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  rw [← e.map_apply, h P hP σ hσ, Module.End.one_apply, Module.End.one_apply]

theorem isStrictOrdinaryAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsStrictOrdinaryAt p) : ρ₂.IsStrictOrdinaryAt p := by
  obtain ⟨f⟩ := e
  let E : ρ₁.V ≃ₗ[A] ρ₂.V := f.toLinearEquiv
  have hmap : ∀ σ v, E (ρ₁.ρ σ v) = ρ₂.ρ σ (E v) := fun σ v => f.map_apply σ v
  have hmap' : ∀ σ w, ρ₂.ρ σ w = E (ρ₁.ρ σ (E.symm w)) := fun σ w => by
    rw [hmap, LinearEquiv.apply_symm_apply]
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, hb⟩, hD, hI, hS⟩ := h.2 P hP
  refine ⟨L.map (E : ρ₁.V →ₗ[A] ρ₂.V), ⟨b.map E, ?_⟩, ?_, ?_, ?_⟩
  · rw [hb, Submodule.map_span, Set.image_singleton]; rfl
  · intro σ hσ w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    exact Submodule.mem_map.2 ⟨ρ₁.ρ σ v, hD σ hσ v hv, (hmap σ v)⟩
  · intro σ hσ w
    have := hI σ hσ (E.symm w)
    refine Submodule.mem_map.2 ⟨ρ₁.ρ σ (E.symm w) - E.symm w, this, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub]
    rw [hmap, LinearEquiv.apply_symm_apply]
  · intro σ hσ
    obtain ⟨x, z, hx, hz, hcong⟩ := hS σ hσ
    refine ⟨x, z, fun w hw => ?_, fun w => ?_, hcong⟩
    · obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      simp only [LinearEquiv.coe_coe]
      rw [← hmap, hx v hv, map_smul]
    · refine Submodule.mem_map.2 ⟨ρ₁.ρ σ (E.symm w) - z • E.symm w, hz (E.symm w), ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul]
      rw [hmap, LinearEquiv.apply_symm_apply]

end GaloisRepAdic.S1Aux

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.strictOrdinaryCondition 𝒪 p S ρ₁) :
    GaloisRep.strictOrdinaryCondition 𝒪 p S ρ₂ := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨GaloisRepAdic.S1Aux.detIsCyclotomic_of_isEquiv e h₁,
    GaloisRepAdic.S1Aux.isStrictOrdinaryAt_of_isEquiv e h₂,
    fun q hq hqS => GaloisRepAdic.S1Aux.isUnramifiedAt_of_isEquiv e (h₃ q hq hqS)⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
