import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_StrictOrdinary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv

set_option autoImplicit false

namespace P2mStrictEquiv

variable {A : Type} [CommRing A] [IsLocalRing A] {ρ₁ ρ₂ : GaloisRepAdic A}

/--
@isnad1 id=eq.0h6v.s11.7650abc59236 from=translated src=- shape=a4ee6e32 vocab=c7c87294
-/
theorem map_apply_symm (e : GaloisRepAdic.Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ρ₂.V) :
    ρ₂.ρ σ y = e.toLinearEquiv (ρ₁.ρ σ (e.toLinearEquiv.symm y)) := by
  rw [e.map_apply, LinearEquiv.apply_symm_apply]

end P2mStrictEquiv

open P2mStrictEquiv in
/--
@isnad1 id=isstrict.2h4v.s5.faadedfa1719 from=translated src=- shape=fadfb841 vocab=e654899b
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsStrictOrdinaryAt p) : ρ₂.IsStrictOrdinaryAt p := by
  obtain ⟨e⟩ := e
  obtain ⟨hpA, h⟩ := h
  refine ⟨hpA, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, rfl⟩, hD, hI, hS⟩ := h P hP
  set E : ρ₁.V ≃ₗ[A] ρ₂.V := e.toLinearEquiv with hE
  have hmem : ∀ {v : ρ₁.V}, v ∈ A ∙ b 0 → E v ∈ A ∙ E (b 0) := by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨A ∙ E (b 0), ⟨b.map E, by rw [Module.Basis.map_apply]⟩, ?_, ?_, ?_⟩
  ·
    intro σ hσ v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, map_apply_symm e, ← hE, LinearEquiv.symm_apply_apply]
    exact Submodule.smul_mem _ _ (hmem (hD σ hσ _ (Submodule.mem_span_singleton_self _)))
  ·
    intro σ hσ v
    have h1 : ρ₂.ρ σ v - v = E (ρ₁.ρ σ (E.symm v) - E.symm v) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
    rw [h1]
    exact hmem (hI σ hσ _)
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hc⟩ := hS σ hσ
    refine ⟨x, z, ?_, ?_, hc⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_apply_symm e, ← hE, map_smul, LinearEquiv.symm_apply_apply,
        ← map_smul E, hx _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
        map_smul, map_smul, smul_comm]
    · intro v
      have h1 : ρ₂.ρ σ v - z • v = E (ρ₁.ρ σ (E.symm v) - z • E.symm v) := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
      rw [h1]
      exact hmem (hz _)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
