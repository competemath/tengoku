import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_baseChangeAlong.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_baseChangeAlong

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/--
@isnad1 id=isordina.2h5v.s6.9616d06b8ac8 from=translated src=- shape=cbde18a5 vocab=5a9966d4
-/
theorem isOrdinaryAt_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsOrdinaryAt p := by
  letI : Algebra A B := φ.toAlgebra
  intro P hP
  obtain ⟨L, ⟨b, hL⟩, hstab, hinert⟩ := h P hP
  show ∃ L' : Submodule B (B ⊗[A] ρ.V),
      (∃ b' : Module.Basis (Fin 2) B (B ⊗[A] ρ.V), L' = B ∙ b' 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ L', (ρ.ρ σ).baseChange B w ∈ L') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : B ⊗[A] ρ.V, (ρ.ρ σ).baseChange B w - w ∈ L')

  have hline : ∀ (c : B), ∀ x ∈ L, c ⊗ₜ[A] x ∈ B ∙ ((1 : B) ⊗ₜ[A] b 0) := by
    intro c x hx
    rw [hL] at hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [TensorProduct.tmul_smul]
    refine Submodule.smul_of_tower_mem _ a (Submodule.mem_span_singleton.mpr ⟨c, ?_⟩)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨B ∙ (b.baseChange B 0), ⟨b.baseChange B, rfl⟩, ?_, ?_⟩
  · intro σ hσ w hw
    rw [Module.Basis.baseChange_apply] at hw ⊢
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, LinearMap.baseChange_tmul]
    exact Submodule.smul_mem _ c
      (hline 1 _ (hstab σ hσ (b 0) (hL ▸ Submodule.mem_span_singleton_self (b 0))))
  · intro σ hσ w
    rw [Module.Basis.baseChange_apply]
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [LinearMap.map_zero, sub_zero]
      exact Submodule.zero_mem _
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub]
      exact hline c _ (hinert σ hσ v)
    | add x y hx hy =>
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy

end GaloisRepAdic.LCSol

/--
@isnad1 id=isordina.2h5v.s6.9616d06b8ac8 from=translated src=- shape=cbde18a5 vocab=5a9966d4
-/
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.IsOrdinaryAt p) : (ρ.baseChangeAlong φ hφ).IsOrdinaryAt p :=
  GaloisRepAdic.LCSol.isOrdinaryAt_baseChangeAlong φ hφ ρ h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
