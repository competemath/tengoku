import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_ordinaryCondition_baseChangeAlong.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_ordinaryCondition_baseChangeAlong

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/--
@isnad1 id=eq.1h5v.s12.c4b737551d18 from=translated src=- shape=8cf7b612 vocab=365ed307
-/
theorem det_apply_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong φ hφ).ρ σ) = φ (LinearMap.det (ρ.ρ σ)) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = algebraMap A B (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)

/--
@isnad1 id=detiscyc.2h5v.s6.3c40fbb80c46 from=translated src=- shape=cbde18a5 vocab=26b7bab2
-/
theorem detIsCyclotomic_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p := by
  refine ⟨?_, fun n σ a hσ => ?_⟩
  · have hp : φ (p : A) ∈ IsLocalRing.maximalIdeal B := map_nonunit φ (p : A) h.1
    rwa [map_natCast] at hp
  · rw [det_apply_baseChangeAlong, Ideal.mem_span_singleton]
    have hdvd := map_dvd φ (Ideal.mem_span_singleton.mp (h.2 n σ a hσ))
    rwa [map_natCast, map_sub, map_natCast] at hdvd

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

/--
@isnad1 id=isunrami.2h5v.s6.d0490229d467 from=translated src=- shape=cbde18a5 vocab=596d07dd
-/
theorem isUnramifiedAt_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {q : ℕ} (h : ρ.IsUnramifiedAt q) : (ρ.baseChangeAlong φ hφ).IsUnramifiedAt q := by
  letI : Algebra A B := φ.toAlgebra
  intro P hP σ hσ
  show (ρ.ρ σ).baseChange B = 1
  rw [h P hP σ hσ, LinearMap.baseChange_one]

/--
@isnad1 id=ordinary.2h7v.s7.97ed1a0fa0e4 from=translated src=- shape=07c16804 vocab=c47ae4d6
-/
theorem ordinaryCondition_baseChangeAlong (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ) :
    GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨detIsCyclotomic_baseChangeAlong φ hφ ρ h₁, isOrdinaryAt_baseChangeAlong φ hφ ρ h₂,
    fun q hq hqS => isUnramifiedAt_baseChangeAlong φ hφ ρ (h₃ q hq hqS)⟩

end GaloisRepAdic.LCSol

/--
@isnad1 id=ordinary.2h7v.s7.97ed1a0fa0e4 from=translated src=- shape=07c16804 vocab=c47ae4d6
-/
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 A] [Algebra 𝒪 B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) {p : ℕ} {S : Finset ℕ}
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ) :
    GaloisRep.ordinaryCondition 𝒪 p S (ρ.baseChangeAlong φ hφ) :=
  GaloisRepAdic.LCSol.ordinaryCondition_baseChangeAlong 𝒪 φ hφ ρ h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
