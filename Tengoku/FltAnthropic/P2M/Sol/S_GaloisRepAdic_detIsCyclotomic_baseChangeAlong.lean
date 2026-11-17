import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_detIsCyclotomic_baseChangeAlong

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

end GaloisRepAdic.LCSol

/--
@isnad1 id=detiscyc.2h5v.s6.3c40fbb80c46 from=translated src=- shape=cbde18a5 vocab=26b7bab2
-/
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p :=
  GaloisRepAdic.LCSol.detIsCyclotomic_baseChangeAlong φ hφ ρ h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
