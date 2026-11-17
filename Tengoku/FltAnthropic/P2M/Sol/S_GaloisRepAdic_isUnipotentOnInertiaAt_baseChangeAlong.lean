import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/--
@isnad1 id=eq.1h5v.s11.10f3ce1babcd from=translated src=- shape=ff8b3317 vocab=46317988
-/
theorem charpoly_apply_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((ρ.baseChangeAlong φ hφ).ρ σ).charpoly = (ρ.ρ σ).charpoly.map φ := by
  letI : Algebra A B := φ.toAlgebra
  show ((ρ.ρ σ).baseChange B).charpoly = (ρ.ρ σ).charpoly.map (algebraMap A B)
  exact LinearMap.charpoly_baseChange (ρ.ρ σ) B

/--
@isnad1 id=isunipot.2h5v.s6.27bc20927637 from=translated src=- shape=cbde18a5 vocab=72c8589d
-/
theorem isUnipotentOnInertiaAt_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnipotentOnInertiaAt q) :
    (ρ.baseChangeAlong φ hφ).IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  rw [charpoly_apply_baseChangeAlong, h P hP σ hσ, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one]

end GaloisRepAdic.LCSol

/--
@isnad1 id=isunipot.2h5v.s6.27bc20927637 from=translated src=- shape=cbde18a5 vocab=72c8589d
-/
theorem solution
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) {q : ℕ} (h : ρ.IsUnipotentOnInertiaAt q) :
    (ρ.baseChangeAlong φ hφ).IsUnipotentOnInertiaAt q :=
  GaloisRepAdic.LCSol.isUnipotentOnInertiaAt_baseChangeAlong φ hφ ρ h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
