import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum
import Tengoku.FltAnthropic.Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_forall_exists_finiteDimensional_primeLocalToGlobal_iff

set_option autoImplicit false
open CategoryTheory ExtCitation
open Polynomial
open scoped Pointwise

/--
@isnad1 id=iff.0h3v.s13.dd5f1d461bd9 from=translated src=- shape=8674436f vocab=0403df3e
-/
theorem solution
    (q : Nat.Primes) [Fact (q : ℕ).Prime]
    {k : Type} [CommRing k] (M : Rep k (primeLocalGaloisGroup q)) :
    (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m) ↔
      ∀ m : M, ∃ K : IntermediateField ℚ_[(q : ℕ)] (PadicAlgCl (q : ℕ)), FiniteDimensional ℚ_[(q : ℕ)] K ∧
        ∀ s : primeLocalGaloisGroup q, s ∈ K.fixingSubgroup → M.ρ s m = m :=
  forall_congr' fun m =>
    exists_finiteDimensional_comap_localGaloisToGlobal_iff (q : ℕ)
      (fun U => ∀ s : primeLocalGaloisGroup q, s ∈ U → M.ρ s m = m)
      (fun _ _ hVU h s hs => h s (hVU hs))
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
