import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial

/--
@isnad1 id=and.1h3v.s13.7c9f83fa6754 from=translated src=- shape=3801cd81 vocab=335aa0a6
-/
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ∧ Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by
  classical
  have hq : 1 < q := (Fact.out : q.Prime).one_lt
  have hm : 0 < q ^ N - 1 := by
    have : 1 < q ^ N := Nat.one_lt_pow hN.ne' hq
    omega

  set P : (↥K)[X] := X ^ (q ^ N - 1) - 1 with hP
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact Polynomial.X_pow_sub_C_ne_zero hm 1
  have hset : {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} = P.rootSet (PadicAlgCl q) := by
    ext ζ
    rw [Polynomial.mem_rootSet, hP]
    simp only [Set.mem_ofPred_eq, map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact ⟨fun h => ⟨hP0, h⟩, fun h => h.2⟩
  rw [hset]
  haveI : IsSplittingField K (IntermediateField.adjoin K (P.rootSet (PadicAlgCl q))) P :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  exact ⟨IsSplittingField.finiteDimensional _ P, Normal.of_isSplittingField P⟩
