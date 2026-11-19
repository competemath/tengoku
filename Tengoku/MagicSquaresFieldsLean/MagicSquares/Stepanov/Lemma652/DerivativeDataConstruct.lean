import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DerivativeExpansion
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DerivativeData
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Constructing StepánovDerivativeData from 6.49 and 6.50

This removes the first abstract input from Batch 5, under the literal
LN97 hypothesis that `g = f^s`.
-/

/-- The complete linear family `e_{ijn}`.-/
noncomputable def stepanovBookEDerivLinear
    {m u D M : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree) :
    StepanovUnknowns F m u D →ₗ[F]
      (Fin M → Fin m → Fin (u + 1) → Polynomial F) where
  toFun := fun v n i j =>
    stepanovBookDerivativeCoeffLinear
      f s hf hfdeg n i j v
  map_add' := by
    intro x y
    funext n i j
    simp
  map_smul' := by
    intro a x
    funext n i j
    simp

omit [Fintype F] in
/-- Uniform degree bound for all `e_{ijn}` with `n<M`.-/
theorem stepanovBookEDeriv_degree_le
    {m u D M K : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (hfK : f.natDegree ≤ K)
    (v : StepanovUnknowns F m u D)
    (n : Fin M) (i : Fin m) (j : Fin (u + 1)) :
    (stepanovBookEDerivLinear f s hf hfdeg v n i j).natDegree
      ≤ D + (M - 1) * (K - 1) := by
  have h0 :=
    stepanovBookDerivativeCoeff_natDegree_le
      (F := F) f s hf hfdeg v n i j
  have hn : (n : ℕ) ≤ M - 1 := by omega
  have hk : f.natDegree - 1 ≤ K - 1 := by omega
  have hmul :
      (n : ℕ) * (f.natDegree - 1)
        ≤ (M - 1) * (K - 1) :=
    Nat.mul_le_mul hn hk
  exact le_trans h0 (Nat.add_le_add_left hmul D)

/-- The concrete `StepanovDerivativeData` required by Batch 5.-/
noncomputable def stepanovDerivativeDataOfPower
    {m u D M K : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (hfK : f.natDegree ≤ K)
    (hMcard : M ≤ Fintype.card F) :
    StepanovDerivativeData
      F m u D M (D + (M - 1) * (K - 1))
      f (f ^ s) where
  eDeriv :=
    stepanovBookEDerivLinear f s hf hfdeg
  degree_le := by
    intro v n i j
    exact stepanovBookEDeriv_degree_le
      (F := F) f s hf hfdeg hfK v n i j
  expansion_eval := by
    intro v n c
    have hpoly :=
      stepanovDerivativeExpansion
        (F := F) f s hf hfdeg hMcard v n
    have hev := congrArg (fun P : Polynomial F => eval c P) hpoly
    simpa [stepanovBookEDerivLinear, Polynomial.eval_mul, Polynomial.eval_finsetSum] using hev

end LN97
end MagicSquares
