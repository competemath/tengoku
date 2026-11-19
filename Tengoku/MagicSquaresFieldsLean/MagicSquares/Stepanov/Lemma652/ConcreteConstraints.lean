import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DerivativeData
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Constraints
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.STNVanish
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The actual s_{t,n} constraint map

Given the derivative data `e_{i,j,n}`, this file constructs the linear
map whose values are the polynomials `s_{t,n}`. Taking its first
`N+1` coefficients gives exactly the homogeneous system counted in
(6.26).

Version 2 makes the parameter `r` explicit at every use where Lean
cannot infer it from the arguments, and spells out the finite-sum
linearity of `stepanovSTN`.
-/

/-- The family `(v,t,n) ↦ s_{t,n}` is linear in the original unknown
coefficient vector `v`.-/
noncomputable def stepanovSTNFamilyLinear
    {m r u D M Emax : ℕ}
    {f g : Polynomial F}
    (B : Polynomial F)
    (data : StepanovDerivativeData F m u D M Emax f g) :
    StepanovUnknowns F m u D →ₗ[F]
      (Fin r → Fin M → Polynomial F) where
  toFun := fun v t n =>
    stepanovSTN
      (fun tt ii =>
        powerReductionCoeff B (ii : ℕ) (tt : ℕ))
      (fun i j => data.eDeriv v n i j) t
  map_add' := by
    intro x y
    funext t n
    simp [stepanovSTN, Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' := by
    intro a x
    funext t n
    simp [stepanovSTN, Finset.smul_sum]

/-- The scalar homogeneous system obtained by setting every coefficient
of every `s_{t,n}` through degree `N` equal to zero.-/
noncomputable def stepanovCoefficientConstraints
    {m r u D M Emax : ℕ}
    {f g : Polynomial F}
    (N : ℕ)
    (B : Polynomial F)
    (data : StepanovDerivativeData F m u D M Emax f g) :
    StepanovUnknowns F m u D →ₗ[F]
      StepanovConstraintSpace F r M N :=
  polynomialFamilyCoeffConstraints N
    (stepanovSTNFamilyLinear (r := r) B data)

/-- If `Emax + u ≤ N`, kernel membership in the coefficient system
forces every polynomial `s_{t,n}` to vanish identically.-/
theorem stepanovSTN_eq_zero_of_coefficientConstraints_eq_zero
    {m r u D M Emax N : ℕ}
    {f g : Polynomial F}
    (B : Polynomial F)
    (data : StepanovDerivativeData F m u D M Emax f g)
    (hNu : Emax + u ≤ N)
    (v : StepanovUnknowns F m u D)
    (hv :
      stepanovCoefficientConstraints (r := r) N B data v = 0) :
    ∀ (t : Fin r) (n : Fin M),
      stepanovSTN
        (fun tt ii =>
          powerReductionCoeff B (ii : ℕ) (tt : ℕ))
        (fun i j => data.eDeriv v n i j) t = 0 := by
  apply polynomialFamily_eq_zero_of_constraints_eq_zero
    (S := stepanovSTNFamilyLinear (r := r) B data)
    (v := v)
    (N := N)
  · intro t n
    exact le_trans
      (stepanovSTN_natDegree_le
        (F := F)
        (fun tt ii =>
          powerReductionCoeff B (ii : ℕ) (tt : ℕ))
        (fun i j => data.eDeriv v n i j)
        (fun i j => data.degree_le v n i j)
        t)
      hNu
  · exact hv

/-- Kernel membership therefore gives the Hasse-derivative vanishing
required by Lemma 6.51 at every point with `B(g(c))=0`.-/
theorem hasse_vanish_of_coefficientConstraints_eq_zero
    {m r u D M Emax N : ℕ}
    {f g : Polynomial F}
    (B : Polynomial F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (data : StepanovDerivativeData F m u D M Emax f g)
    (hNu : Emax + u ≤ N)
    (v : StepanovUnknowns F m u D)
    (hv :
      stepanovCoefficientConstraints (r := r) N B data v = 0)
    (c : F)
    (hc : B.IsRoot (eval c g)) :
    ∀ n < M,
      eval c
        ((hasseDeriv n)
          (stepanovAuxiliary
            (Fintype.card F) M f g
            (stepanovDecode v))) = 0 := by
  intro n hn
  let nn : Fin M := ⟨n, hn⟩
  have hstn :
      ∀ (t : Fin r) (n' : Fin M),
        stepanovSTN
          (fun tt ii =>
            powerReductionCoeff B (ii : ℕ) (tt : ℕ))
          (fun i j => data.eDeriv v n' i j) t = 0 :=
    stepanovSTN_eq_zero_of_coefficientConstraints_eq_zero
      (F := F) (r := r) B data hNu v hv
  have hsum :
      (∑ i : Fin m,
        ∑ j : Fin (u + 1),
          eval c (data.eDeriv v nn i j) *
            (eval c g) ^ (i : ℕ) *
            (c ^ Fintype.card F) ^ (j : ℕ)) = 0 :=
    eval_doubleSum_frobenius_eq_zero_of_stepanovSTN_eq_zero
      (F := F) B hB hr hdeg
      (fun i j => data.eDeriv v nn i j)
      g c hc (fun t => hstn t nn)
  change
    eval c
      ((hasseDeriv (nn : ℕ))
        (stepanovAuxiliary
          (Fintype.card F) M f g
          (stepanovDecode v))) = 0
  rw [data.expansion_eval v nn c, hsum, mul_zero]

end LN97
end MagicSquares
