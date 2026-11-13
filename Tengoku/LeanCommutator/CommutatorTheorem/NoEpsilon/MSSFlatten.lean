import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fresh-variable and flat mixed-characteristic operators

These algebraic identities compare nested fresh variables with a single finite
multivariate polynomial. All coefficient rings are arbitrary commutative rings.
-/

namespace NoEpsilon.MSSExpectation

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Move the first variable into the coefficient ring, leaving the other variables free.-/
noncomputable def splitHead (n : ℕ) : MvPolynomial (Fin (n + 1)) R →+*
    MvPolynomial (Fin n) (MvPolynomial Unit R) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (Fin.cases (MvPolynomial.C (MvPolynomial.X ())) MvPolynomial.X)

/-- Restrict to the first coordinate axis, retaining its polynomial variable.-/
noncomputable def headRestriction (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial Unit R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.cases (MvPolynomial.X ()) (fun _ ↦ 0))

@[simp] theorem headRestriction_C (n : ℕ) (a : R) :
    headRestriction n (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [headRestriction]

@[simp] theorem headRestriction_X_zero (n : ℕ) :
    headRestriction n (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X () := by simp [headRestriction]

@[simp] theorem headRestriction_X_succ (n : ℕ) (i : Fin n) :
    headRestriction n (MvPolynomial.X i.succ : MvPolynomial (Fin (n + 1)) R) = 0 := by
  simp [headRestriction]

@[simp] theorem splitHead_C (n : ℕ) (a : R) :
    splitHead n (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := by
  simp [splitHead]

@[simp] theorem splitHead_X_zero (n : ℕ) :
    splitHead n (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.C (MvPolynomial.X ()) := by simp [splitHead]

@[simp] theorem splitHead_X_succ (n : ℕ) (i : Fin n) :
    splitHead n (MvPolynomial.X i.succ : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.X i := by simp [splitHead]

/-- Evaluating the remaining variables at zero gives restriction to the first axis.-/
theorem eval_zero_splitHead (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (fun _ ↦ (0 : MvPolynomial Unit R)) (splitHead n p) =
      headRestriction n p := by
  have h : (MvPolynomial.eval (fun _ : Fin n ↦ (0 : MvPolynomial Unit R))).comp
      (splitHead n) = headRestriction (R := R) n := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      induction i using Fin.cases <;> simp [headRestriction]
  exact RingHom.congr_fun h p

/-- Evaluating the retained first coordinate too is simultaneous evaluation at zero.-/
theorem eval_zero_headRestriction (n : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (fun _ ↦ (0 : R)) (headRestriction n p) =
      MvPolynomial.eval (fun _ ↦ (0 : R)) p := by
  have h : (MvPolynomial.eval (fun _ : Unit ↦ (0 : R))).comp (headRestriction n) =
      MvPolynomial.eval (fun _ : Fin (n + 1) ↦ (0 : R)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      induction i using Fin.cases <;> simp [headRestriction]
  exact RingHom.congr_fun h p

/-- A finite sequence of the literal MSS differential operators.-/
noncomputable def mixedDifference {σ : Type*} (xs : List σ)
    (p : MvPolynomial σ R) : MvPolynomial σ R :=
  xs.foldr (fun i q ↦ q - MvPolynomial.pderiv i q) p

/-- The determinant pencil with an arbitrary base matrix and one covariance per variable.-/
noncomputable def affinePencil {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin n → Matrix ι ι R) :
    MvPolynomial (Fin n) R :=
  (B.map MvPolynomial.C + ∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) R) •
    (A i).map MvPolynomial.C).det

/-- The flat mixed determinant is exactly the product of the `1 - ∂ᵢ` operators
applied to the affine determinant pencil, followed by evaluation at zero.-/
noncomputable def flatMixedDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (B : Matrix ι ι R) (A : Fin n → Matrix ι ι R) : R :=
  MvPolynomial.eval (fun _ ↦ (0 : R))
    (mixedDifference (List.finRange n) (affinePencil n B A))

end NoEpsilon.MSSExpectation
