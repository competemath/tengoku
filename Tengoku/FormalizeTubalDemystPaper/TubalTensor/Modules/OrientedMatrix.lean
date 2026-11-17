import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.CommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Modules/OrientedMatrix.lean
  K_M^m — the module of oriented matrices (Section 4, Theorem 19).

  K_M^m is the direct sum of m copies of K_M, viewed as column vectors.
  It is a free module over K_M of rank m.
-/

namespace TubalTensor

open Module

variable {n : ℕ} {td : TubalData n}

/-! ## Definition of oriented matrices -/

/-- The module of oriented matrices: m-tuples of elements of K_M.
    This is K_M^m = K_M ⊕ ⋯ ⊕ K_M (m copies).-/
def OrientedMatrix (m : ℕ) (n : ℕ) (td : TubalData n) := Fin m → KM n td

namespace OrientedMatrix

variable {m : ℕ}

noncomputable instance : DecidableEq (OrientedMatrix m n td) :=
  inferInstanceAs (DecidableEq (Fin m → KM n td))

/-- Oriented matrices inherit addition, scalar multiplication, and module structure
    componentwise from KM.-/
noncomputable instance instAddCommGroup : AddCommGroup (OrientedMatrix m n td) :=
  inferInstanceAs (AddCommGroup (Fin m → KM n td))

noncomputable instance instModule : Module (KM n td) (OrientedMatrix m n td) :=
  inferInstanceAs (Module (KM n td) (Fin m → KM n td))

/-! ## Standard basis (E₁, …, Eₘ) -/

/-- The i-th standard basis oriented matrix: has 1 (= eM) at position i, 0 elsewhere.-/
noncomputable def stdBasis (i : Fin m) : OrientedMatrix m n td :=
  Pi.single i 1

@[simp]
theorem stdBasis_apply_same (i : Fin m) : stdBasis (td := td) i i = 1 :=
  Pi.single_eq_same i 1

@[simp]
theorem stdBasis_apply_ne {i j : Fin m} (h : j ≠ i) : stdBasis (td := td) i j = 0 :=
  Pi.single_eq_of_ne h 1

/-- The standard basis for K_M^m over K_M.-/
noncomputable def basis : Basis (Fin m) (KM n td) (OrientedMatrix m n td) :=
  Pi.basisFun (KM n td) (Fin m)

@[simp]
theorem basis_apply (i : Fin m) : basis (td := td) i = stdBasis i :=
  Pi.basisFun_apply (KM n td) (Fin m) i

/-! ## Theorem 19: K_M^m is a free module of rank m -/

noncomputable instance instFree : Module.Free (KM n td) (OrientedMatrix m n td) :=
  inferInstanceAs (Module.Free (KM n td) (Fin m → KM n td))

noncomputable instance instFinite : Module.Finite (KM n td) (OrientedMatrix m n td) :=
  inferInstanceAs (Module.Finite (KM n td) (Fin m → KM n td))

/-- **Theorem 19**: K_M^m is a free module over K_M of rank m.-/
theorem finrank_eq (hn : 0 < n) :
    finrank (KM n td) (OrientedMatrix m n td) = m := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (KM n td) := inferInstanceAs (Nontrivial (Fin n → ℝ))
  exact Module.finrank_fin_fun (R := KM n td)

end OrientedMatrix

end TubalTensor
