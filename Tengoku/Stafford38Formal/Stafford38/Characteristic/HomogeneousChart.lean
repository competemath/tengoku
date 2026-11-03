module
public import Tengoku.Stafford38Formal.Stafford38.MathlibCompat.MvPolynomialCoeff
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.LinearAction
public import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
public import Tengoku.Seed.Algebra.MvPolynomial.Monad
public import Tengoku.Seed.Algebra.CharZero.Infinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_eval_ne_zero_of_homogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_symbolLinearAlgHom` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms homogeneous_unit_eq_monomial` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms axisPoint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms axisPolynomial` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms axisPolynomial_isHomogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_axis_eq_eval_axisPolynomial_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_axis_eq_pureCoefficient` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearCombination_isHomogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symbolLinearAlgHom_isHomogeneous` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_symbolLinearAlgHom_axis` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pureCoefficient_symbolLinearAlgHom` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Homogeneous symbols and nonzero chart columns

Over a characteristic-zero field, a nonzero homogeneous phase-space symbol
has a nonvanishing point over the original field. Linear substitution
identifies evaluation along a chosen matrix column with the corresponding
pure-power coefficient. `SymplecticCompletion` constructs a symplectic matrix
with the required nonzero vector in that column.
-/

namespace Stafford38.CharacteristicHomogeneousChart

open Stafford38.Characteristic
open Stafford38.CharacteristicLinearAction

noncomputable section
universe u
variable (k : Type u) [Field k]

/--
@isnad1 id=ex.2h4v.s7.eb6aa8ffc6d7 from=translated src=- shape=dbd4964d vocab=3b1197ff
-/
theorem exists_eval_ne_zero_of_homogeneous [CharZero k]
    {n N : ℕ} {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) :
    ∃ v : PhaseVar n → k, MvPolynomial.eval v P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hne (hP.eq_zero_of_forall_eval_eq_zero h)

/--
@isnad1 id=eq.0h5v.s9.c3dbac6fdd87 from=translated src=- shape=f9f5e8e0 vocab=ab73f47e
-/
theorem eval_symbolLinearAlgHom {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (v : PhaseVar n → k) (P : SymbolRing k n) :
    MvPolynomial.eval v (symbolLinearAlgHom k M P) =
      MvPolynomial.eval (fun i => ∑ j, M i j * v j) P := by
  rw [symbolLinearAlgHom]
  change MvPolynomial.aeval v
      (MvPolynomial.aeval (symbolLinearCombination k M) P) =
    MvPolynomial.aeval (fun i => ∑ j, M i j * v j) P
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  simp [symbolLinearCombination]

/--
@isnad1 id=eq.1h3v.s8.951450fff5bf from=translated src=- shape=a3f4f0c3 vocab=9159080d
-/
theorem homogeneous_unit_eq_monomial {N : ℕ}
    (P : MvPolynomial Unit k) (hP : P.IsHomogeneous N) :
    P = MvPolynomial.monomial (Finsupp.single () N)
      (MvPolynomial.coeff (Finsupp.single () N) P) := by
  ext d
  by_cases hd : d = Finsupp.single () N
  · subst d
    simp
  · have hdegree : d.degree ≠ N := by
      intro hdeg
      apply hd
      have hdform : d = Finsupp.single () (d ()) := by
        apply Finsupp.ext
        intro i
        rcases i with ⟨⟩
        simp
      rw [hdform, Finsupp.degree_single] at hdeg
      rw [hdform, hdeg]
    rw [hP.coeff_eq_zero hdegree]
    rw [MvPolynomial.coeff_monomial, ite_eq_right (Ne.symm hd)]

def axisPoint {n : ℕ} (t : PhaseVar n) : PhaseVar n → k :=
  fun i => if i = t then 1 else 0

def axisPolynomial {n : ℕ} (t : PhaseVar n) :
    SymbolRing k n →ₐ[k] MvPolynomial Unit k :=
  MvPolynomial.aeval (fun i => if i = t then MvPolynomial.X () else 0)

/--
@isnad1 id=ishomoge.1h5v.s8.c5b413446618 from=translated src=- shape=09618882 vocab=06a59fbc
-/
theorem axisPolynomial_isHomogeneous {n N : ℕ}
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (axisPolynomial k t P).IsHomogeneous N := by
  simpa [axisPolynomial, ← MvPolynomial.aeval_eq_bind₁] using hP.aeval (n := 1)
    (fun i => if i = t then MvPolynomial.X () else 0)
    (fun i => by
      by_cases hi : i = t
      · simp [hi, MvPolynomial.isHomogeneous_X]
      · simp [hi, MvPolynomial.isHomogeneous_zero])

/--
@isnad1 id=eq.0h4v.s9.4344a56bc802 from=translated src=- shape=35a53756 vocab=6e347481
-/
theorem eval_axis_eq_eval_axisPolynomial_one {n : ℕ}
    (t : PhaseVar n) (P : SymbolRing k n) :
    MvPolynomial.eval (axisPoint k t) P =
      MvPolynomial.eval (fun _ : Unit => (1 : k)) (axisPolynomial k t P) := by
  change MvPolynomial.aeval (axisPoint k t) P =
    MvPolynomial.aeval (fun _ : Unit => (1 : k))
      (MvPolynomial.aeval
        (fun i => if i = t then MvPolynomial.X () else 0) P)
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext i
  by_cases hi : i = t
  · simp [axisPoint, hi]
  · simp [axisPoint, hi]

/--
@isnad1 id=eq.1h5v.s8.c23e89996f69 from=translated src=- shape=88b6b30f vocab=d2da507f
-/
theorem eval_axis_eq_pureCoefficient {n N : ℕ}
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    MvPolynomial.eval (axisPoint k t) P =
      MvPolynomial.coeff (Finsupp.single () N) (axisPolynomial k t P) := by
  rw [eval_axis_eq_eval_axisPolynomial_one]
  rw [homogeneous_unit_eq_monomial k (axisPolynomial k t P)
    (axisPolynomial_isHomogeneous k t hP)]
  simp [MvPolynomial.eval_monomial]

/--
@isnad1 id=ishomoge.0h4v.s5.d2d1b7a6680b from=translated src=- shape=3b2ed6b4 vocab=57afe81e
-/
theorem symbolLinearCombination_isHomogeneous {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    (symbolLinearCombination k M i).IsHomogeneous 1 := by
  rw [symbolLinearCombination]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j hj
  simpa using (MvPolynomial.isHomogeneous_C (PhaseVar n) (M i j)).mul
    (MvPolynomial.isHomogeneous_X (R := k) j)

/--
@isnad1 id=ishomoge.1h5v.s8.debbfbf8df15 from=translated src=- shape=ec1e6436 vocab=17f90802
-/
theorem symbolLinearAlgHom_isHomogeneous {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    (symbolLinearAlgHom k M P).IsHomogeneous N := by
  simpa [symbolLinearAlgHom] using hP.aeval (n := 1)
    (symbolLinearCombination k M)
    (symbolLinearCombination_isHomogeneous k M)

/--
@isnad1 id=eq.0h5v.s9.3579708afd59 from=translated src=- shape=a2bf669e vocab=32c71058
-/
theorem eval_symbolLinearAlgHom_axis {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (t : PhaseVar n) (P : SymbolRing k n) :
    MvPolynomial.eval (axisPoint k t) (symbolLinearAlgHom k M P) =
      MvPolynomial.eval (fun i => M i t) P := by
  rw [eval_symbolLinearAlgHom]
  congr 2
  funext i
  simp [axisPoint]

/--
@isnad1 id=eq.1h6v.s9.98487b4a186f from=translated src=- shape=feda0d54 vocab=521fb17c
-/
theorem pureCoefficient_symbolLinearAlgHom {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (t : PhaseVar n) {P : SymbolRing k n} (hP : P.IsHomogeneous N) :
    MvPolynomial.coeff (Finsupp.single () N)
        (axisPolynomial k t (symbolLinearAlgHom k M P)) =
      MvPolynomial.eval (fun i => M i t) P := by
  rw [← eval_axis_eq_pureCoefficient k t
    (symbolLinearAlgHom_isHomogeneous k M hP)]
  exact eval_symbolLinearAlgHom_axis k M t P

/- Exact statement pins for original-field nonvanishing and column detection. -/

end
end Stafford38.CharacteristicHomogeneousChart
