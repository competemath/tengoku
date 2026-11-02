import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.TensorDifferenceAlgebraicity
import Tengoku.Seed.Data.Nat.Find
import Tengoku.Seed.Algebra.Polynomial.Derivative
import Tengoku.Seed.Algebra.Polynomial.Div
import Tengoku.Seed.RingTheory.Nilpotent.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_annihilator_derivative_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms difference_eq_zero_of_annihilator_of_isNilpotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_base_of_contraction` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_base_of_difference_isNilpotent` (it only prints; the queue checks the axioms of every declaration). -/

/-! A minimal nonzero annihilator replaces the minpoly/separability route. -/

noncomputable section
namespace AlbertLean.Generic.TensorDifferenceDescent

open TensorDifferenceAlgebraicity
open scoped TensorProduct

universe u v
variable (H : Type u) (K : Type v)
variable [Field H] [CharZero H] [Field K] [Algebra H K]

abbrev TensorSquare := K ⊗[H] K

def left (a : K) : TensorSquare H K :=
  Algebra.TensorProduct.includeLeft (S := H) a

def right (a : K) : TensorSquare H K :=
  Algebra.TensorProduct.includeRight a

def difference (a : K) : TensorSquare H K := left H K a - right H K a

/-- Among the nonzero annihilators of `a`, one of minimal degree has
nonvanishing derivative at `a` in characteristic zero.-/
theorem exists_annihilator_derivative_ne_zero (a : K)
    (h : ∃ p : Polynomial H, p ≠ 0 ∧ Polynomial.aeval a p = 0) :
    ∃ p : Polynomial H, p ≠ 0 ∧ Polynomial.aeval a p = 0 ∧
      Polynomial.aeval a p.derivative ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ p : Polynomial H, p ≠ 0 ∧ Polynomial.aeval a p = 0 ∧ p.natDegree = n
  have hn : ∃ n, P n := by
    obtain ⟨p, hp0, hp⟩ := h
    exact ⟨p.natDegree, p, hp0, hp, rfl⟩
  obtain ⟨p, hp0, hpa, hpdeg⟩ := Nat.find_spec hn
  have hpdeg0 : p.natDegree ≠ 0 := by
    intro hdeg
    have hpC : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hcmap : algebraMap H K (p.coeff 0) = 0 := by
      have hr := hpa
      rw [hpC, Polynomial.aeval_C] at hr
      exact hr
    have hc : p.coeff 0 = 0 := (algebraMap H K).injective (by simpa using hcmap)
    apply hp0
    rw [hpC, hc, Polynomial.C_0]
  refine ⟨p, hp0, hpa, ?_⟩
  intro hpder
  have hpder0 : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hpdeg0
  have hlt0 : p.derivative.natDegree < p.natDegree :=
    Polynomial.natDegree_derivative_lt hpdeg0
  have hlt : p.derivative.natDegree < Nat.find hn := by
    simpa [hpdeg] using hlt0
  exact (Nat.find_min hn hlt)
    ⟨p.derivative, hpder0, hpder, rfl⟩

/-- A nonzero polynomial annihilator whose derivative remains nonzero at `a`
kills a nilpotent difference between the two tensor-square embeddings.-/
theorem difference_eq_zero_of_annihilator_of_isNilpotent
    (a : K) (p : Polynomial H)
    (hpa : Polynomial.aeval a p = 0)
    (hpder : Polynomial.aeval a p.derivative ≠ 0)
    (hz : IsNilpotent (difference H K a)) :
    difference H K a = 0 := by
  let q : Polynomial (TensorSquare H K) := p.map (algebraMap H (TensorSquare H K))
  let x : TensorSquare H K := right H K a
  let z : TensorSquare H K := difference H K a
  have hq_x : q.eval x = 0 := by
    change (p.map _).eval ((Algebra.TensorProduct.includeRight :
      K →ₐ[H] TensorSquare H K) a) = 0
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, hpa, map_zero]
  have hxz : x + z = left H K a := by
    simp [x, z, difference]
  have hq_xz : q.eval (x + z) = 0 := by
    rw [hxz]
    change (p.map _).eval ((Algebra.TensorProduct.includeLeft (S := H) :
      K →ₐ[H] TensorSquare H K) a) = 0
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, hpa, map_zero]
  have hdu : IsUnit (q.derivative.eval x) := by
    have huK : IsUnit (Polynomial.aeval a p.derivative) :=
      isUnit_iff_ne_zero.mpr hpder
    have huT := huK.map (Algebra.TensorProduct.includeRight :
      K →ₐ[H] TensorSquare H K)
    change IsUnit ((p.map _).derivative.eval ((Algebra.TensorProduct.includeRight :
      K →ₐ[H] TensorSquare H K) a))
    rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply]
    exact huT
  obtain ⟨r, hr⟩ : ∃ r : Polynomial (TensorSquare H K),
      q = (Polynomial.X - Polynomial.C x) * r :=
    Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hq_x)
  have hr_deriv : r.eval x = q.derivative.eval x := by
    have h := congrArg (fun s : Polynomial (TensorSquare H K) => s.derivative.eval x) hr
    simpa [Polynomial.derivative_mul] using h.symm
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (x + z) x r
  have hr_add : r.eval (x + z) = r.eval x + z * c := by
    have hc' : r.eval (x + z) - r.eval x = z * c := by
      simpa [add_sub_cancel_left] using hc
    simpa [add_comm] using sub_eq_iff_eq_add.mp hc'
  have hzc : IsNilpotent (z * c) :=
    (Commute.all z c).isNilpotent_mul_right hz
  have hfactor : IsUnit (r.eval (x + z)) := by
    rw [hr_add, hr_deriv]
    exact hzc.isUnit_add_left_of_commute hdu (Commute.all _ _)
  have hprod : z * r.eval (x + z) = 0 := by
    have h := congrArg (fun s : Polynomial (TensorSquare H K) => s.eval (x + z)) hr
    rw [hq_xz, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h
    simpa using h.symm
  exact hfactor.mul_right_injective (by simpa [mul_comm] using hprod)

/-- Once a contraction has the expected values on the two tensor embeddings,
tensor equality exhibits `a` in the base-field image.-/
theorem exists_base_of_contraction
    (a : K) (ell : K →ₗ[H] H) (pi : TensorSquare H K →ₗ[H] K)
    (hleft : pi (left H K a) = a)
    (hright : pi (right H K a) = algebraMap H K (ell a))
    (hz : difference H K a = 0) :
    ∃ h : H, algebraMap H K h = a := by
  refine ⟨ell a, ?_⟩
  have := congrArg pi hz
  simp only [difference, map_sub, map_zero, sub_eq_zero, hleft, hright] at this
  exact this.symm

/-- In characteristic zero, a nilpotent diagonal tensor difference forces the
chosen element to belong to the base field, without assuming the extension is
algebraic.-/
theorem exists_base_of_difference_isNilpotent (a : K)
    (hz : IsNilpotent (difference H K a)) :
    ∃ h : H, algebraMap H K h = a := by
  obtain ⟨n, hn⟩ := hz
  obtain ⟨p, hpmonic, hpa⟩ :=
    exists_monic_annihilator_of_tensorDifference_pow_eq_zero H K a n hn
  obtain ⟨q, hq0, hqa, hqder⟩ :=
    exists_annihilator_derivative_ne_zero H K a
      ⟨p, hpmonic.ne_zero, hpa⟩
  apply exists_base_of_contraction H K a (scalarRetraction H K) (contractRight H K)
  · simp [left]
  · simp [right, Algebra.smul_def]
  · exact difference_eq_zero_of_annihilator_of_isNilpotent H K a q hqa hqder ⟨n, hn⟩

end AlbertLean.Generic.TensorDifferenceDescent
