import Tengoku.Seed.Algebra.Algebra.Spectrum.Basic
import Tengoku.Seed.Analysis.Normed.Algebra.Basic
import Tengoku.Seed.Analysis.Normed.Operator.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projected resolvents and finite mean-gap compression

The exact second resolvent identity factors through an idempotent when the
perturbation is supported on that idempotent. One-sided comparison with a
reference resolvent retains this support. These estimates permit compressing
a gap in a deterministic matrix mean without spectral projections of an
infinite-dimensional random or free operator.
-/

noncomputable section
set_option autoImplicit false

section Algebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- A reference resolvent on the right controls a projected resolvent by an
exact factorization, without any commutation or smallness hypothesis.
@isnad1 id=eq.2h6v.s7.038c1217ce93 from=translated src=- shape=b251bc22 vocab=3e933c6e
-/
theorem resolvent_mul_eq_one_add_mul_resolvent_mul {a d : A} {z : R}
    (ha : z ∈ resolventSet R a) (hd : z ∈ resolventSet R d) (p : A) :
    resolvent a z * p =
      (1 + resolvent a z * (a - d)) * (resolvent d z * p) := by
  have hi : resolvent a z * (algebraMap R A z - a) = 1 :=
    Ring.inverse_mul_cancel _ ha
  have hj : (algebraMap R A z - d) * resolvent d z = 1 :=
    Ring.mul_inverse_cancel _ hd
  calc
    _ = resolvent a z * ((algebraMap R A z - d) * resolvent d z) * p := by
      rw [hj, mul_one]
    _ = (resolvent a z * (algebraMap R A z - d)) * (resolvent d z * p) := by
      simp only [mul_assoc]
    _ = _ := by
      congr 1
      calc
        resolvent a z * (algebraMap R A z - d) =
            resolvent a z * ((algebraMap R A z - a) + (a - d)) := by abel_nf
        _ = 1 + resolvent a z * (a - d) := by rw [mul_add, hi]

/-- The analogous left projection factorization retains the reference
resolvent on the left. No spectral projection of `a` is needed.
@isnad1 id=eq.2h6v.s7.032b905743be from=translated src=- shape=97c4a68a vocab=3e933c6e
-/
theorem mul_resolvent_eq_mul_resolvent_mul_one_add {a d : A} {z : R}
    (ha : z ∈ resolventSet R a) (hd : z ∈ resolventSet R d) (p : A) :
    p * resolvent a z =
      (p * resolvent d z) * (1 + (a - d) * resolvent a z) := by
  have hi : (algebraMap R A z - a) * resolvent a z = 1 :=
    Ring.mul_inverse_cancel _ ha
  have hj : resolvent d z * (algebraMap R A z - d) = 1 :=
    Ring.inverse_mul_cancel _ hd
  calc
    _ = p * (resolvent d z * (algebraMap R A z - d)) * resolvent a z := by
      rw [hj, mul_one]
    _ = (p * resolvent d z) * ((algebraMap R A z - d) * resolvent a z) := by
      simp only [mul_assoc]
    _ = _ := by
      congr 1
      calc
        (algebraMap R A z - d) * resolvent a z =
            ((algebraMap R A z - a) + (a - d)) * resolvent a z := by abel_nf
        _ = 1 + (a - d) * resolvent a z := by rw [add_mul, hi]

end Algebra

section Norm

variable {R A : Type*} [NormedField R] [NormedRing A] [NormedAlgebra R A]

/-- A right projected resolvent is controlled by the corresponding reference
resolvent and the actual perturbation norm.
@isnad1 id=le.2h6v.s8.bf774db3bc42 from=translated src=- shape=8943977b vocab=8378491f
-/
theorem norm_resolvent_mul_le_reference {a d : A} {z : R}
    (ha : z ∈ resolventSet R a) (hd : z ∈ resolventSet R d) (p : A) :
    ‖resolvent a z * p‖ ≤
      (‖(1 : A)‖ + ‖resolvent a z‖ * ‖a - d‖) * ‖resolvent d z * p‖ := by
  rw [resolvent_mul_eq_one_add_mul_resolvent_mul ha hd p]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) (norm_nonneg _))

/-- The left projected resolvent obeys the symmetric reference estimate,
with the factor order preserved.
@isnad1 id=le.2h6v.s8.5369c58c4811 from=translated src=- shape=7af95b12 vocab=8378491f
-/
theorem norm_mul_resolvent_le_reference {a d : A} {z : R}
    (ha : z ∈ resolventSet R a) (hd : z ∈ resolventSet R d) (p : A) :
    ‖p * resolvent a z‖ ≤
      ‖p * resolvent d z‖ * (‖(1 : A)‖ + ‖a - d‖ * ‖resolvent a z‖) := by
  rw [mul_resolvent_eq_mul_resolvent_mul_one_add ha hd p]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) (norm_nonneg _))

/-- The supported second-resolvent identity bounds the difference by the two
projected endpoint resolvents. The projection need only be idempotent.
@isnad1 id=le.4h7v.s8.aea7e17b707a from=translated src=- shape=2dd972cb vocab=95328525
-/
theorem norm_resolvent_sub_resolvent_le_projected {a b p : A} {z : R}
    (ha : z ∈ resolventSet R a) (hb : z ∈ resolventSet R b)
    (hp : p * p = p) {c : R}
    (hab : a - b = c • p) :
    ‖resolvent a z - resolvent b z‖ ≤
      ‖c‖ * (‖resolvent a z * p‖ * ‖p * resolvent b z‖) := by
  rw [spectrum.resolvent_sub_resolvent ha hb, hab, mul_smul_comm, smul_mul_assoc, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  have heq : resolvent a z * p * resolvent b z =
      (resolvent a z * p) * (p * resolvent b z) := by
    calc
      _ = resolvent a z * (p * p) * resolvent b z := by rw [hp]
      _ = _ := by simp only [mul_assoc]
  rw [heq]
  exact norm_mul_le _ _

end Norm

end
