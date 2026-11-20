/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rotation and enumeration invariance

The literal complex cardinal is unchanged when both its nodes and evaluation point
are multiplied by a nonzero scalar. Reindexing the nodes simply reindexes the
cardinals. These identities imply the corresponding invariance of the actual
Lebesgue sum and its supremum over the entire unit circle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Rotate an admissible family by a unit complex number.-/
def NodeFamily.rotate (nodes : NodeFamily n) (rotation : Circle) : NodeFamily n where
  point i := rotation * nodes.point i
  injective := fun _ _ h => nodes.injective (mul_left_cancel h)

/-- Change the enumeration of an admissible family.-/
def NodeFamily.reindex (nodes : NodeFamily n) (permutation : Equiv.Perm (Fin n)) :
    NodeFamily n where
  point i := nodes.point (permutation i)
  injective := nodes.injective.comp permutation.injective

/--
@isnad1 id=eq.0h4v.s6.62f3de0d9c59 from=translated src=- shape=2886a311 vocab=fcf1ac12
-/
@[simp] lemma NodeFamily.coordinates_rotate (nodes : NodeFamily n) (rotation : Circle)
    (i : Fin n) :
    (nodes.rotate rotation).coordinates i = (rotation : ℂ) * nodes.coordinates i := by
  simp only [NodeFamily.coordinates, NodeFamily.rotate, Circle.coe_mul]

/--
@isnad1 id=eq.0h4v.s5.1cdf8f25c0eb from=translated src=- shape=88dc6672 vocab=64f93499
-/
@[simp] lemma NodeFamily.coordinates_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex permutation).coordinates i = nodes.coordinates (permutation i) :=
  rfl

/-- The cancellation identity uses only the nonzero multiplier; the nodes may be arbitrary.
@isnad1 id=eq.1h5v.s5.6123192c695b from=translated src=- shape=803c21c9 vocab=9b09519e
-/
lemma cardinal_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0) (j : Fin n) (w : ℂ) :
    cardinal (fun i => a * z i) j (a * w) = cardinal z j w := by
  unfold cardinal
  apply Finset.prod_congr rfl
  intro k hk
  rw [← mul_sub a w (z k), ← mul_sub a (z j) (z k)]
  exact mul_div_mul_left _ _ ha

/--
@isnad1 id=eq.1h5v.s5.64170685f126 from=translated src=- shape=7a41c5ab vocab=448ccd50
-/
lemma norm_cardinal_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0)
    (j : Fin n) (w : ℂ) :
    ‖cardinal (fun i => a * z i) j (a * w)‖ = ‖cardinal z j w‖ := by
  rw [cardinal_mul z ha]

/--
@isnad1 id=eq.1h4v.s5.8735077b7ef2 from=translated src=- shape=eef7dac4 vocab=75954f5e
-/
lemma lebesgueFunction_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    lebesgueFunction (fun i => a * z i) (a * w) = lebesgueFunction z w := by
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro j hj
  exact norm_cardinal_mul z ha j w

/--
@isnad1 id=eq.0h5v.s7.7c0ada304759 from=translated src=- shape=a1196b97 vocab=8b88fbe9
-/
lemma cardinal_rotate (nodes : NodeFamily n) (rotation : Circle) (j : Fin n)
    (w : Circle) :
    cardinal (nodes.rotate rotation).coordinates j ((rotation * w : Circle) : ℂ) =
      cardinal nodes.coordinates j (w : ℂ) := by
  simp only [Circle.coe_mul]
  change cardinal (fun i => (rotation : ℂ) * nodes.coordinates i) j
    ((rotation : ℂ) * (w : ℂ)) = _
  exact cardinal_mul nodes.coordinates (Circle.coe_ne_zero rotation) j (w : ℂ)

/--
@isnad1 id=eq.0h5v.s7.96a59782dbd6 from=translated src=- shape=559bed39 vocab=d514831f
-/
lemma norm_cardinal_rotate (nodes : NodeFamily n) (rotation : Circle) (j : Fin n)
    (w : Circle) :
    ‖cardinal (nodes.rotate rotation).coordinates j ((rotation * w : Circle) : ℂ)‖ =
      ‖cardinal nodes.coordinates j (w : ℂ)‖ := by
  rw [cardinal_rotate]

/--
@isnad1 id=eq.0h4v.s7.372740db9181 from=translated src=- shape=155377db vocab=0396d767
-/
lemma lebesgueFunction_rotate (nodes : NodeFamily n) (rotation : Circle) (w : Circle) :
    lebesgueFunction (nodes.rotate rotation).coordinates ((rotation * w : Circle) : ℂ) =
      lebesgueFunction nodes.coordinates (w : ℂ) := by
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro j hj
  exact norm_cardinal_rotate nodes rotation j w

/--
@isnad1 id=eq.0h3v.s4.3a20bfd06ff6 from=translated src=- shape=bd668e41 vocab=85720b2d
-/
lemma amplification_rotate (nodes : NodeFamily n) (rotation : Circle) :
    amplification (nodes.rotate rotation) = amplification nodes := by
  apply le_antisymm
  · apply (amplification_le_iff _ _).mpr
    intro w
    calc
      lebesgueFunction (nodes.rotate rotation).coordinates (w : ℂ) =
          lebesgueFunction (nodes.rotate rotation).coordinates
            ((rotation * (rotation⁻¹ * w) : Circle) : ℂ) := by simp
      _ = lebesgueFunction nodes.coordinates ((rotation⁻¹ * w : Circle) : ℂ) :=
        lebesgueFunction_rotate nodes rotation (rotation⁻¹ * w)
      _ ≤ amplification nodes := le_amplification nodes (rotation⁻¹ * w)
  · apply (amplification_le_iff _ _).mpr
    intro w
    calc
      lebesgueFunction nodes.coordinates (w : ℂ) =
          lebesgueFunction (nodes.rotate rotation).coordinates
            ((rotation * w : Circle) : ℂ) :=
        (lebesgueFunction_rotate nodes rotation w).symm
      _ ≤ amplification (nodes.rotate rotation) :=
        le_amplification (nodes.rotate rotation) (rotation * w)

/-- Reindexing a family transports the cardinal indexed by the same permutation.
@isnad1 id=eq.0h5v.s6.f9683ddd50f4 from=translated src=- shape=07bf0f07 vocab=25c0c4de
-/
lemma cardinal_reindex (z : Fin n → ℂ) (permutation : Equiv.Perm (Fin n))
    (j : Fin n) (w : ℂ) :
    cardinal (fun i => z (permutation i)) j w = cardinal z (permutation j) w := by
  unfold cardinal
  apply Finset.prod_equiv permutation
  · intro i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (not_congr permutation.injective.eq_iff).symm
  · intro i hi
    rfl

/--
@isnad1 id=eq.0h5v.s6.6ab8ea50c0dd from=translated src=- shape=a51fe7ca vocab=243f485e
-/
lemma norm_cardinal_reindex (z : Fin n → ℂ) (permutation : Equiv.Perm (Fin n))
    (j : Fin n) (w : ℂ) :
    ‖cardinal (fun i => z (permutation i)) j w‖ =
      ‖cardinal z (permutation j) w‖ := by
  rw [cardinal_reindex]

/--
@isnad1 id=eq.0h4v.s4.8dc24c95668a from=translated src=- shape=6fc9f924 vocab=0268ca4f
-/
lemma lebesgueFunction_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) (w : ℂ) :
    lebesgueFunction (nodes.reindex permutation).coordinates w =
      lebesgueFunction nodes.coordinates w := by
  unfold lebesgueFunction
  apply Fintype.sum_equiv permutation
  intro j
  change ‖cardinal (fun i => nodes.coordinates (permutation i)) j w‖ = _
  exact norm_cardinal_reindex nodes.coordinates permutation j w

/--
@isnad1 id=eq.0h3v.s4.b1e3572ebacd from=translated src=- shape=27cf56ec vocab=cfd6ed36
-/
lemma amplification_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    amplification (nodes.reindex permutation) = amplification nodes := by
  unfold amplification
  simp only [lebesgueFunction_reindex]

/--
@isnad1 id=iff.0h3v.s4.eb109dd88c0b from=translated src=- shape=82f667ad vocab=cf517bca
-/
lemma isMinimizer_rotate_iff (nodes : NodeFamily n) (rotation : Circle) :
    IsMinimizer (nodes.rotate rotation) ↔ IsMinimizer nodes := by
  simp only [IsMinimizer, amplification_rotate]

/--
@isnad1 id=iff.0h3v.s4.5cf5466c0ba1 from=translated src=- shape=054148bb vocab=08053279
-/
lemma isMinimizer_reindex_iff (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    IsMinimizer (nodes.reindex permutation) ↔ IsMinimizer nodes := by
  simp only [IsMinimizer, amplification_reindex]

/--
@isnad1 id=iff.0h3v.s4.6153b65d4075 from=translated src=- shape=82f667ad vocab=d8ebfdd5
-/
lemma isRegularRotation_rotate_iff (nodes : NodeFamily n) (rotation : Circle) :
    IsRegularRotation (nodes.rotate rotation) ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨r, permutation, h⟩
    refine ⟨rotation⁻¹ * r, permutation, ?_⟩
    intro i
    have hi := congrArg (fun z : Circle => rotation⁻¹ * z) (h i)
    change rotation⁻¹ * (rotation * nodes.point i) =
      rotation⁻¹ * (r * regularPoint n (permutation i)) at hi
    simpa only [inv_mul_cancel_left, mul_assoc] using hi
  · rintro ⟨r, permutation, h⟩
    refine ⟨rotation * r, permutation, ?_⟩
    intro i
    change rotation * nodes.point i = (rotation * r) * regularPoint n (permutation i)
    rw [h i, mul_assoc]

/--
@isnad1 id=iff.0h3v.s4.110c3bfe32e3 from=translated src=- shape=054148bb vocab=9fe0c6f4
-/
lemma isRegularRotation_reindex_iff (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    IsRegularRotation (nodes.reindex permutation) ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨rotation, p, h⟩
    refine ⟨rotation, permutation.symm.trans p, ?_⟩
    intro i
    have hi := h (permutation.symm i)
    change nodes.point (permutation (permutation.symm i)) =
      rotation * regularPoint n (p (permutation.symm i)) at hi
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using hi
  · rintro ⟨rotation, p, h⟩
    refine ⟨rotation, permutation.trans p, ?_⟩
    intro i
    exact h (permutation i)

end

end UnitCircleInterpolation
