/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Definitions
import Tengoku.Seed.Topology.Order.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary properties of the literal interpolation objective

This file proves interpolation at the nodes, continuity, and attainment of the supremum
over the entire unit circle. It does not assert the minimizer classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/--
@isnad1 id=injectiv.0h2v.s3.e31881768c35 from=translated src=- shape=cc4c7d09 vocab=2764adf3
-/
lemma NodeFamily.coordinates_injective (nodes : NodeFamily n) :
    Function.Injective nodes.coordinates :=
  Circle.coe_injective.comp nodes.injective

/--
@isnad1 id=eq.0h3v.s4.2e2080358087 from=translated src=- shape=1f9e19e1 vocab=e9a56d00
-/
@[simp] lemma NodeFamily.norm_coordinates (nodes : NodeFamily n) (j : Fin n) :
    ‖nodes.coordinates j‖ = 1 :=
  Circle.norm_coe _

/--
@isnad1 id=eq.1h3v.s4.2de23fbff90c from=translated src=- shape=bc6ed8cb vocab=c003372a
-/
lemma cardinal_self (z : Fin n → ℂ) (hz : Function.Injective z) (j : Fin n) :
    cardinal z j (z j) = 1 := by
  apply Finset.prod_eq_one
  intro k hk
  exact div_self (sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hz h).symm))

/--
@isnad1 id=eq.1h4v.s5.770312a3f380 from=translated src=- shape=45e1ca2a vocab=d4bffe4b
-/
lemma cardinal_other (z : Fin n → ℂ) {i j : Fin n} (hij : i ≠ j) :
    cardinal z j (z i) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  simp

/--
@isnad1 id=eq.1h3v.s4.2fda2e521875 from=translated src=- shape=c4114bd0 vocab=d955b665
-/
lemma lebesgueFunction_at_node (z : Fin n → ℂ) (hz : Function.Injective z) (i : Fin n) :
    lebesgueFunction z (z i) = 1 := by
  unfold lebesgueFunction
  rw [Finset.sum_eq_single i]
  · rw [cardinal_self z hz i, norm_one]
  · intro j hj hji
    rw [cardinal_other z (Ne.symm hji), norm_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/--
@isnad1 id=le.0h3v.s4.e604a36ec326 from=translated src=- shape=451ad09c vocab=b6cbd107
-/
lemma lebesgueFunction_nonneg (z : Fin n → ℂ) (w : ℂ) :
    0 ≤ lebesgueFunction z w :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/--
@isnad1 id=continuo.0h3v.s5.baeadd461a05 from=translated src=- shape=93394161 vocab=25a23de7
-/
lemma continuous_cardinal (z : Fin n → ℂ) (j : Fin n) :
    Continuous (cardinal z j) := by
  apply continuous_finsetProd
  intro k hk
  exact (continuous_id.sub continuous_const).div_const _

/--
@isnad1 id=continuo.0h2v.s4.994c10f94ebd from=translated src=- shape=c761b738 vocab=1b94b757
-/
lemma continuous_lebesgueFunction (z : Fin n → ℂ) :
    Continuous (lebesgueFunction z) := by
  apply continuous_finsetSum
  intro j hj
  exact (continuous_cardinal z j).norm

/--
@isnad1 id=continuo.0h2v.s6.1dd7bcf59a4c from=translated src=- shape=14c9a6a6 vocab=2c59a831
-/
lemma continuous_circle_lebesgueFunction (nodes : NodeFamily n) :
    Continuous (fun w : Circle => lebesgueFunction nodes.coordinates (w : ℂ)) :=
  (continuous_lebesgueFunction nodes.coordinates).comp continuous_subtype_val

/--
@isnad1 id=ex.0h2v.s7.3e492df25a3d from=translated src=- shape=ce76b615 vocab=e787bab9
-/
lemma exists_circle_maximum (nodes : NodeFamily n) :
    ∃ w : Circle, ∀ v : Circle,
      lebesgueFunction nodes.coordinates (v : ℂ) ≤
        lebesgueFunction nodes.coordinates (w : ℂ) := by
  obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set Circle).Nonempty from ⟨1, Set.mem_univ 1⟩)
    (continuous_circle_lebesgueFunction nodes).continuousOn
  exact ⟨w, fun v => hw (Set.mem_univ v)⟩

/--
@isnad1 id=bddabove.0h2v.s6.44d2a6f6e575 from=translated src=- shape=238859fe vocab=3a6b2fc2
-/
lemma bddAbove_circle_lebesgueFunction (nodes : NodeFamily n) :
    BddAbove (Set.range (fun w : Circle => lebesgueFunction nodes.coordinates (w : ℂ))) := by
  obtain ⟨w, hw⟩ := exists_circle_maximum nodes
  refine ⟨lebesgueFunction nodes.coordinates (w : ℂ), ?_⟩
  rintro y ⟨v, rfl⟩
  exact hw v

/--
@isnad1 id=le.0h3v.s6.53cdd08ca8c5 from=translated src=- shape=371dc2fb vocab=50644a43
-/
lemma le_amplification (nodes : NodeFamily n) (w : Circle) :
    lebesgueFunction nodes.coordinates (w : ℂ) ≤ amplification nodes :=
  le_csSup (bddAbove_circle_lebesgueFunction nodes) ⟨w, rfl⟩

/--
@isnad1 id=iff.0h3v.s6.90df2eb6e420 from=translated src=- shape=2b572ba1 vocab=50644a43
-/
lemma amplification_le_iff (nodes : NodeFamily n) (b : ℝ) :
    amplification nodes ≤ b ↔
      ∀ w : Circle, lebesgueFunction nodes.coordinates (w : ℂ) ≤ b := by
  constructor
  · intro h w
    exact (le_amplification nodes w).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨w, rfl⟩
    exact h w

/--
@isnad1 id=ex.0h2v.s6.8fe347b0a7ac from=translated src=- shape=cbed934f vocab=89e94f54
-/
lemma amplification_attained (nodes : NodeFamily n) :
    ∃ w : Circle, amplification nodes = lebesgueFunction nodes.coordinates (w : ℂ) := by
  obtain ⟨w, hw⟩ := exists_circle_maximum nodes
  exact ⟨w, le_antisymm ((amplification_le_iff nodes _).mpr hw)
    (le_amplification nodes w)⟩

/--
@isnad1 id=le.1h2v.s4.5be426c763c2 from=translated src=- shape=bc264ae3 vocab=ea2cd438
-/
lemma one_le_amplification (nodes : NodeFamily n) (hn : 0 < n) :
    1 ≤ amplification nodes := by
  let i : Fin n := ⟨0, hn⟩
  have h := le_amplification nodes (nodes.point i)
  change lebesgueFunction nodes.coordinates (nodes.coordinates i) ≤ amplification nodes at h
  rw [lebesgueFunction_at_node nodes.coordinates nodes.coordinates_injective i] at h
  exact h

end

end UnitCircleInterpolation
