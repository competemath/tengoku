import Tengoku.Seed.Analysis.Convex.Jensen
import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Pow
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms root_concave` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms objective_channel_le` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Finite channels and the Hellinger objective

This file proves the finite Jensen/data-processing component used by the
linear-quotient comparison in the manuscript. It does not assume or prove
the trace-norm lifting or the main Hellinger conjecture.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Hellinger

noncomputable def root (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

/-- Normalized finite sum. Its probability interpretation requires a nonempty
index type; every Boolean cube used below is nonempty.-/
noncomputable def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ x, f x

noncomputable def objective {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  root (mean f) - mean (fun x => root (f x))

/--
@isnad1 id=eq.0h2v.s4.ca0c65c5bef0 from=translated src=- shape=5addde91 vocab=7fec4007
-/
theorem mean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    mean (fun _ : Ω => a) = a := by
  simp [mean, Fintype.card_ne_zero]

/--
@isnad1 id=eq.0h1v.s3.98515834817c from=translated src=- shape=cd419dad vocab=f3004e99
-/
theorem root_neg (t : ℝ) : root (-t) = root t := by
  simp [root]

/--
@isnad1 id=eq.0h2v.s4.a93c266bdd3b from=translated src=- shape=67aa5d67 vocab=51279537
-/
theorem mean_neg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean (fun x => -f x) = -mean f := by
  simp [mean, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h2v.s4.0d40883b34e1 from=translated src=- shape=6c68cda4 vocab=6f44ca3b
-/
theorem objective_neg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    objective (fun x => -f x) = objective f := by
  simp [objective, mean_neg, root_neg]

/-- A finite channel which preserves uniform measure. The first index is
the observed point and the second is the point being averaged.-/
structure UniformChannel (Ω : Type*) [Fintype Ω] where
  weight : Ω → Ω → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  row_sum : ∀ x, ∑ y, weight x y = 1
  column_sum : ∀ y, ∑ x, weight x y = 1

namespace UniformChannel

variable {Ω : Type*} [Fintype Ω]

noncomputable def apply (K : UniformChannel Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∑ y, K.weight x y * f y

/--
@isnad1 id=eq.0h3v.s5.dd36db95c56f from=translated src=- shape=d1d72538 vocab=ec0cb58a
-/
theorem apply_neg (K : UniformChannel Ω) (f : Ω → ℝ) :
    K.apply (fun x => -f x) = fun x => -K.apply f x := by
  funext x
  simp [apply, Finset.sum_neg_distrib]

/--
@isnad1 id=eq.0h3v.s5.fe2fa0d47145 from=translated src=- shape=403aaa8b vocab=cc5d398b
-/
theorem sum_apply (K : UniformChannel Ω) (f : Ω → ℝ) :
    ∑ x, K.apply f x = ∑ x, f x := by
  classical
  simp only [apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_mul, K.column_sum, one_mul]

/--
@isnad1 id=eq.0h3v.s4.29a29b2c905a from=translated src=- shape=73009a18 vocab=60138813
-/
theorem mean_apply (K : UniformChannel Ω) (f : Ω → ℝ) :
    mean (K.apply f) = mean f := by
  simp only [mean, K.sum_apply]

/--
@isnad1 id=mem.1h4v.s6.8ee45f97ffbd from=translated src=- shape=e13cdc35 vocab=aafdfd79
-/
theorem apply_mem_Icc (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (x : Ω) :
    K.apply f x ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · calc
      -1 = ∑ y, K.weight x y * (-1) := by simp [K.row_sum]
      _ ≤ K.apply f x := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hf y).1 (K.nonneg x y)
  · calc
      K.apply f x ≤ ∑ y, K.weight x y * 1 := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hf y).2 (K.nonneg x y)
      _ = 1 := by simp [K.row_sum]

/-- Convex functions decrease on average after an additional uniform channel.
@isnad1 id=le.2h4v.s6.10fbd1bfad19 from=translated src=- shape=e4857148 vocab=c52d82b7
-/
theorem convex_mean_contracts (K : UniformChannel Ω) (f : Ω → ℝ)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Φ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    mean (fun x => Φ (K.apply f x)) ≤ mean (fun x => Φ (f x)) := by
  have hpoint (x : Ω) : Φ (K.apply f x) ≤ K.apply (fun y => Φ (f y)) x := by
    simpa [apply, smul_eq_mul] using
      hΦ.map_sum_le (t := Finset.univ) (w := K.weight x) (p := f)
        (fun y _ => K.nonneg x y) (by simpa using K.row_sum x) (fun y _ => hf y)
  calc
    mean (fun x => Φ (K.apply f x)) ≤ mean (K.apply (fun y => Φ (f y))) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpoint x)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = mean (fun y => Φ (f y)) := K.mean_apply _

/--
@isnad1 id=le.2h4v.s6.f9c9119fac72 from=translated src=- shape=dbed268f vocab=05df8514
-/
theorem concave_mean_expands (K : UniformChannel Ω) (f : Ω → ℝ)
    (r : ℝ → ℝ) (hr : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) r)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    mean (fun x => r (f x)) ≤ mean (fun x => r (K.apply f x)) := by
  have hpoint (x : Ω) : K.apply (fun y => r (f y)) x ≤ r (K.apply f x) := by
    simpa [apply, smul_eq_mul] using
      hr.le_map_sum (t := Finset.univ) (w := K.weight x) (p := f)
        (fun y _ => K.nonneg x y) (by simpa using K.row_sum x) (fun y _ => hf y)
  calc
    mean (fun y => r (f y)) = mean (K.apply (fun y => r (f y))) := (K.mean_apply _).symm
    _ ≤ mean (fun x => r (K.apply f x)) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpoint x)
        (inv_nonneg.mpr (Nat.cast_nonneg _))

end UniformChannel

/--
@isnad1 id=concaveo.0h0v.s5.b4d394815ea8 from=translated src=- shape=65986746 vocab=77819332
-/
theorem root_concave : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) root := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxq : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hyq : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hq : a * (1 - x ^ 2) + b * (1 - y ^ 2) ≤ 1 - (a * x + b * y) ^ 2 := by
    have hpos := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
    have hident : 1 - (a * x + b * y) ^ 2 -
        (a * (1 - x ^ 2) + b * (1 - y ^ 2)) = a * b * (x - y) ^ 2 := by
      have hb' : b = 1 - a := by linarith
      rw [hb']
      ring
    linarith
  have hj := Real.strictConcaveOn_sqrt.concaveOn.2 hxq hyq ha hb hab
  change a * Real.sqrt (1 - x ^ 2) + b * Real.sqrt (1 - y ^ 2) ≤
    Real.sqrt (1 - (a * x + b * y) ^ 2)
  have hj' : a * Real.sqrt (1 - x ^ 2) + b * Real.sqrt (1 - y ^ 2) ≤
      Real.sqrt (a * (1 - x ^ 2) + b * (1 - y ^ 2)) := by
    simpa only [smul_eq_mul] using hj
  exact hj'.trans (Real.sqrt_le_sqrt hq)

/-- The bias term is preserved, so the full Hellinger objective contracts.
@isnad1 id=le.1h3v.s5.e5590db8da42 from=translated src=- shape=012ab37a vocab=0213b492
-/
theorem objective_channel_le {Ω : Type*} [Fintype Ω]
    (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    objective (K.apply f) ≤ objective f := by
  unfold objective
  rw [K.mean_apply]
  exact sub_le_sub_left (K.concave_mean_expands f root root_concave hf) _

end Hellinger
