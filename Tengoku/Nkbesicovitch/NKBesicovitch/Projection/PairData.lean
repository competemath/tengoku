/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Incidence
public import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar
public import Tengoku.Seed.MeasureTheory.Measure.WithDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates for the double-projection density

Keep the common point and replace each slope by its position at a specified
height. The two independent slope changes give the exact inverse Jacobian.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Common position and the two projected positions of an incident pair.-/
def pairData (a s t : ℝ) (p : PairCoordinates m) : PairCoordinates m :=
  (p.1, (p.1 + (s - a) • p.2.1, p.1 + (t - a) • p.2.2))

/-- The two positions used in the double-projection density.-/
def pairProjections (a s t : ℝ) (p : PairCoordinates m) : Line m :=
  (pairData a s t p).2

/--
@isnad1 id=eq.0h5v.s6.db344102b7df from=translated src=- shape=fb716cd6 vocab=34ce8a98
-/
theorem pairProjections_eq (a s t : ℝ) (p : PairCoordinates m) :
    pairProjections a s t p =
      (atHeight s (lineAt a p.1 p.2.1), atHeight t (lineAt a p.1 p.2.2)) := by
  simp [pairProjections, pairData, atHeight_lineAt]

/-- Recover the two slopes from the common position and the projected positions.-/
noncomputable def pairFromData (a s t : ℝ) (p : PairCoordinates m) : PairCoordinates m :=
  (p.1, ((s - a)⁻¹ • (p.2.1 - p.1), (t - a)⁻¹ • (p.2.2 - p.1)))

/--
@isnad1 id=eq.2h5v.s5.fcd3e5838dab from=translated src=- shape=f89a5db6 vocab=38f8e6c7
-/
theorem pairFromData_pairData {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    (p : PairCoordinates m) : pairFromData a s t (pairData a s t p) = p := by
  simp [pairFromData, pairData, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hs),
    inv_mul_cancel₀ (sub_ne_zero.mpr ht)]

/--
@isnad1 id=eq.2h5v.s5.554ef2905db8 from=translated src=- shape=f89a5db6 vocab=38f8e6c7
-/
theorem pairData_pairFromData {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    (p : PairCoordinates m) : pairData a s t (pairFromData a s t p) = p := by
  simp [pairFromData, pairData, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hs),
    mul_inv_cancel₀ (sub_ne_zero.mpr ht)]

/--
@isnad1 id=eq.2h5v.s5.0da72abf4d7b from=translated src=- shape=16b19328 vocab=c391d4ad
-/
theorem pairProjections_pairFromData {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a)
    (p : PairCoordinates m) : pairProjections a s t (pairFromData a s t p) = p.2 :=
  congrArg Prod.snd (pairData_pairFromData hs ht p)

/-- The inverse Jacobian of the two slope changes.-/
noncomputable def pairJacobian (m : ℕ) (a s t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |((s - a) ^ m)⁻¹| * ENNReal.ofReal |((t - a) ^ m)⁻¹|

/--
@isnad1 id=continuo.0h4v.s7.214a4f981eff from=translated src=- shape=91cb3c49 vocab=22d50dfd
-/
theorem continuous_pairData (a s t : ℝ) : Continuous (pairData (m := m) a s t) := by
  unfold pairData
  fun_prop

/--
@isnad1 id=continuo.0h4v.s7.30e34edd650e from=translated src=- shape=ebcfe9f3 vocab=73a3e637
-/
theorem continuous_pairProjections (a s t : ℝ) :
    Continuous (pairProjections (m := m) a s t) :=
  (continuous_pairData a s t).snd

/--
@isnad1 id=continuo.0h4v.s7.e3ec9e76a831 from=translated src=- shape=91cb3c49 vocab=c46dbba7
-/
theorem continuous_pairFromData (a s t : ℝ) : Continuous (pairFromData (m := m) a s t) := by
  unfold pairFromData
  fun_prop

/--
@isnad1 id=measurep.2h4v.s11.c7fc5417ebc2 from=translated src=- shape=2365190c vocab=903e1f51
-/
theorem measurePreserving_pairData {a s t : ℝ} (hs : s ≠ a) (ht : t ≠ a) :
    MeasurePreserving (pairData (m := m) a s t) volume (pairJacobian m a s t • volume) := by
  change MeasurePreserving (fun p : PairCoordinates m ↦
    (p.1, (p.1 + (s - a) • p.2.1, p.1 + (t - a) • p.2.2))) _ _
  have hscale (r : ℝ) (hr : r ≠ 0) :
      MeasurePreserving (fun ξ : EuclideanSpace ℝ (Fin m) ↦ r • ξ) volume
        (ENNReal.ofReal |(r ^ m)⁻¹| • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa using Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin m))) hr
  have hfiber (w : EuclideanSpace ℝ (Fin m)) :
      MeasurePreserving (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) ↦
        (w + (s - a) • p.1, w + (t - a) • p.2)) volume
        (pairJacobian m a s t • volume) := by
    have hp := ((hscale (s - a) (sub_ne_zero.mpr hs)).add_left _ w).prod
      ((hscale (t - a) (sub_ne_zero.mpr ht)).add_left _ w)
    simpa [pairJacobian, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.volume_eq_prod, mul_comm, Prod.map_def] using hp
  have h := (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).skew_product
    (g := fun w (p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ↦ (w + (s - a) • p.1,
      w + (t - a) • p.2))
    (by fun_prop) (ae_of_all _ fun w ↦ (hfiber w).map_eq)
  simpa [Measure.prod_smul_right, Measure.volume_eq_prod] using h

end NKBesicovitch.Projection
