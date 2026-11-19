/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerInverse
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changes of intrinsic corner coordinates

Replacing the middle line by the first line preserves volume. The remaining
change to last intercept and corner code has the exact two-factor Jacobian.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=measurep.0h1v.s10.9d4f59f28b63 from=translated src=- shape=326cf6c6 vocab=98bf7919
-/
theorem measurePreserving_swap_middle :
    MeasurePreserving (fun p : CornerCoordinates m ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      volume volume := by
  have h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
        EuclideanSpace ℝ (Fin m) ≃ᵐ EuclideanSpace ℝ (Fin m) ×
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))
      volume volume := volume_preserving_prodAssoc
  have hswap := Measure.measurePreserving_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))
  have hp := h₃.comp
    ((hswap.prod (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m))))).comp
      (h₃.symm MeasurableEquiv.prodAssoc))
  have h₄ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ×
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ≃ᵐ
        EuclideanSpace ℝ (Fin m) × (EuclideanSpace ℝ (Fin m) × (EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin m)))) volume volume := volume_preserving_prodAssoc
  simpa [Function.comp_def, Prod.map_def, MeasurableEquiv.prodAssoc, Measure.volume_eq_prod] using
    (h₄.symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).prod hp).comp h₄)

/-- First line and the remaining two slopes of a corner.-/
def cornerToFirst (a : ℝ) (p : CornerCoordinates m) : CornerCoordinates m :=
  (cornerFirst a p, (p.1.2, p.2.2))

/--
@isnad1 id=measurep.0h2v.s10.2739161a2f0d from=translated src=- shape=48dcd0a6 vocab=8cef5d4a
-/
theorem measurePreserving_cornerToFirst (a : ℝ) :
    MeasurePreserving (cornerToFirst (m := m) a) volume volume := by
  have hline := measurePreserving_lineCoordinates (m := m) a
  have hinv : MeasurePreserving (lineCoordinates (m := m) a).symm volume volume :=
    hline.symm (lineCoordinates a).toHomeomorph.toMeasurableEquiv
  have hi := (MeasurePreserving.id (volume : Measure (Line m)))
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    (lineAt a (atHeight a p.1) p.2.1, (p.1.2, p.2.2))) _ _
  simpa [Function.comp_def, Prod.map_def, lineCoordinates_apply, lineCoordinates_symm_apply,
    Measure.volume_eq_prod] using (hline.prod hi).comp
      (measurePreserving_swap_middle.comp (hinv.prod hi))

/--
@isnad1 id=eq.0h3v.s4.00a45e8f58dd from=translated src=- shape=72544f21 vocab=0861f000
-/
theorem codeJacobian_comm (a b : ℝ) : codeJacobian m a b = codeJacobian m b a := by
  simp [codeJacobian, abs_sub_comm]

/--
@isnad1 id=measurep.1h5v.s11.5cfbf57532bc from=translated src=- shape=0b09908a vocab=d67a5000
-/
theorem measurePreserving_cornerFiber {a b : ℝ} (hab : a ≠ b) (v w : EuclideanSpace ℝ (Fin m)) :
    MeasurePreserving (fun p : Line m ↦
      (v + (b - a) • p.1 - b • p.2, w + (a - b) • p.2)) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have hscale : MeasurePreserving (fun ξ : EuclideanSpace ℝ (Fin m) ↦ (b - a) • ξ) volume
      (codeJacobian m a b • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [codeJacobian] using
      Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin m)))
        (sub_ne_zero.mpr hab.symm)
  have hscale' : MeasurePreserving (fun ξ : EuclideanSpace ℝ (Fin m) ↦ (a - b) • ξ) volume
      (codeJacobian m a b • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [codeJacobian, abs_sub_comm] using
      Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin m))) (sub_ne_zero.mpr hab)
  have hfirst := (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).skew_product
    (g := fun ξ (x : EuclideanSpace ℝ (Fin m)) ↦ (v - b • ξ) + (b - a) • x)
    (by fun_prop) (ae_of_all _ fun ξ ↦ (hscale.add_left _ (v - b • ξ)).map_eq)
  have hs : MeasurePreserving (fun p : Line m ↦ (v + (b - a) • p.1 - b • p.2, p.2))
      volume (codeJacobian m a b • volume) := by
    simpa [Function.comp_def, Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.volume_eq_prod, sub_add_eq_add_sub] using
      Measure.measurePreserving_swap.comp (hfirst.comp Measure.measurePreserving_swap)
  have hlast : MeasurePreserving (fun p : Line m ↦ (p.1, w + (a - b) • p.2))
      volume (codeJacobian m a b • volume) := by
    simpa [Prod.map_def, Measure.prod_smul_right, Measure.volume_eq_prod] using
      (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).prod
        (hscale'.add_left _ w)
  simpa [Function.comp_def, smul_smul, pow_two] using (hlast.smul_measure _).comp hs

/-- First line, last-line intercept, and corner code.-/
def cornerCodeCoordinates (a b c κ : ℝ) (p : CornerCoordinates m) : CornerCoordinates m :=
  (cornerFirst a p, ((cornerLast b p).1, cornerCode a b c κ p))

/--
@isnad1 id=eq.0h4v.s8.2cd59d4de146 from=translated src=- shape=75f2472d vocab=7ad1edd1
-/
theorem cornerLast_fst_eq (a b : ℝ) (p : CornerCoordinates m) :
    (cornerLast b p).1 =
      atHeight a (cornerFirst a p) + (b - a) • p.1.2 - b • p.2.2 := by
  rw [atHeight_cornerFirst]
  unfold cornerLast lineAt atHeight
  module

/--
@isnad1 id=continuo.0h5v.s8.46fa3d69417d from=translated src=- shape=cf0abafa vocab=cdb8acbb
-/
theorem continuous_cornerCodeCoordinates (a b c κ : ℝ) :
    Continuous (cornerCodeCoordinates (m := m) a b c κ) := by
  unfold cornerCodeCoordinates cornerCode cornerFirst cornerLast lineAt atHeight
  fun_prop

/--
@isnad1 id=measurep.1h5v.s11.9a7b450676bb from=translated src=- shape=d48e6c7f vocab=d5eab19f
-/
theorem measurePreserving_cornerCodeCoordinates {a b : ℝ} (hab : a ≠ b) (c κ : ℝ) :
    MeasurePreserving (cornerCodeCoordinates (m := m) a b c κ) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have hs : MeasurePreserving (fun p : CornerCoordinates m ↦
      (p.1, (atHeight a p.1 + (b - a) • p.2.1 - b • p.2.2,
        κ • atHeight c p.1 + (a - b) • p.2.2))) volume
      (codeJacobian m a b ^ 2 • volume) := by
    have h := (MeasurePreserving.id (volume : Measure (Line m))).skew_product
      (g := fun g (s : Line m) ↦ (atHeight a g + (b - a) • s.1 - b • s.2,
        κ • atHeight c g + (a - b) • s.2))
      (by unfold atHeight; fun_prop)
      (ae_of_all _ fun g ↦ (measurePreserving_cornerFiber hab (atHeight a g)
        (κ • atHeight c g)).map_eq)
    simpa [Measure.prod_smul_right, Measure.volume_eq_prod] using h
  change MeasurePreserving (fun p : CornerCoordinates m ↦
    (cornerFirst a p, ((cornerLast b p).1, κ • atHeight c (cornerFirst a p) + (a - b) • p.2.2))) _ _
  simpa [Function.comp_def, cornerToFirst, cornerLast_fst_eq a b] using
    hs.comp (measurePreserving_cornerToFirst a)

/--
@isnad1 id=measurep.1h5v.s11.6a790119685a from=translated src=- shape=d3823876 vocab=55f0b266
-/
theorem measurePreserving_cornerCodeCoordinates_assoc {a b : ℝ} (hab : a ≠ b) (c κ : ℝ) :
    MeasurePreserving (fun p : CornerCoordinates m ↦
      ((cornerFirst a p, (cornerLast b p).1), cornerCode a b c κ p)) volume
      (codeJacobian m a b ^ 2 • volume) := by
  have ha : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (Line m × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin m) ≃ᵐ Line m ×
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))) volume volume :=
    volume_preserving_prodAssoc
  simpa [Function.comp_def, MeasurableEquiv.prodAssoc, cornerCodeCoordinates] using
    ((ha.symm MeasurableEquiv.prodAssoc).smul_measure (codeJacobian m a b ^ 2)).comp
      (measurePreserving_cornerCodeCoordinates hab c κ)

end NKBesicovitch.Projection
