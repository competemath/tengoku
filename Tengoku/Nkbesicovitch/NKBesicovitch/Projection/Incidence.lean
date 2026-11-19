/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Defs
public import Tengoku.Seed.MeasureTheory.Group.Prod
public import Tengoku.Seed.Topology.Algebra.Module.Equiv
public import Tengoku.Seed.Tactic.FunProp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Slice multiplicities and intrinsic pair incidence

At height `a`, a line is encoded by its position `w` and slope. Pairs with a
common position use `(w, ξ₁, ξ₂)` and the product measure in these coordinates,
not the ambient measure on two copies of line space.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The line at position `w` at height `a`, with slope `ξ`.-/
def lineAt (a : ℝ) (w ξ : EuclideanSpace ℝ (Fin m)) : Line m := (w - a • ξ, ξ)

/--
@isnad1 id=eq.0h5v.s7.3824523c0562 from=translated src=- shape=c0b16290 vocab=7540f5ea
-/
theorem atHeight_lineAt (a t : ℝ) (w ξ : EuclideanSpace ℝ (Fin m)) :
    atHeight t (lineAt a w ξ) = w + (t - a) • ξ := by
  simp [atHeight, lineAt, sub_smul, sub_add_eq_add_sub, add_sub_assoc]

/--
@isnad1 id=eq.0h3v.s4.077c27438064 from=translated src=- shape=28eee5f3 vocab=a072421c
-/
theorem lineAt_atHeight (a : ℝ) (g : Line m) : lineAt a (atHeight a g) g.2 = g := by
  simp [lineAt, atHeight]

/-- The volume-preserving change from position-slope coordinates to intercept-slope coordinates.-/
noncomputable def lineCoordinates (a : ℝ) : Line m ≃L[ℝ] Line m :=
  (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))).trans
    (((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin m))).skewProd
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin m)))
        (-a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)))).trans
        (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))))

/--
@isnad1 id=eq.0h3v.s11.8534576d41b5 from=translated src=- shape=1f164c10 vocab=69729c67
-/
theorem lineCoordinates_apply (a : ℝ) (p : Line m) :
    lineCoordinates a p = lineAt a p.1 p.2 := by
  simp [lineCoordinates, lineAt, sub_eq_add_neg]

/--
@isnad1 id=eq.0h3v.s11.43cd3056f531 from=translated src=- shape=764a32cd vocab=cad1cde8
-/
theorem lineCoordinates_symm_apply (a : ℝ) (g : Line m) :
    (lineCoordinates a).symm g = (atHeight a g, g.2) := by
  apply (lineCoordinates a).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, lineCoordinates_apply, lineAt_atHeight]

/--
@isnad1 id=measurep.0h2v.s11.5ca3659a7457 from=translated src=- shape=34c2a033 vocab=4ef5aeb8
-/
theorem measurePreserving_lineCoordinates (a : ℝ) :
    MeasurePreserving (lineCoordinates (m := m) a) volume volume := by
  change MeasurePreserving (fun p : Line m ↦ (p.1 + (-a) • p.2, p.2))
    (volume.prod volume) (volume.prod volume)
  have hs : MeasurePreserving (fun p : Line m ↦ (p.1, p.2 + (-a) • p.1))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin m)))).skew_product
      (by fun_prop)
      (ae_of_all _ fun ξ ↦ map_add_right_eq_self volume ((-a) • ξ))
  simpa [Function.comp_def] using
    Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)

/--
@isnad1 id=quasimea.0h2v.s9.899cdda48487 from=translated src=- shape=9457a37c vocab=4a3e69a4
-/
theorem quasiMeasurePreserving_atHeight (a : ℝ) :
    Measure.QuasiMeasurePreserving (atHeight (m := m) a) volume volume := by
  have h : MeasurePreserving (lineCoordinates (m := m) a).symm volume volume :=
    (measurePreserving_lineCoordinates a).symm (lineCoordinates a).toHomeomorph.toMeasurableEquiv
  change Measure.QuasiMeasurePreserving (fun g : Line m ↦ atHeight a g) _ _
  simpa [Function.comp_def, lineCoordinates_symm_apply, Measure.volume_eq_prod] using
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (EuclideanSpace ℝ (Fin m))))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))).comp h.quasiMeasurePreserving

/--
@isnad1 id=eq.1h3v.s9.3b43b3391c18 from=translated src=- shape=40c19d7a vocab=fff62a76
-/
theorem lintegral_lineAt (a : ℝ) {f : Line m → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, ∫⁻ ξ, f (lineAt a y ξ)) = ∫⁻ g, f g := by
  calc
    _ = ∫⁻ p, f (lineCoordinates a p) := by
      have hm : Measurable (fun p : Line m ↦ f (lineCoordinates a p)) :=
        hf.comp (lineCoordinates a).continuous.measurable
      simpa only [Measure.volume_eq_prod, lineCoordinates_apply] using
        (lintegral_prod (μ := (volume : Measure (EuclideanSpace ℝ (Fin m)))) (ν := volume)
          (fun p : Line m ↦ f (lineCoordinates a p)) hm.aemeasurable).symm
    _ = _ := (measurePreserving_lineCoordinates a).lintegral_comp hf

/-- Mass of the lines in a family passing through a specified point of a slice.-/
noncomputable def sliceMultiplicity (a : ℝ) (G : Set (Line m)) (w : EuclideanSpace ℝ (Fin m)) :
    ℝ≥0∞ :=
  volume ((lineAt a w) ⁻¹' G)

/--
@isnad1 id=measurab.1h3v.s7.f9303fe1f7a3 from=translated src=- shape=552be994 vocab=85355602
-/
theorem measurable_sliceMultiplicity (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    Measurable (sliceMultiplicity a G) := by
  change Measurable (fun w : EuclideanSpace ℝ (Fin m) ↦ volume ((lineAt a w) ⁻¹' G))
  have hm := measurable_measure_prodMk_left
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (hG.preimage (lineCoordinates a).continuous.measurable)
  have hc : ⇑(lineCoordinates (m := m) a) = fun p ↦ lineAt a p.1 p.2 :=
    funext (lineCoordinates_apply a)
  simpa only [hc, Set.preimage_preimage, Function.comp_def] using hm

/--
@isnad1 id=eq.1h3v.s9.ba73fb42585c from=translated src=- shape=4e916d75 vocab=77e86e51
-/
theorem lintegral_sliceMultiplicity (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    (∫⁻ w, sliceMultiplicity a G w) = volume G := by
  have he := Measure.prod_apply (μ := (volume : Measure (EuclideanSpace ℝ (Fin m)))) (ν := volume)
    (hG.preimage (lineCoordinates a).continuous.measurable)
  have hc : ⇑(lineCoordinates (m := m) a) = fun p ↦ lineAt a p.1 p.2 :=
    funext (lineCoordinates_apply a)
  calc
    (∫⁻ w, sliceMultiplicity a G w) = volume (lineCoordinates a ⁻¹' G) := by
      simpa only [sliceMultiplicity, hc, Set.preimage_preimage, Function.comp_def,
        Measure.volume_eq_prod] using he.symm
    _ = volume G := (measurePreserving_lineCoordinates a).measure_preimage hG.nullMeasurableSet

/-- Coordinates of two lines sharing a point at one height.-/
abbrev PairCoordinates (m : ℕ) := EuclideanSpace ℝ (Fin m) ×
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))

/-- The intrinsic incidence family of ordered pairs from `G` meeting at height `a`.-/
def pairFamily (a : ℝ) (G : Set (Line m)) : Set (PairCoordinates m) :=
  {p | lineAt a p.1 p.2.1 ∈ G ∧ lineAt a p.1 p.2.2 ∈ G}

/--
@isnad1 id=measurab.1h3v.s7.ffd41b9689f7 from=translated src=- shape=f607426c vocab=00a4097c
-/
theorem measurableSet_pairFamily (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    MeasurableSet (pairFamily a G) := by
  have h₁ : Measurable (fun p : PairCoordinates m ↦ lineAt a p.1 p.2.1) := by
    unfold lineAt
    fun_prop
  have h₂ : Measurable (fun p : PairCoordinates m ↦ lineAt a p.1 p.2.2) := by
    unfold lineAt
    fun_prop
  exact (hG.preimage h₁).inter (hG.preimage h₂)

/--
@isnad1 id=eq.1h3v.s10.489f1fe04546 from=translated src=- shape=98cea554 vocab=639113a9
-/
theorem volume_pairFamily (a : ℝ) {G : Set (Line m)} (hG : MeasurableSet G) :
    volume (pairFamily a G) = ∫⁻ w, sliceMultiplicity a G w ^ 2 := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_pairFamily a hG)]
  apply lintegral_congr
  intro w
  change volume (((lineAt a w) ⁻¹' G) ×ˢ ((lineAt a w) ⁻¹' G)) = _
  rw [Measure.volume_eq_prod, Measure.prod_prod, pow_two]
  rfl

end NKBesicovitch.Projection
