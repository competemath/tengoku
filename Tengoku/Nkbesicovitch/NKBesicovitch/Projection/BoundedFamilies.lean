/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Incidence
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Parallel
public import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.Finite
public import Tengoku.Seed.Order.ConditionallyCompleteLattice.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite masses of bounded line families

The projection estimate is stated for bounded Borel line families. Boundedness
also controls projection images and intrinsic incidence pairs, justifying the
finite real quantities and divisions in the amplification argument.
-/

public section

open MeasureTheory Set Bornology
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/--
@isnad1 id=isbounde.1h3v.s6.33b92ffc20c7 from=translated src=- shape=fe7645fc vocab=5a98071d
-/
theorem isBounded_projection (t : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (atHeight t '' G) := by
  let f : Line m →L[ℝ] EuclideanSpace ℝ (Fin m) := ContinuousLinearMap.fst ℝ
    (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) +
    t • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m))
  exact f.lipschitzWith.isBounded_image hG

/--
@isnad1 id=isbounde.1h3v.s7.75e0aeecae2c from=translated src=- shape=f607426c vocab=ab818bea
-/
theorem isBounded_pairFamily (a : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    IsBounded (pairFamily a G) := by
  apply ((isBounded_projection a hG).prod (hG.image_snd.prod hG.image_snd)).subset
  intro p hp
  refine ⟨⟨lineAt a p.1 p.2.1, hp.1, ?_⟩,
    ⟨lineAt a p.1 p.2.1, hp.1, rfl⟩, ⟨lineAt a p.1 p.2.2, hp.2, rfl⟩⟩
  simp [atHeight_lineAt]

/--
@isnad1 id=ne.1h3v.s8.2d6752421927 from=translated src=- shape=668aff0c vocab=7532939b
-/
theorem volume_projection_ne_top (t : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (atHeight t '' G) ≠ ∞ := (isBounded_projection t hG).measure_lt_top.ne

/--
@isnad1 id=ne.1h3v.s9.85da35fa19b8 from=translated src=- shape=fe1c8054 vocab=2db51e34
-/
theorem volume_pairFamily_ne_top (a : ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    volume (pairFamily a G) ≠ ∞ := (isBounded_pairFamily a hG).measure_lt_top.ne

/--
@isnad1 id=ne.1h2v.s6.7fd93126a27f from=translated src=- shape=290d3c9d vocab=953e589a
-/
theorem parallelMultiplicity_ne_top {G : Set (Line m)} (hG : IsBounded G) :
    parallelMultiplicity G ≠ ∞ :=
  ne_top_of_le_ne_top (volume_projection_ne_top 0 hG) (parallelMultiplicity_le_projection G 0)

/--
@isnad1 id=ne.1h3v.s6.8801c950f209 from=translated src=- shape=10978b65 vocab=abb5e3b0
-/
theorem sliceSize_ne_top (Γ : Finset ℝ) {G : Set (Line m)} (hG : IsBounded G) :
    sliceSize Γ G ≠ ∞ := by
  simpa only [sliceSize, iSup_subtype] using
    (iSup_ne_top fun t : Γ ↦ volume_projection_ne_top t hG)

end NKBesicovitch.Projection
