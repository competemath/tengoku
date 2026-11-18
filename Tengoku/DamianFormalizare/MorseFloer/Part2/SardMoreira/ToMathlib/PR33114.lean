/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
public import Tengoku.Seed.Topology.EMetricSpace.Paracompact
public import Tengoku.Seed.Topology.Separation.CompletelyRegular
import Tengoku.Seed.Analysis.MeanInequalitiesPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A copy of a metric space with metric given by `d x y = dist x y ^ α`

Given a (pseudo) (extended) metric space `X` and a number `0 < α < 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
In this file we define `WithRPowDist X α hα₀ hα₁` to be a one-field structure wrapper around `X`
with metric given by this formula.

One of the reasons to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ α)`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali family in this context, we need to cover the set by products
`closedBall a (R ^ α) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/

@[expose] public section
namespace Tengoku.DamianFormalizare end Tengoku.DamianFormalizare open Tengoku.DamianFormalizare 
open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure.-/
@[ext]
structure _root_.Tengoku.DamianFormalizare.WithRPowDist (X : Type*) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) where
  /-- The value wrapped in `x : WithRPowDist X α hα₀ hα₁`.-/
  val : X

namespace Tengoku.DamianFormalizare.WithRPowDist

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

/-- The natural equivalence between `WithRPowDist X α hr₀ hr₁` and `X`.-/
@[simps -fullyApplied apply symm_apply]
def equiv (X : Type*) (α : ℝ) (hr₀ : 0 < α) (hr₁ : α ≤ 1) : WithRPowDist X α hr₀ hr₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.2h2v.s5.da52089a38ab from=translated src=- shape=96db0149 vocab=640992f9
-/
@[simp]
theorem val_comp_mk : (val : WithRPowDist X α hα₀ hα₁ → X) ∘ mk = id := rfl

/--
@isnad1 id=eq.2h2v.s6.ec341c48e451 from=translated src=- shape=07a70046 vocab=640992f9
-/
@[simp]
theorem mk_comp_val : (mk : X → WithRPowDist X α hα₀ hα₁) ∘ val = id := rfl

/--
@isnad1 id=eq.2h3v.s5.b0bb80352f9b from=translated src=- shape=9885a9d9 vocab=ede55639
-/
theorem image_mk_eq_preimage (s : Set X) :
    (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = val ⁻¹' s :=
  (equiv X α hα₀ hα₁).symm.image_eq_preimage_symm _

/--
@isnad1 id=eq.2h3v.s5.f91543b0a4bb from=translated src=- shape=57381654 vocab=ede55639
-/
theorem image_val_eq_preimage (s : Set (WithRPowDist X α hα₀ hα₁)) :
    val '' s = mk ⁻¹' s :=
  (equiv X α hα₀ hα₁).image_eq_preimage_symm _

/--
@isnad1 id=eq.2h3v.s6.cddb592c7e76 from=translated src=- shape=2a8a8c25 vocab=b2dcbc93
-/
@[simp]
theorem image_mk_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    mk '' (val '' s) = s :=
  (equiv X α hα₀ hα₁).symm_image_image _

/--
@isnad1 id=eq.2h3v.s5.e20cdb5139fe from=translated src=- shape=65960054 vocab=b2dcbc93
-/
@[simp]
theorem image_val_image_mk (s : Set X) : val '' (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = s :=
  (equiv X α hα₀ hα₁).image_symm_image _

/--
@isnad1 id=surjecti.2h2v.s5.fa36a36ae686 from=translated src=- shape=af2885cf vocab=69532ea8
-/
theorem surjective_val : Surjective (val : WithRPowDist X α hα₀ hα₁ → X) :=
  equiv _ _ _ _ |>.surjective

/--
@isnad1 id=surjecti.2h2v.s5.5497aaa797a2 from=translated src=- shape=dc08934d vocab=dbc36064
-/
theorem surjective_mk : Surjective (mk :  X → WithRPowDist X α hα₀ hα₁) :=
  equiv _ _ _ _ |>.symm |>.surjective

/--
@isnad1 id=injectiv.2h2v.s5.c8e7d6fd79ec from=translated src=- shape=dc08934d vocab=7a249cb2
-/
theorem injective_mk : Injective (mk : X → WithRPowDist X α hα₀ hα₁) := by
  simp [Injective]

/-!
### Topological space structure

The topology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section TopologicalSpace

variable [TopologicalSpace X]

/-- The topological space structure on `WithRPowDist X α _ _` is induced from the original space.-/
instance : TopologicalSpace (WithRPowDist X α hα₀ hα₁) := .induced WithRPowDist.val ‹_›

/--
@isnad1 id=continuo.2h2v.s5.180162fa6b14 from=translated src=- shape=e48e4955 vocab=08c8055b
-/
@[fun_prop]
theorem continuous_val : Continuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  continuous_induced_dom

/--
@isnad1 id=continuo.2h2v.s5.57983fb6e144 from=translated src=- shape=ec6931a8 vocab=f5861d7b
-/
@[fun_prop]
theorem continuous_mk : Continuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-- The natural homeomorphism between `WithRPowDist X α hα₀ hα₁` and `X`.-/
@[simps! -fullyApplied toEquiv apply symm_apply]
def homeomorph : WithRPowDist X α hα₀ hα₁ ≃ₜ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁

/-!
We copy some instances from the underlying space `X` to `WithRPowDist X α hα₀ hα₁`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it automatically.
-/

instance [T0Space X] : T0Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t0Space

instance [SecondCountableTopology X] : SecondCountableTopology (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

/-!
### Bornology

The bornology on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section Bornology

variable [Bornology X]

instance : Bornology (WithRPowDist X α hα₀ hα₁) := .induced val

open Bornology

/--
@isnad1 id=iff.2h3v.s6.cb4f0c45cb0d from=translated src=- shape=002437fa vocab=b06b2a2a
-/
@[simp]
theorem isBounded_image_val_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

/--
@isnad1 id=iff.2h3v.s6.0c7a9ec47b0d from=translated src=- shape=90c467f8 vocab=781e5fc5
-/
@[simp]
theorem isBounded_preimage_mk_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (mk ⁻¹' s) ↔ IsBounded s := by
  rw [← image_val_eq_preimage, isBounded_image_val_iff]

/--
@isnad1 id=iff.2h3v.s5.f9781f2e7baa from=translated src=- shape=c4fbb332 vocab=34dc7397
-/
@[simp]
theorem isBounded_image_mk_iff {s : Set X} :
    IsBounded (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_val_iff, image_val_image_mk]

/--
@isnad1 id=iff.2h3v.s5.a9287f05a9d0 from=translated src=- shape=178c48c8 vocab=2cd2a570
-/
@[simp]
theorem isBounded_preimage_val_iff {s : Set X} :
    IsBounded (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_mk_eq_preimage, isBounded_image_mk_iff]

end Bornology

/-!
### Uniform space structure

The uniform space structure on `WithRPowDist X α hα₀ hα₁` is induced from `X`.
-/

section UniformSpace

variable [UniformSpace X]

instance : UniformSpace (WithRPowDist X α hα₀ hα₁) :=
  UniformSpace.comap WithRPowDist.val ‹_›

/--
@isnad1 id=uniformc.2h2v.s5.9f21a57e66dd from=translated src=- shape=e48e4955 vocab=b9b468ea
-/
theorem uniformContinuous_val : UniformContinuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  uniformContinuous_comap

/--
@isnad1 id=uniformc.2h2v.s5.685afcc82347 from=translated src=- shape=ec6931a8 vocab=c776bf88
-/
theorem uniformContinuous_mk : UniformContinuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-
Define a UniformEquiv between this space and X.
-/
@[simps! toEquiv apply symm_apply]
def uniformEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  uniformContinuous_toFun := uniformContinuous_val
  uniformContinuous_invFun := uniformContinuous_mk

end UniformSpace

/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `edist x y = (edist x.val y.val) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/

section EDist

variable [EDist X]

instance : EDist (WithRPowDist X α hα₀ hα₁) where
  edist x y := edist x.val y.val ^ α

/--
@isnad1 id=eq.2h4v.s6.b3702608d063 from=translated src=- shape=c3694e2d vocab=6c87797d
-/
theorem edist_def (x y : WithRPowDist X α hα₀ hα₁) : edist x y = edist x.val y.val ^ α := rfl

/--
@isnad1 id=eq.2h4v.s6.5bc6df30e3b5 from=translated src=- shape=85019651 vocab=7c058252
-/
@[simp]
theorem edist_mk_mk (x y : X) : edist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = edist x y ^ α :=
  rfl

/--
@isnad1 id=eq.2h4v.s6.3d953885ff61 from=translated src=- shape=20f92c74 vocab=c3cfa593
-/
@[simp]
theorem edist_val_val (x y : WithRPowDist X α hα₀ hα₁) : edist x.val y.val = edist x y ^ α⁻¹ := by
  rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

open EMetric Metric

instance : PseudoEMetricSpace (WithRPowDist X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.val y.val z.val, ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

/--
@isnad1 id=eq.2h4v.s6.adb033b6ae7e from=translated src=- shape=5cb4f1cb vocab=deca590d
-/
@[simp]
theorem preimage_val_emetricBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

/--
@isnad1 id=eq.2h4v.s6.bfb707e8744f from=translated src=- shape=54c0422d vocab=aac97fd1
-/
@[simp]
theorem image_mk_emetricBall (x : X) (r : ℝ≥0∞) :
    mk '' eball x r = eball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricBall]

/--
@isnad1 id=eq.2h4v.s6.49bb5deef0de from=translated src=- shape=6ad8f1f2 vocab=805d9837
-/
@[simp]
theorem preimage_mk_emetricBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' eball x d = eball x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricBall, Set.image_preimage_eq _ surjective_mk, ENNReal.rpow_inv_rpow hα₀.ne']

/--
@isnad1 id=eq.2h4v.s6.ecb14b5ea00c from=translated src=- shape=d46ddcdf vocab=8359ee58
-/
@[simp]
theorem image_val_emetricBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' eball x d = eball x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricBall]

/--
@isnad1 id=eq.2h4v.s6.0f4c181757dc from=translated src=- shape=5cb4f1cb vocab=e6994b1d
-/
@[simp]
theorem preimage_val_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

/--
@isnad1 id=eq.2h4v.s6.072e0a829685 from=translated src=- shape=54c0422d vocab=7b5b7342
-/
@[simp]
theorem image_mk_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    mk '' closedEBall x r = closedEBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricClosedBall]

/--
@isnad1 id=eq.2h4v.s6.641664c76dc7 from=translated src=- shape=6ad8f1f2 vocab=002b10b6
-/
@[simp]
theorem preimage_mk_emetricClosedBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricClosedBall, Set.image_preimage_eq _ surjective_mk,
    ENNReal.rpow_inv_rpow hα₀.ne']

/--
@isnad1 id=eq.2h4v.s6.d05c3fe5bfdd from=translated src=- shape=d46ddcdf vocab=879b27be
-/
@[simp]
theorem image_val_emetricClosedBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' closedEBall x d = closedEBall x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricClosedBall]

/--
@isnad1 id=eq.2h3v.s6.289362023611 from=translated src=- shape=9c60df2d vocab=126ec48f
-/
@[simp]
theorem ediam_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) : ediam (val '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp [ediam_le_iff, ENNReal.rpow_inv_le_iff hα₀]

/--
@isnad1 id=eq.2h3v.s6.3eb41aa69e1a from=translated src=- shape=50c0b03d vocab=823fca11
-/
@[simp]
theorem ediam_preimage_mk (s : Set (WithRPowDist X α hα₀ hα₁)) :
    ediam (mk ⁻¹' s) = ediam s ^ α⁻¹ := by
  rw [← image_val_eq_preimage, ediam_image_val]

/--
@isnad1 id=eq.2h3v.s6.e48ae243f4e8 from=translated src=- shape=e79e5397 vocab=b27dcf26
-/
@[simp]
theorem ediam_preimage_val (s : Set X) :
    ediam (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _), ← ediam_preimage_mk,
    ← Set.preimage_comp, val_comp_mk, Set.preimage_id]

/--
@isnad1 id=eq.2h3v.s6.ec62c5486845 from=translated src=- shape=5ca060d7 vocab=65798bb0
-/
@[simp]
theorem ediam_image_mk (s : Set X) :
    ediam (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_mk_eq_preimage]

end PseudoEMetricSpace

instance [EMetricSpace X] : EMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _

/-!
### Distance and a (pseudo) metric space structure

Th extended distance on `WithRPowDist X α hα₀ hα₁`
is given by `dist x y = (dist x.val y.val) ^ α`.

If the original space is a (pseudo) metric space, then so is `WithRPowDist X α hα₀ hα₁`.
-/

instance [Dist X] : Dist (WithRPowDist X α hα₀ hα₁) where
  dist x y := dist x.val y.val ^ α

/--
@isnad1 id=eq.2h4v.s6.0bb437fbbb02 from=translated src=- shape=76ae6062 vocab=65a8e0b5
-/
@[simp]
theorem dist_mk_mk [Dist X] (x y : X) :
    dist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by rintro ⟨x⟩ ⟨y⟩; rw [dist_mk_mk]; positivity)
      (by
        rintro ⟨x⟩ ⟨y⟩
        rw [edist_mk_mk, dist_mk_mk, ← ENNReal.ofReal_rpow_of_nonneg, ← edist_dist] <;> positivity)
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_mk_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [dist_mk_mk, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_mk_mk, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

/--
@isnad1 id=eq.2h4v.s6.41e228522af5 from=translated src=- shape=a5ea4e11 vocab=75378ce0
-/
@[simp]
theorem dist_val_val (x y : WithRPowDist X α hα₀ hα₁) : dist x.val y.val = dist x y ^ α⁻¹ := by
  cases x; cases y
  rw [dist_mk_mk, Real.rpow_rpow_inv dist_nonneg hα₀.ne']

/--
@isnad1 id=eq.3h4v.s6.13eb5f192577 from=translated src=- shape=f22dfde6 vocab=3204616c
-/
@[simp]
theorem preimage_val_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

/--
@isnad1 id=eq.3h4v.s6.e8dfaa4afbde from=translated src=- shape=5cfc5483 vocab=e96f0e72
-/
@[simp]
theorem image_mk_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_ball x hr]

/--
@isnad1 id=eq.3h4v.s6.0a9336a9d312 from=translated src=- shape=baf5f71b vocab=cb518d95
-/
@[simp]
theorem preimage_mk_ball (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' ball x r = ball x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_ball _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

/--
@isnad1 id=eq.3h4v.s6.3250d9f61b8e from=translated src=- shape=1a38f153 vocab=bbf3be2b
-/
@[simp]
theorem image_val_ball (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' ball x r = ball x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_ball _ hr]

/--
@isnad1 id=eq.3h4v.s6.13b1b873ee35 from=translated src=- shape=f22dfde6 vocab=1dc709e0
-/
@[simp]
theorem preimage_val_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

/--
@isnad1 id=eq.3h4v.s6.7f09aedc38ef from=translated src=- shape=5cfc5483 vocab=68abfefe
-/
@[simp]
theorem image_mk_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_closedBall x hr]

/--
@isnad1 id=eq.3h4v.s6.39b7797febf6 from=translated src=- shape=baf5f71b vocab=2966acac
-/
@[simp]
theorem preimage_mk_closedBall (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_closedBall _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

/--
@isnad1 id=eq.3h4v.s6.61dc88944754 from=translated src=- shape=1a38f153 vocab=27a4d450
-/
@[simp]
theorem image_val_closedBall (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_closedBall _ hr]

end PseudoMetricSpace

instance [MetricSpace X] : MetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end Tengoku.DamianFormalizare.WithRPowDist
-- Tengoku: root names of this library moved to Tengoku.DamianFormalizare so they do not collide with other libraries (generated)
