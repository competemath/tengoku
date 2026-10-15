/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import Tengoku.LeanPool.LeanPool.Monsky.Square
public import Tengoku

/-!
# LeanPool.Monsky.TriangleCorollary

Imported Lean Pool material for `LeanPool.Monsky.TriangleCorollary`.
-/

@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "Triangle" => Fin 3 → ℝ²
local notation "Segment" => Fin 2 → ℝ²

open BigOperators
open Finset

/-I think that the most important subpart of this corollary is to show that the volume/area
of the triangles must add up to one. Measure theory tells us that the area of a disjoint union is
the sum of the areas. However, in order to apply this, we first need to that both that the `true'
area
of a triangle corresponds to the version of area in Monsky's theorem. Secondly, we need that the
sets we work with are measurable.

To show that the true area is indeed the determinant area, we start by proving that the open hull of
the
 `unit triangle' has volume 1/2, where this triangle is given by
((0,0),(1,0)(0,1)). From this we calculate the volumes of the other triangles, using the fact that
the volume of an object is invariant under translation and scale with the determinant of a linear
transformation.

For the measurability we do something similar: we show that the unit triangle is measurable, then we
show that any nondegenerate triangle is a preimage of a measurable function of the open hull of
the unit triangle. For degenerate triangles, we use that they have measure zero, and are thus
null-measurable, which is a weaker statement but sufficient for our result (They are actually
measurable
but this is probably quite annoying to show)-/

open MeasureTheory

--We start with the definition of the unit triangle

/-- The measurable equivalence `ℝ² ≃ᵐ ℝ × ℝ` unfolding a Euclidean plane vector to a pair. -/
noncomputable def idMapEquiv : ℝ² ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- The underlying function of `idMapEquiv`. -/
noncomputable def idMap : ℝ² → ℝ × ℝ := idMapEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μa : Measure α} {μb : Measure β} in
/--
@isnad1 id=eq.1h6v.s6.acd31942533c from=translated src=- shape=1c943d6d vocab=abb99986
-/
theorem measure_image_equiv {f : α ≃ᵐ β} (hf : MeasurePreserving f μa μb) (s : Set α) :
    μa s = μb (f '' s) := by
  simpa using hf.measure_preimage_equiv (f '' s)

/--
@isnad1 id=eq.0h1v.s9.553e526bce7f from=translated src=- shape=8061e9d1 vocab=3fecdf95
-/
theorem map_pres (X : Set ℝ²) : volume X = volume (idMap '' X) :=
  measure_image_equiv (f := idMapEquiv)
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)) X

/-- `idMap` sends a Euclidean plane vector to the pair of its coordinates.
@isnad1 id=eq.0h1v.s7.c7808f42dc67 from=translated src=- shape=66ce1243 vocab=7fcdf33b
-/
@[simp] lemma idMap_apply (x : ℝ²) : idMap x = (x 0, x 1) := rfl

/-- The unit triangle with vertices `(0,0)`, `(1,0)` and `(0,1)`. -/
def unitTriangle : Triangle := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
/--
@isnad1 id=eq.0h0v.s6.280b38744b18 from=translated src=- shape=20141c89 vocab=ccb37b99
-/
lemma unitTriangle_def : unitTriangle = fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1) := by rfl

/-- The lower boundary function (constantly zero) of the unit triangle region. -/
def lower : ℝ → ℝ := 0
/-- The upper boundary function `x ↦ 1 - x` of the unit triangle region. -/
def upper : ℝ → ℝ := fun x ↦ 1 - x

/--
@isnad1 id=eq.0h0v.s5.612112a8ebb5 from=translated src=- shape=af590187 vocab=aeee7fb5
-/
theorem unit_is_unit_in_prod
    : idMap '' (openHull unitTriangle) = regionBetween lower upper (Set.Ioc 0 1) := by
  ext x
  constructor <;>
    unfold regionBetween openHull openSimplex lower upper unitTriangle <;> intro hx <;>
    simp only [idMap_apply, Fin.isValue, Set.mem_image, Set.mem_ofPred_eq,
      exists_exists_and_eq_and, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Set.mem_Ioc, Set.mem_Ioo, Pi.zero_apply] at *
  · rcases hx with ⟨a, ⟨ha, ha''⟩, ha'⟩
    rw [Fin.sum_univ_three] at ha'' ha'
    rw [←ha']
    simp [Fin.sum_univ_three, v] at *
    constructor <;> constructor <;> linarith [ha 0, ha 1, ha 2]
  · use ![1 - x.1 - x.2, x.1, x.2]
    rcases hx with ⟨⟨⟩, ⟨⟩⟩
    constructor
    · constructor
      · intro i
        fin_cases i <;> simp <;> linarith
      · rw [Fin.sum_univ_three]
        simp []
        ring
    · simp only [Fin.sum_univ_three, v]
      simp

/--
@isnad1 id=eq.0h0v.s5.746c4fb82a76 from=translated src=- shape=c3990f7b vocab=00c51c28
-/
theorem unit_in_prod_is_unit
    : idMap⁻¹' (regionBetween lower upper (Set.Ioc 0 1)) = openHull unitTriangle
  := (Set.preimage_eq_iff_eq_image (MeasurableEquiv.bijective idMapEquiv)).mpr
      unit_is_unit_in_prod.symm

-- Then we have the statement that the open hull of the unit triangle has the right area, plus we
-- add the statement that it is measurable
/--
@isnad1 id=eq.0h0v.s9.1554c54a1ab7 from=translated src=- shape=e5cbeec7 vocab=d24e95d5
-/
theorem volume_open_unitTriangle : (MeasureTheory.volume (openHull unitTriangle)) = 1/2 := by
  have xyz : ∀ x ∈ Set.Ioc 0 1, lower x ≤ upper x := by
    intro x
    simp [upper, lower]
  have integ : IntegrableOn lower (Set.Ioc 0 1) := by unfold lower; exact integrableOn_zero
  have integ' : IntegrableOn upper (Set.Ioc 0 1) :=
    MeasureTheory.Integrable.sub (integrable_const 1)
      (intervalIntegral.intervalIntegrable_id (a := 0) (b := 1)).1
  suffices  ∫ (x : ℝ) in (0 : ℝ)..1, upper x = 1/2 by
    calc
      MeasureTheory.volume (openHull unitTriangle)
          = MeasureTheory.volume (regionBetween lower upper (Set.Ioc 0 1 : Set ℝ)) := by
            rw [map_pres (openHull unitTriangle), unit_is_unit_in_prod]
        _ = ENNReal.ofReal (∫ (x : ℝ) in (Set.Ioc 0 1), upper x - lower x) :=
            volume_regionBetween_eq_integral integ integ' measurableSet_Ioc xyz
        _ = ENNReal.ofReal (∫ (x : ℝ) in (0 : ℝ)..1, upper x) := by
            simp [lower, sub_zero, intervalIntegral.integral_of_le]
        _ = 1/2 := by rw [this, ENNReal.ofReal_div_of_pos] <;> norm_num
  unfold upper
  rw [intervalIntegral.integral_sub] <;> simp
  norm_num

/--
@isnad1 id=eq.0h0v.s9.e2bdff3af6f0 from=translated src=- shape=9f92a63b vocab=626f91da
-/
theorem volume_open_unitTriangle1 : (MeasureTheory.volume (openHull unitTriangle)).toReal = 1/2
    := by
  rw [volume_open_unitTriangle]
  norm_num

/--
@isnad1 id=measurab.0h0v.s6.d4bf44c73ebc from=translated src=- shape=d2b7d05a vocab=3c7f1464
-/
theorem measurable_unitTriangle : MeasurableSet (openHull unitTriangle) := by
  rw [←unit_in_prod_is_unit]
  apply MeasurableEquiv.measurable_toFun
  refine measurableSet_regionBetween (by unfold lower; exact measurable_zero) ?_ measurableSet_Ioc
  exact Measurable.sub measurable_const (fun ⦃t⦄ a ↦ a)

-- Now that we have this, we want to show that the areas can be nicely transformed, for which we use
-- tthis theorem
/--
@isnad1 id=eq.0h2v.s12.61b68083f636 from=translated src=- shape=8ca97687 vocab=c77f452e
-/
theorem area_lin_map (L : ℝ² →ₗ[ℝ] ℝ²) (A : Set ℝ²) : MeasureTheory.volume (Set.image L A)
    = (ENNReal.ofReal (abs ( LinearMap.det L ))) * (MeasureTheory.volume (A)) := by
  exact MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume L A

-- We have something similar for translations, but we first have to give a definition of a
-- translation :)
/-- Translation of the plane by a fixed vector `a`. -/
def translation (a : ℝ²) : (ℝ² → ℝ²) := fun x ↦ x + a

/--
@isnad1 id=eq.0h2v.s10.275ffb9c73ad from=translated src=- shape=d51430d1 vocab=2eb366db
-/
theorem area_translation (a : ℝ²) (A : Set ℝ²)
    :  MeasureTheory.volume (Set.image (translation a) A) = MeasureTheory.volume (A) :=   by
  unfold translation
  simp

-- If we want to use these two theorems we need the proof that a generic triangle is given by a
-- linear transform and the translation. For this we show that a linear transformation commutes with
-- the open hull operation, in which we use the following lemma
/--
@isnad1 id=eq.0h4v.s10.c3ba02e3503c from=translated src=- shape=112c0395 vocab=ce298d3c
-/
lemma lincom_commutes (L : ℝ² →ₗ[ℝ] ℝ²) {n : ℕ} (a : Fin n → ℝ) (f : Fin n → ℝ²)
    : ∑ i : Fin n, a i • L (f i)  =L (∑ i : Fin n, (a i) • (f i)) := by
  simp_all

/--
@isnad1 id=eq.0h3v.s10.b05f54ad9927 from=translated src=- shape=5fb8a19a vocab=fa8b2c74
-/
theorem openHull_lin_trans (L : ℝ² →ₗ[ℝ] ℝ²) {n : ℕ} (f : (Fin n → ℝ²))
    : openHull (L ∘ f ) = Set.image L (openHull f) := by
  unfold openHull
  rw[ ← Set.image_comp] -- for some reason repeat rw does not work here
  simp_all

--Now also for the closed version, whose proof is almost identical
/--
@isnad1 id=eq.0h3v.s10.637df2f6d534 from=translated src=- shape=5fb8a19a vocab=7b587825
-/
theorem closedHull_lin_trans (L : ℝ² →ₗ[ℝ] ℝ²) {n : ℕ} (f : (Fin n → ℝ²))
    : closedHull (L ∘ f ) = Set.image L (closedHull f) := by
  unfold closedHull
  rw[ ← Set.image_comp] -- for some reason repeat rw does not work here
  simp_all

--Again we have a similar lemma
/--
@isnad1 id=eq.1h4v.s9.15853a797ba5 from=translated src=- shape=ad924a01 vocab=9bf095c5
-/
lemma aux_for_translation {n : ℕ} {f : Fin n → ℝ²} {a : Fin n → ℝ} {b : ℝ²}
    (h1 : a ∈ openSimplex n) : ∑ i : Fin n, a i • (f i + b) = ∑ i : Fin n, a i • f i + b := by
  have h4 : b = ∑ i : Fin n, a i • b := by rw [← sum_smul, h1.2, one_smul]
  nth_rewrite 2 [h4]
  rw [← sum_add_distrib]
  exact Fintype.sum_congr _ _ fun i ↦ DistribSMul.smul_add (a i) (f i) b

--Most of the proof of openHull_lin_trans now gets copied
/--
@isnad1 id=eq.0h3v.s6.28fd658436b7 from=translated src=- shape=66104286 vocab=16ce92e7
-/
theorem translation_commutes {n : ℕ} (f : (Fin n → ℝ²)) (b : ℝ²)
    : openHull ( (translation b) ∘ f) = Set.image (translation b) (openHull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  unfold openHull
  rw[ ← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp; rwa[← aux_for_translation h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp; rwa[ aux_for_translation h1]⟩

-- And the version for the closed hull, that needs an adapted different lemma
/--
@isnad1 id=eq.1h4v.s9.25b77036d42a from=translated src=- shape=ad924a01 vocab=a427a598
-/
theorem aux_for_translation_closed {n : ℕ} {f : Fin n → ℝ²} {a : Fin n → ℝ} {b : ℝ²}
    (h1 : a ∈ closedSimplex n) :
    ∑ i : Fin n, a i • (f i + b) = ∑ i : Fin n, a i • f i + b := by
  have h4 : b = ∑ i : Fin n, a i • b := by rw [← sum_smul, h1.2, one_smul]
  nth_rewrite 2 [h4]
  rw [← sum_add_distrib]
  exact Fintype.sum_congr _ _ fun i ↦ DistribSMul.smul_add (a i) (f i) b

/--
@isnad1 id=eq.0h3v.s6.18d08d95b8aa from=translated src=- shape=66104286 vocab=55149b90
-/
theorem translation_commutes_closed {n : ℕ} (f : (Fin n → ℝ²)) (b : ℝ²)
    : closedHull ( (translation b) ∘ f) = Set.image (translation b) (closedHull f) := by
  have htrans : translation b = fun x ↦ x + b := by rfl
  unfold closedHull
  rw[← Set.image_comp]
  rw[htrans] at *
  ext x
  constructor
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp; rwa[← aux_for_translation_closed h1]⟩
  · rintro ⟨ a ,h1 , h2⟩
    dsimp at h2
    exact ⟨ a, h1, by dsimp; rwa[ aux_for_translation_closed h1]⟩

-- Now we explicitly give the translation and linear map that so that the unit triangle gets mapped
-- unto the triangle
--First, we make explicit that our basis is the standard basis
/-- The standard basis of the Euclidean plane used throughout. -/
noncomputable def ourBasis : Module.Basis (Fin 2) ℝ ℝ² :=  PiLp.basisFun 2 ℝ (Fin 2)
/-- The standard orthonormal basis of the Euclidean plane. -/
noncomputable def ourBasisOrtho
    : OrthonormalBasis (Fin 2) ℝ ℝ² :=   EuclideanSpace.basisFun (Fin 2) ℝ

/-- The first standard orthonormal basis vector of the plane is `(1, 0)`.
@isnad1 id=eq.0h0v.s8.333654769491 from=translated src=- shape=fcfb87a3 vocab=798a88f4
-/
theorem ourBasisOrtho_zero : (ourBasisOrtho 0 : ℝ²) = !₂[1, 0] := by
  change (EuclideanSpace.basisFun (Fin 2) ℝ) 0 = !₂[1, 0]
  rw [EuclideanSpace.basisFun_apply]
  ext j; fin_cases j <;> simp

/-- The second standard orthonormal basis vector of the plane is `(0, 1)`.
@isnad1 id=eq.0h0v.s8.912574bd7757 from=translated src=- shape=fcfb87a3 vocab=798a88f4
-/
theorem ourBasisOrtho_one : (ourBasisOrtho 1 : ℝ²) = !₂[0, 1] := by
  change (EuclideanSpace.basisFun (Fin 2) ℝ) 1 = !₂[0, 1]
  rw [EuclideanSpace.basisFun_apply]
  ext j; fin_cases j <;> simp

--This map tells us how the basis elements should be mapped
/-- The pair of edge vectors of a triangle from its first vertex. -/
noncomputable def basisTransform (T : Triangle)
    : (Fin 2 → ℝ²) := (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0))

--And then Lean knows how to make a linear map from this
/-- The linear map sending the standard basis to a triangle's edge vectors. -/
noncomputable def linearTransform (T : Triangle) := ourBasis.constr ℝ (basisTransform T)

--This is our translation
/-- Translation by the first vertex of a triangle. -/
def triangleTranslation (T : Triangle) := translation (T 0)

-- And then some API which I am actually not sure is required
/--
@isnad1 id=eq.0h0v.s7.e0b86d91912e from=translated src=- shape=f4273c5e vocab=9863f7b3
-/
theorem ourBasis_def : ourBasis = PiLp.basisFun 2 ℝ (Fin 2) := by rfl
/--
@isnad1 id=eq.0h1v.s8.3c62afe3985c from=translated src=- shape=3a0136c3 vocab=09aa7d5c
-/
theorem basisTransform_def (T : Triangle)
    : basisTransform T =  (fun | 0 => (T 1 - T 0) | 1 => (T 2 -T 0)) := by rfl
/--
@isnad1 id=eq.0h1v.s12.81310e0d5b29 from=translated src=- shape=e52b8516 vocab=9e8785f3
-/
theorem linearTransform_def (T : Triangle)
    : linearTransform T =  ourBasis.constr ℝ (basisTransform T) := by rfl
/--
@isnad1 id=eq.0h1v.s5.71ffe4bbe967 from=translated src=- shape=86c3c64e vocab=6090d4a4
-/
theorem triangleTranslation_def (T : Triangle)
    : triangleTranslation T =  translation (T 0) := by rfl

-- This theorem tells us that these maps indeed do the trick, for which we use translation_commutes
-- and openHull_lin_trans to show that it is sufficient to show that the points of the unit
-- triangle gets mapped to the triangle (instead of the entirety of the open hull)
/--
@isnad1 id=eq.0h1v.s9.43730f23549e from=translated src=- shape=f88315c5 vocab=169e8593
-/
theorem unitTriangle_to_triangle (T : Triangle) : Set.image (triangleTranslation T)
    (Set.image (linearTransform T) (openHull unitTriangle)) = openHull T:= by
  have h1 : triangleTranslation T = translation (T 0) := by rfl
  let f : (Fin 3 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0) | 2 => (v 0 1)
  have hunitTriangle : unitTriangle = f :=by rfl
  rw[hunitTriangle, h1]
  have h2 : openHull (linearTransform T ∘ f )= ⇑(linearTransform T) '' openHull f :=
    openHull_lin_trans (linearTransform T) f
  rw[← h2]
  --rw[← openHull_lin_trans (linearTransform T) f] Why doesnt this work!??
  rw[← translation_commutes]
  apply congrArg
  -- This part of the proof says that the linear transformation and translation of the unit triangle
  -- give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;>  simp[translation, linearTransform, basisTransform,f, ourBasis]

-- We are allmost ready to show that the volume of triangles scale the way we want them to, but we
-- just need a silly lemma first
/--
@isnad1 id=eq.0h0v.s4.c7fd4066a0c5 from=translated src=- shape=7e54e863 vocab=dea55dc8
-/
lemma half_is_half : (2⁻¹ : ENNReal) = ENNReal.ofReal (2⁻¹ : ℝ ) := by
  simp_all

/--
@isnad1 id=eq.0h1v.s9.e97afd0d9816 from=translated src=- shape=bf74ac0c vocab=61281c8e
-/
theorem volume_open_triangle' (T : Triangle)
    : (MeasureTheory.volume (openHull T)) =  ENNReal.ofReal (|det (T : Triangle)|/2) := by
  rw[← unitTriangle_to_triangle T ,triangleTranslation_def]
  rw[ area_translation, area_lin_map, volume_open_unitTriangle]
  rw[← Matrix.toLin_toMatrix ourBasis ourBasis  ( linearTransform T ) ]
  rw[LinearMap.det_toLin ourBasis ((LinearMap.toMatrix ourBasis ourBasis) (linearTransform T))]
  rw[Matrix.det_fin_two]
  rw[linearTransform_def, basisTransform_def, ourBasis_def ]
  unfold det
  repeat rw[LinearMap.toMatrix_apply]
  simp only [Fin.isValue, PiLp.basisFun_apply, Module.Basis.constr_apply_fintype,
    PiLp.basisFun_equivFun, WithLp.linearEquiv_apply, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, WithLp.addEquiv_apply, PiLp.single_apply, ite_smul, one_smul, zero_smul,
    sum_ite_eq', mem_univ, ↓reduceIte, map_sub, Finsupp.coe_sub, Pi.sub_apply, PiLp.basisFun_repr,
    one_div]
  rw[half_is_half]
  have h2 : ((0:ℝ) ≤ 2⁻¹ ) := by
    norm_num
  rw[← ENNReal.ofReal_mul' h2]
  ring_nf

-- One version of this statement in Real numbers, the other in ENNReal, in terms of proof efficiency
-- these probably should not be completely seperate proofs
/--
@isnad1 id=eq.0h1v.s9.e8f34ab4eb79 from=translated src=- shape=8179e0f7 vocab=553f9c54
-/
theorem volume_open_triangle (T : Triangle)
    : (MeasureTheory.volume (openHull T)).toReal =  (|det (T : Triangle)|/2):= by
  rw [volume_open_triangle', ENNReal.toReal_ofReal_eq_iff]
  exact div_nonneg (abs_nonneg _) (by norm_num)

-- Now that we know the volume of open triangles, we also want to know the area of segments. For
-- this we have a similar strategy. We first take a unit segment, and show it is a subset of the y
-- axis which as hhas measure zero
/-- The unit segment from `(0,0)` to `(0,1)`. -/
noncomputable def unitSegment : Segment := fun | 0 => (v 0 0) | 1 => (v 1 0)
/-- The `y`-axis as a submodule of the plane. -/
noncomputable def yAxis : Submodule ℝ ℝ² := Submodule.span ℝ (Set.range unitSegment )

--And some possibly unnecessary API
/--
@isnad1 id=eq.0h0v.s6.b63501c496e2 from=translated src=- shape=49b150c5 vocab=9b42a8e7
-/
lemma unitSegment_def : unitSegment = fun | 0 => (v 0 0) | 1 => (v 1 0)  := by rfl
/--
@isnad1 id=eq.0h0v.s8.cfb0ac20e92a from=translated src=- shape=bf08a0c6 vocab=d7d23c61
-/
theorem yAxis_def :  yAxis = Submodule.span ℝ (Set.range unitSegment ) := by rfl

--The proof this closed hull of the unit segment is contained in the y-axis
/--
@isnad1 id=le.0h0v.s8.36b2debd2846 from=translated src=- shape=c3e5647a vocab=32399d13
-/
theorem closed_unitSegment_subset : closedHull unitSegment ⊆ yAxis := by
  rintro x ⟨a, ⟨_, _⟩, h2⟩
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a, h2⟩

--And the conclusion it then must have measure zero, which can probably be a lot cleaner
/--
@isnad1 id=eq.0h0v.s9.6bc469c22f1b from=translated src=- shape=f9a23768 vocab=4c76f52d
-/
theorem volume_closed_unitSegment : MeasureTheory.volume (closedHull unitSegment) = 0 := by
  apply MeasureTheory.measure_mono_null (closed_unitSegment_subset )
  apply MeasureTheory.Measure.addHaar_submodule
  intro h
  have h3 : !₂[(0 : ℝ), 1] ∉ yAxis := by
    intro h1
    rw[yAxis] at h1
    rw[ Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, h1⟩ := h1
    rw[Fin.sum_univ_two, unitSegment_def] at h1
    have h1 := congrArg (fun z => z.ofLp 1) h1
    simp at h1
  simp_all

--Now for segments we also need linear maps and translations
/-- The edge vector of a segment together with the zero vector. -/
noncomputable def basisTransformSegment (L : Segment)
    : (Fin 2 → ℝ²) := (fun | 0 => (L 1 - L 0) | 1 => 0)
/-- The linear map sending the standard basis to a segment's edge vector. -/
noncomputable def linearTransformSegment (L : Segment) :=
  ourBasis.constr ℝ (basisTransformSegment L)
/-- Translation by the first endpoint of a segment. -/
def segmentTranslation (L : Segment) := translation (L 0)

--Some API
/--
@isnad1 id=eq.0h1v.s8.22e2d1b73b01 from=translated src=- shape=27067b98 vocab=9e0f6e38
-/
theorem basisTransformSegment_def (L : Segment)
    : basisTransformSegment L =  (fun | 0 => (L 1 - L 0) | 1 => 0) := by rfl
/--
@isnad1 id=eq.0h1v.s12.7c8bb756d71e from=translated src=- shape=e52b8516 vocab=b9e9b753
-/
theorem linearTransformSegment_def (L : Segment)
    : linearTransformSegment L =  ourBasis.constr ℝ (basisTransformSegment L) := by rfl
/--
@isnad1 id=eq.0h1v.s5.f5770fb5e3e0 from=translated src=- shape=86c3c64e vocab=76ce1d03
-/
theorem segmentTranslation_def (L : Segment) : segmentTranslation L =  translation (L 0) := by rfl

--Proving these transformations are the right ones
/--
@isnad1 id=eq.0h1v.s9.b40c3aaa4fcd from=translated src=- shape=f88315c5 vocab=c10b3f5f
-/
theorem unitSegment_toSegment (L : Segment) : Set.image (segmentTranslation L)
    (Set.image (linearTransformSegment L) (closedHull unitSegment)) = closedHull L := by
  have h1 : segmentTranslation L = translation (L 0) := by rfl
  let f : (Fin 2 → ℝ²) := fun | 0 => (v 0 0) | 1 => (v 1 0)
  have hunitSegment : unitSegment = f :=by rfl
  rw[hunitSegment, h1]
  have h2 : closedHull (linearTransformSegment L ∘ f )
      = ⇑(linearTransformSegment L) '' closedHull f :=
    closedHull_lin_trans (linearTransformSegment L) f
  rw[← h2]
  --rw[← openHull_lin_trans (linearTransform T) f] Why doesnt this work!??
  rw[← translation_commutes_closed]
  apply congrArg
  -- This part of the proof says that the linear transformation and translation of the unit triangle
  -- give the triangle we want
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp[translation, linearTransformSegment, basisTransformSegment,f, ourBasis]

--Proving they all have zero area
/--
@isnad1 id=eq.0h1v.s9.83e5ce6cfb7a from=translated src=- shape=52c3876c vocab=11addc22
-/
theorem volume_closed_segment (L : Segment) : (MeasureTheory.volume (closedHull L)) = 0 := by
  rw[←  unitSegment_toSegment L ,segmentTranslation_def]
  rw[ area_translation, area_lin_map, volume_closed_unitSegment]
  simp_all

-- We also in the end need that the unit square has volume 1. The unit square is equal to the square
-- spanned by the basis vectors, which Lean knows has volume 1. This is proved here, although the
-- prove is not finished
/--
@isnad1 id=eq.0h0v.s8.a883a5aeac18 from=translated src=- shape=bac6019e vocab=cb340f32
-/
theorem box_equal_to_pare : parallelepiped ourBasisOrtho = closedHull unitSquare := by
  ext x
  constructor
  · rw[mem_parallelepiped_iff ,  closedHull]
    rintro ⟨ t, ⟨ ⟨ h0,h1⟩ , h2⟩⟩
    use (fun
      | 0 => 1 + 0 ⊔ (t 0 + t 1 -1) - t 0 - t 1
      | 1 => t 0 - (0 ⊔ (t 0 + t 1 -1))
      | 2 => 0 ⊔ (t 0 + t 1 -1)
      | 3 => t 1 - ( 0 ⊔ (t 0 + t 1 -1)))
    constructor
    · constructor
      · intro i
        fin_cases i <;>
          simp only [Fin.isValue, sub_nonneg, sup_le_iff, tsub_le_iff_right,
            add_le_add_iff_left, le_sup_left]
        · rw [le_sub_iff_add_le, add_sup 0]
          ring_nf
          exact le_sup_right
        · exact ⟨h0 0, h1 1⟩
        · refine ⟨h0 1, ?_⟩
          rw [add_comm, add_le_add_iff_left]
          exact h1 0
      · rw [Fin.sum_univ_four]
        simp
        linarith
    · simp only [Fin.isValue]
      rw[h2, Fin.sum_univ_two, Fin.sum_univ_four]
      simp only [unitSquare]
      rw [ourBasisOrtho_zero, ourBasisOrtho_one]
      ext i
      fin_cases i <;> simp [v, PiLp.add_apply, PiLp.smul_apply]
  · rw[mem_parallelepiped_iff ,  closedHull]
    rintro ⟨ a ,⟨ h11,h12⟩  , h2⟩
    use (fun | 0 => a 1 + a 2 | 1 => a 3 + a 2  )
    constructor
    · simp only [Fin.isValue, Set.mem_Icc]
      constructor
      · intro i
        fin_cases i <;> simp <;> linarith [h11 1, h11 2, h11 3]
      · intro i
        rw [Fin.sum_univ_four] at h12
        fin_cases i <;>
          simp only [Fin.zero_eta, Fin.isValue, Pi.one_apply, Fin.mk_one] <;>
            apply le_trans _ (le_of_eq h12)
        · calc
            a 1 + a 2 ≤ a 0 + (a 1 + a 2)       := by exact le_add_of_nonneg_left (h11 0)
                    _ ≤ a 0 + (a 1 + a 2) + a 3 := by exact le_add_of_nonneg_right (h11 3)
                    _ = a 0 + a 1 + a 2 + a 3   := by ring
        · calc
            a 3 + a 2 ≤ a 0 + (a 3 + a 2)       := by exact le_add_of_nonneg_left (h11 0)
                    _ ≤ a 0 + (a 3 + a 2) + a 1 := by exact le_add_of_nonneg_right (h11 1)
                    _ = a 0 + a 1 + a 2 + a 3   := by ring
    · rw[← h2]
      simp only [Fin.sum_univ_four, Fin.sum_univ_two, unitSquare]
      rw [ourBasisOrtho_zero, ourBasisOrtho_one]
      ext i
      fin_cases i
      · simp_all
      · simp only [Fin.isValue, v, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul, mul_zero, add_zero, mul_one,
          zero_add]
        ring

/--
@isnad1 id=eq.0h0v.s9.34b48e99f134 from=translated src=- shape=b7a61bb9 vocab=21ec1216
-/
theorem volume_box : (MeasureTheory.volume (closedHull unitSquare)).toReal = 1 := by
  rw[← box_equal_to_pare]
  rw[OrthonormalBasis.volume_parallelepiped ourBasisOrtho]
  rfl

-- Now that we have calculated the volume, we move on to showing all this stuff is (null)measurable.
-- For this we distinguish between the case where the triangles are degenerate or not

-- this is not very clean, also because this theorem is also proved earlier when translating the
-- triangles
/--
@isnad1 id=eq.0h1v.s11.cb860e27cf4b from=translated src=- shape=ce5d47d0 vocab=03574791
-/
theorem det_of_triangle_transform (T : Triangle)
    : LinearMap.det (linearTransform T) = det (T : Triangle):= by
  rw[← Matrix.toLin_toMatrix ourBasis ourBasis  ( linearTransform T ) ]
  rw[LinearMap.det_toLin ourBasis ((LinearMap.toMatrix ourBasis ourBasis) (linearTransform T))]
  rw[Matrix.det_fin_two]
  rw[linearTransform_def, basisTransform_def, ourBasis_def ]
  unfold det
  repeat rw[LinearMap.toMatrix_apply]
  simp
  ring_nf

--The proof that the linear map corresponding to a nondegenerate triangle has nonzero determinant
/--
@isnad1 id=ne.1h1v.s11.beda903362eb from=translated src=- shape=863f4589 vocab=03574791
-/
theorem nondegen_triangle_lin_inv (T : Triangle) (h : det T ≠ 0)
    : LinearMap.det (linearTransform T) ≠ 0 := by
  rw [det_of_triangle_transform]
  exact h

-- This is the same linear transformation but now in the type of invertible map
/-- The linear equivalence given by a nondegenerate triangle's linear transform. -/
noncomputable def bijLinearTransform (T : Triangle) (h : det T ≠ 0) :=
  (LinearMap.equivOfDetNeZero (linearTransform T) (nondegen_triangle_lin_inv T h))

-- These statements are basically a consequence of that the linear map, but are used in the later
-- proof
/--
@isnad1 id=bijectiv.1h1v.s9.351f35fa4dee from=translated src=- shape=c12cdf6f vocab=ff72f6b0
-/
lemma linearTransform_bij (T : Triangle) (h : det T ≠ 0)
    : Function.Bijective (linearTransform T ) :=
  LinearEquiv.bijective (bijLinearTransform T h)

/--
@isnad1 id=leftinve.1h1v.s10.02fc7ebc9c73 from=translated src=- shape=bf0b8c4e vocab=ed9340ed
-/
lemma linearTransform_bij_left_inf (T : Triangle) (h : det T ≠ 0)
    : Function.LeftInverse (linearTransform T) ((bijLinearTransform T h).symm) :=
  ((bijLinearTransform T h).symm).left_inv

-- This is the inverse of the original triangle translation map, and the proof that are necessary to
-- work with it
/-- The inverse of `triangleTranslation`, translating by the negated first vertex. -/
def invTriangleTranslation (T : Triangle) := translation ( - T 0)

/--
@isnad1 id=bijectiv.0h1v.s4.69e1625fad13 from=translated src=- shape=88858bff vocab=aeef15c5
-/
lemma translation_bijective (a : ℝ²) : Function.Bijective (translation a) := by
  unfold translation
  constructor
  · intro x y
    simp
  · exact fun x ↦ ⟨x - a, by norm_num⟩

/--
@isnad1 id=bijectiv.0h1v.s5.cc81c4184d41 from=translated src=- shape=3ff136ed vocab=2c655683
-/
lemma triangleTranslation_bijective (T : Triangle)
    : Function.Bijective (triangleTranslation T) := by
  unfold triangleTranslation
  exact translation_bijective (T 0)

/--
@isnad1 id=leftinve.0h1v.s5.8fe55a2aeb3e from=translated src=- shape=d9252cb2 vocab=b51dcfdb
-/
lemma inv_translation_left (T : Triangle)
    :  Function.LeftInverse (triangleTranslation T) (invTriangleTranslation T) := by
  intro x
  rw[invTriangleTranslation, triangleTranslation, translation,translation]
  norm_num

--This is unitTriangle_to_triangle in its pre-image form
/--
@isnad1 id=eq.1h1v.s9.84197079139e from=translated src=- shape=f8035a25 vocab=149242ef
-/
theorem pre_unitTriangle_to_triangle (T : Triangle) (h : det T ≠ 0) :
    (linearTransform T) ⁻¹' ( (triangleTranslation T)⁻¹'(openHull T)) = openHull unitTriangle
    := by
  rw[Set.preimage_eq_iff_eq_image  (linearTransform_bij  T  h )]
  rw[Set.preimage_eq_iff_eq_image (triangleTranslation_bijective T)]
  symm
  exact unitTriangle_to_triangle (T : Triangle)

-- We can use then use the previous to show that the open hull of the triangle is a preimage of the
-- open unit triangle
/--
@isnad1 id=eq.1h1v.s10.5418686977e3 from=translated src=- shape=ce4b6dab vocab=b49e26fe
-/
theorem pre_triangle_to_unitTriangle (T : Triangle) (h : det T ≠ 0) :
    (invTriangleTranslation T)⁻¹'  ((bijLinearTransform T h).symm⁻¹' (openHull unitTriangle))
    = openHull T := by
  rw[← pre_unitTriangle_to_triangle T h]
  rw[Function.LeftInverse.preimage_preimage (linearTransform_bij_left_inf T h)
    (triangleTranslation T ⁻¹' openHull T)]
  rw[Function.LeftInverse.preimage_preimage (inv_translation_left T) ]

--In order to actually use this, we need that all these maps are measurable
/--
@isnad1 id=measurab.0h1v.s10.59b86579af00 from=translated src=- shape=6c8d1879 vocab=f3d7fafe
-/
theorem meas_lin_map (L : ℝ² →ₗ[ℝ] ℝ²) : Measurable L :=
  ContinuousLinearMap.measurable (LinearMap.toContinuousLinearMap L)

/--
@isnad1 id=measurab.0h1v.s7.8b87c95f1cb7 from=translated src=- shape=88858bff vocab=2a243630
-/
theorem meas_translation (a : ℝ²) : Measurable (translation a) := by
  unfold translation
  exact Measurable.add_const (fun ⦃t⦄ a ↦ a) a

/--
@isnad1 id=measurab.0h1v.s7.3199655a08f2 from=translated src=- shape=3ff136ed vocab=3229afc9
-/
lemma meas_invTriangleTranslation (T : Triangle) : Measurable (invTriangleTranslation T) := by
  unfold invTriangleTranslation
  exact meas_translation (- T 0)

--Then we can show that nondegenerate triangles are measurable
/--
@isnad1 id=measurab.1h1v.s6.4a0f8ffe73e6 from=translated src=- shape=15c1b25f vocab=35be7369
-/
theorem nondegen_triangle_meas (T : Triangle) (h : det T ≠ 0) : MeasurableSet (openHull T) := by
  rw[← pre_triangle_to_unitTriangle T h]
  have h1 : MeasurableSet ((bijLinearTransform T h).symm ⁻¹' openHull unitTriangle) :=
    measurableSet_preimage (meas_lin_map (bijLinearTransform T h).symm) measurable_unitTriangle
  exact measurableSet_preimage (meas_invTriangleTranslation T) h1

--As any set of measure zero is null measurable, we have then that all triangles are null measurable
/--
@isnad1 id=nullmeas.0h1v.s7.17f79fe00759 from=translated src=- shape=aff51f02 vocab=3474d1aa
-/
theorem null_meas_triangle (T : Triangle) : MeasureTheory.NullMeasurableSet (openHull T) := by
  by_cases h : |det T| > 0
  · exact (nondegen_triangle_meas T (abs_ne_zero.mp (ne_of_lt h).symm)).nullMeasurableSet
  · simp only [gt_iff_lt, abs_pos, ne_eq, Decidable.not_not] at h
    apply MeasureTheory.NullMeasurableSet.of_null
    rw[volume_open_triangle' T, h]
    simp

--Now that we have also have measurability we can start the real work
--The edge points of the triangle have already been defined with Tside

-- We show that the closed hull of these edges together with an open triangle makes a closed
-- triangle, first the definition
/-- The union of the closed hulls of a triangle's three sides. -/
def allEdgesTriangleHull (T : Triangle) :=
  closedHull (Tside T 0) ∪ closedHull (Tside T 1) ∪ closedHull (Tside T 2)

-- then the proof (this proof is probably the ugliest I have written, with lots of ctr copy ctr
-- paste, but it is also the last sorry I had to fill in so I don't care :))
/--
@isnad1 id=eq.0h1v.s5.ab6c47047ebc from=translated src=- shape=85ef9be2 vocab=eb413047
-/
theorem closed_triangle_is_union (T : Triangle)
    : closedHull T = openHull T ∪ allEdgesTriangleHull T := by
  ext x
  constructor
  · rintro ⟨ a ,⟨ h1, h2⟩  , h3⟩
    by_cases ha0 : a 0 = 0
    · right
      left
      left
      use (fun | 0 => a 1 | 1 => a 2)
      unfold Tside
      dsimp
      constructor
      · constructor
        · simp_all
        · rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
          linarith
      · dsimp at h3
        rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
        simp_all
    · by_cases ha1 : a 1 = 0
      · right
        left
        right
        use (fun | 0 => a 2 | 1 => a 0)
        unfold Tside
        dsimp
        constructor
        · constructor
          · simp_all
          · rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
            linarith
        · dsimp at h3
          rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
          rw[ha1] at h3 h2
          simp only [Fin.isValue, zero_smul, add_zero] at *
          rw[add_comm]
          exact h3
      · by_cases ha2 : a 2 = 0
        · right
          right
          use (fun | 0 => a 0 | 1 => a 1)
          unfold Tside
          dsimp
          constructor
          · constructor
            · simp_all
            · rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
              linarith
          · dsimp at h3
            rw[Fin.sum_univ_two,Fin.sum_univ_three] at *
            simp_all
        · left
          use a
          constructor
          · constructor
            · intro i
              fin_cases i
              · specialize h1 0
                exact lt_of_le_of_ne h1 fun a_1 ↦ ha0 (id (Eq.symm a_1))
              · specialize h1 1
                exact lt_of_le_of_ne h1 fun a_1 ↦ ha1 (id (Eq.symm a_1))
              · specialize h1 2
                exact lt_of_le_of_ne h1 fun a_1 ↦ ha2 (id (Eq.symm a_1))
            · exact h2
          · exact h3
  · rintro ( hx1| hx2)
    · exact open_sub_closed T hx1
    · unfold allEdgesTriangleHull at hx2
      rcases hx2 with ((hx3|hx4 )| hx5)
      · exact closed_side_sub hx3
      · exact closed_side_sub hx4
      · exact closed_side_sub hx5

--This is useful lemma
/--
@isnad1 id=eq.1h2v.s10.231fcad93c2f from=translated src=- shape=44e8ecbd vocab=b773bffc
-/
lemma volume_zero (A B : Set ℝ²) (h : MeasureTheory.volume B = 0)
    : MeasureTheory.volume (A ∪ B) = MeasureTheory.volume A := by
  symm
  apply MeasureTheory.measure_eq_measure_of_null_sdiff
  · exact Set.subset_union_left
  · have h1 : ((A ∪ B) \ A) ⊆ B :=
      Set.sdiff_subset_iff.mpr fun ⦃a⦄ a ↦ a
    exact MeasureTheory.measure_mono_null h1 h

--This shows that the boundary (but not Pjotrs boundary) of a triangle has measure zero
/--
@isnad1 id=eq.0h1v.s9.5cf8834c490f from=translated src=- shape=31475079 vocab=69a86670
-/
theorem allEdgesTriangleHull_area (T : Triangle)
    : MeasureTheory.volume (allEdgesTriangleHull T) = 0:= by
  unfold allEdgesTriangleHull
  rw [volume_zero _ _ (volume_closed_segment (Tside T 2)),
    volume_zero _ _ (volume_closed_segment (Tside T 1))]
  exact volume_closed_segment (Tside T 0)

-- This shows that all boundaries combined also have measure zero. This proof is a lot uglier then I
-- would like it to be, it might be due to a lack of understanding of sums and unions....
/--
@isnad1 id=eq.0h1v.s9.40c059b3e963 from=translated src=- shape=2c7cd6f6 vocab=fa6732a2
-/
theorem union_of_edges_zero_vol (S : Finset Triangle)
    : MeasureTheory.volume ( ⋃ (T ∈ S) , allEdgesTriangleHull T ) = 0 := by
  let f := Set.domRestrict ↑S allEdgesTriangleHull
  have h : ∀ (i : S), MeasureTheory.NullMeasurableSet (f i) := by
    · intro T
      exact MeasureTheory.NullMeasurableSet.of_null (allEdgesTriangleHull_area T)
  have hd : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) f) := by
    intro i j _
    rw[Function.onFun_apply]
    have h2 : S.restrict allEdgesTriangleHull i ∩ S.restrict allEdgesTriangleHull j
        ⊆ S.restrict allEdgesTriangleHull i := Set.inter_subset_left
    apply MeasureTheory.measure_mono_null h2 (allEdgesTriangleHull_area i)
  have h4 :  ⋃ T ∈ S, allEdgesTriangleHull T
      = (⋃ i, (↑S : Set Triangle).domRestrict allEdgesTriangleHull i) :=
    Eq.symm (Set.iUnion_subtype (Membership.mem S) (S.restrict allEdgesTriangleHull))
  rw[h4]
  rw[MeasureTheory.measure_iUnion₀ hd h]
  have h5 : (fun x ↦ MeasureTheory.volume (f x))= (fun x ↦ 0) := by
    ext x
    unfold f
    exact allEdgesTriangleHull_area x
  simp_all

-- This theorem shows that whenever you have a cover by triangles, the measure theoretic area of the
-- triangles add up to the measure theoretic area of what they cover
--This proof is a bit ugly, but these sums and unions are very annoying to work with in my opinion
/--
@isnad1 id=eq.1h2v.s10.b18e2fd98ee9 from=translated src=- shape=164c3b3f vocab=af3463bd
-/
theorem area_equal_sum_cover (X : Set ℝ²) (S : Finset Triangle)
    (hcover : isDisjointCover X (↑S : Set Triangle))
    : MeasureTheory.volume X = ∑  (T ∈  S), MeasureTheory.volume (openHull T) := by
  unfold isDisjointCover at hcover
  rw[hcover.1]
  have h1:  closedHull  = (fun T ↦  openHull T ∪ allEdgesTriangleHull T) := by
    ext T X
    rw[closed_triangle_is_union T]
  have h2 :  ⋃ T ∈ (↑S : Set Triangle), closedHull T
      = (⋃ i, (↑S : Set Triangle).domRestrict closedHull i) :=
    Eq.symm (Set.iUnion_subtype (Membership.mem S) (S.restrict closedHull))
  rw[h2,  h1]
  dsimp
  rw[Set.iUnion_union_distrib ]
  rw[volume_zero]
  · let openHullT : (Triangle → Set ℝ²) := openHull
    let f := Set.domRestrict ↑S openHullT
    have h : ∀ (i : S), MeasureTheory.NullMeasurableSet (f i) := by
      · intro T
        exact null_meas_triangle T
    have hd : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) f) := by
      have h6 := hcover.2
      unfold f openHullT
      unfold isDisjointPolygonSet at h6
      unfold Pairwise
      intro i j hij
      apply Disjoint.aedisjoint
      simp_all
    erw[MeasureTheory.measure_iUnion₀ hd h, tsum_fintype,]
    simp only [SetLike.coe_sort_coe, univ_eq_attach, Set.domRestrict_apply, f]
    rw [Finset.sum_attach S (fun x ↦ volume (openHullT x))]
  · have h4 :  ⋃ T ∈ S, allEdgesTriangleHull T
        = (⋃ i, (↑S : Set Triangle).domRestrict allEdgesTriangleHull i) :=
      Eq.symm (Set.iUnion_subtype (Membership.mem S) (S.restrict allEdgesTriangleHull))
    have h5 := union_of_edges_zero_vol S
    simp_all

-- This theorem is similar to the above but specifically to the unit square (which has an area of 1)
-- and where the measure theoretic area of the triangles replaced by their area in determinant form
--This proof is even uglier then the previous
/--
@isnad1 id=eq.1h1v.s7.1b7f44c986d0 from=translated src=- shape=80bcaf2b vocab=53ecbcf7
-/
theorem triangle_det_sum_one (S : Finset Triangle)
    (hcover : isDisjointCover (closedHull unitSquare) (↑S : Set Triangle)) :
    ∑  (T ∈  S), |det T|/2 = 1 := by
  rw[← volume_box]
  rw[area_equal_sum_cover (closedHull unitSquare) S hcover]
  have h: ∀ T ∈  S, |det T|/2 = (MeasureTheory.volume (openHull T)).toReal := by
    intro T _
    rw[volume_open_triangle]
  rw[sum_congr (by rfl) h]
  rw[ENNReal.toReal_sum]
  intro a _; rw [volume_open_triangle']; simp

-- This is the statemet we have been working so hard for: whenever we have a cover of triangles of
-- equal area, this area must be 1/|amount of triangles|
/--
@isnad1 id=eq.2h2v.s7.69597f82287f from=translated src=- shape=f1c069f5 vocab=085591ff
-/
theorem equal_area_cover_implies_triangleArea_n (S : Finset Triangle)
  (hcover : isEqualAreaCover (closedHull unitSquare) S)
  : ∀ T ∈ S, triangleArea T = 1/ S.card := by
  rcases hcover with ⟨ h1, ⟨ area,h2 ⟩ ⟩
  intro T hT
  have h3 := triangle_det_sum_one S h1
  have h4 : ∑ T ∈ S, |det T|/2 = ∑ _ ∈ S, area := sum_congr rfl h2
  rw [h4, sum_const] at h3
  rw[h2 T hT, ← h3, nsmul_eq_mul]
  ring_nf
  rw [mul_assoc,mul_comm,mul_assoc, IsUnit.inv_mul_cancel _, mul_one]
  simp only [nsmul_eq_mul] at h3
  apply isUnit_iff_exists.mpr
  use area
  constructor
  · exact h3
  · rw [mul_comm]; exact h3

end Monsky
end LeanPool
