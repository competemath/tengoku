/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Function-space representations from subgroup characters

This file constructs a finite-dimensional representation on a covariance submodule of
complex-valued functions on a finite group. It also develops an averaging projection, computes
the corresponding trace, and relates characters transformed by subgroup normalizer elements.
-/

noncomputable section

namespace RepresentationTheory.FDRep.SubgroupCharacterFunctions

open Finset

variable {G : Type} [Group G] (H : Subgroup G) (lam : ↥H →* ℂˣ)

/-- A complex submodule of functions on a group associated with a subgroup character.-/
def subgroupCharacterFunctionSubmodule : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g}
  add_mem' {f f'} hf hf' := by
    intro h g; simp only [Pi.add_apply]; rw [hf h g, hf' h g, mul_add]
  zero_mem' := by intro h g; simp
  smul_mem' c f hf := by
    intro h g; simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf h g, mul_left_comm]

/-- A function belongs to the subgroup-character submodule exactly when left multiplication by a
subgroup element scales it by the character value.
@isnad1 id=iff.0h4v.s9.7a233dc882ec from=translated src=- shape=9453bb2c vocab=88f11d0b
-/
lemma mem_subgroupCharacterFunctionSubmodule_iff (f : G → ℂ) :
    f ∈ subgroupCharacterFunctionSubmodule H lam ↔
      ∀ (h : ↥H) (g : G), f (h.val * g) = (lam h : ℂ) * f g :=
  Iff.rfl

/-- Right translation by a group element as a complex-linear map on functions on the group.-/
def rightTranslationLinearMap (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => f (g * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Right translation sends a function to its evaluation after right multiplication by the
translating element.
@isnad1 id=eq.0h4v.s7.190dc1183b62 from=translated src=- shape=553f4243 vocab=dbc810bd
-/
@[simp]
lemma rightTranslationLinearMap_apply (a : G) (f : G → ℂ) (g : G) :
    rightTranslationLinearMap a f g = f (g * a) := rfl

/-- The subgroup-character function submodule is stable under every right translation.
@isnad1 id=mem.1h5v.s8.b3279ca01b04 from=translated src=- shape=f2d69b6a vocab=d11a0738
-/
lemma rightTranslationLinearMap_mem {f : G → ℂ}
    (hf : f ∈ subgroupCharacterFunctionSubmodule H lam) (a : G) :
    rightTranslationLinearMap a f ∈ subgroupCharacterFunctionSubmodule H lam := by
  intro h g
  change f (h.val * g * a) = (lam h : ℂ) * f (g * a)
  rw [mul_assoc]; exact hf h (g * a)

/-- A complex representation of the group on the subgroup-character function submodule.-/
def subgroupCharacterFunctionRepresentation :
    Representation ℂ G (subgroupCharacterFunctionSubmodule H lam) where
  toFun a :=
    { toFun := fun f =>
        ⟨rightTranslationLinearMap a f.val, rightTranslationLinearMap_mem H lam f.2 a⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro f
    exact Subtype.ext (funext fun g => congr_arg f.val (mul_assoc g a b).symm)

/-- The representation action evaluates a function after right multiplication of its argument.
@isnad1 id=eq.0h6v.s11.d6178417ed63 from=translated src=- shape=434cd440 vocab=97637098
-/
@[simp]
lemma subgroupCharacterFunctionRepresentation_apply (a : G)
    (f : ↥(subgroupCharacterFunctionSubmodule H lam)) (g : G) :
    ((subgroupCharacterFunctionRepresentation H lam a f :
      ↥(subgroupCharacterFunctionSubmodule H lam)) : G → ℂ) g =
      (f : G → ℂ) (g * a) := rfl

/-! Normalizer transformations. -/

/-- A subgroup character obtained from a character and an element of the subgroup normalizer.-/
def subgroupCharacterOfNormalizer (s : G) (hs : s ∈ Subgroup.normalizer H) : ↥H →* ℂˣ where
  toFun h := lam ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩
  map_one' := by
    rw [← map_one lam]
    apply congrArg lam
    ext
    simp
  map_mul' a b := by
    rw [← map_mul]
    apply congrArg lam
    ext
    simp only [Subgroup.coe_mul]
    group

/-- A linear equivalence between the function submodules associated with a subgroup character and
its normalizer transform.-/
def subgroupCharacterFunctionLinearEquivOfNormalizer (s : G)
    (hs : s ∈ Subgroup.normalizer H) :
    subgroupCharacterFunctionSubmodule H lam ≃ₗ[ℂ]
      subgroupCharacterFunctionSubmodule H (subgroupCharacterOfNormalizer H lam s hs) where
  toFun f := ⟨fun g => f.val (s * g), by
    intro h g
    change f.val (s * (h * g)) =
      (lam ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ : ℂ) * f.val (s * g)
    have hf := f.2 ⟨s * h * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs h).mp h.2⟩ (s * g)
    convert hf using 1; group⟩
  invFun f := ⟨fun g => f.val (s⁻¹ * g), by
    intro h g
    have hs_inv : s⁻¹ ∈ Subgroup.normalizer H := inv_mem hs
    have hmem : s⁻¹ * (h : G) * s ∈ H := by
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hs_inv h).mp h.2
    let h' : H := ⟨s⁻¹ * (h : G) * s, hmem⟩
    change f.val (s⁻¹ * ((h : G) * g)) = (lam h : ℂ) * f.val (s⁻¹ * g)
    have hf := f.2 h' (s⁻¹ * g)
    change f.val ((h' : G) * (s⁻¹ * g)) =
      (lam ⟨s * (h' : G) * s⁻¹,
        (Subgroup.mem_normalizer_iff.mp hs h').mp h'.2⟩ : ℂ) * f.val (s⁻¹ * g) at hf
    simpa [h', mul_assoc] using hf⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normalizer linear equivalence sends a function to evaluation after left multiplication by
the normalizing element.
@isnad1 id=eq.1h6v.s10.03027906d6c5 from=translated src=- shape=60580de0 vocab=9e3e76e9
-/
@[simp]
lemma subgroupCharacterFunctionLinearEquivOfNormalizer_apply (s : G)
    (hs : s ∈ Subgroup.normalizer H) (f : subgroupCharacterFunctionSubmodule H lam) (g : G) :
    ((subgroupCharacterFunctionLinearEquivOfNormalizer H lam s hs f :
      subgroupCharacterFunctionSubmodule H (subgroupCharacterOfNormalizer H lam s hs)) :
      G → ℂ) g = f.val (s * g) := rfl

variable [Fintype G] [DecidablePred (· ∈ H)]

/-- A finite-dimensional complex representation associated with a subgroup and a character into
the complex units.-/
def representationFromSubgroupCharacter : FDRep ℂ G :=
  FDRep.of (subgroupCharacterFunctionRepresentation H lam)

/-! Averaging into the subgroup-character submodule. -/

/-- A complex-linear endomorphism of complex-valued functions on the group associated with finite
subgroup character data.-/
def subgroupCharacterAveraging : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring

/-- At each group element, the averaging map is the normalized subgroup sum weighted by inverse
character values.
@isnad1 id=eq.0h5v.s9.476c1fde3c1f from=translated src=- shape=bcdffd1d vocab=d64112e0
-/
lemma subgroupCharacterAveraging_apply (f : G → ℂ) (g : G) :
    subgroupCharacterAveraging H lam f g =
      (Fintype.card ↥H : ℂ)⁻¹ *
        ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) := rfl

/-- The subgroup-character average of any function belongs to the associated function submodule.
@isnad1 id=mem.0h4v.s8.ba87a7169bdc from=translated src=- shape=c4c8758e vocab=e3fc8be0
-/
lemma subgroupCharacterAveraging_mem (f : G → ℂ) :
    subgroupCharacterAveraging H lam f ∈ subgroupCharacterFunctionSubmodule H lam := by
  intro h₀ g
  rw [subgroupCharacterAveraging_apply, subgroupCharacterAveraging_apply, ← mul_assoc,
    mul_comm ((lam h₀ : ℂˣ) : ℂ), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h₀) _ _ ?_
  intro h
  have hlam : (((lam (h * h₀))⁻¹ : ℂˣ) : ℂ) =
      (((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_mul, mul_inv, Units.val_mul]
  have hcancel : ((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) = 1 :=
    Units.mul_inv _
  change (((lam h)⁻¹ : ℂˣ) : ℂ) * f ((h : G) * (h₀.val * g)) =
    ((lam h₀ : ℂˣ) : ℂ) *
      ((((lam (h * h₀))⁻¹ : ℂˣ) : ℂ) * f (((h * h₀ : ↥H) : G) * g))
  rw [hlam, show ((h * h₀ : ↥H) : G) = (h : G) * (h₀ : G) from rfl,
    ← mul_assoc (h : G) (h₀ : G) g]
  set X := f ((h : G) * (h₀ : G) * g)
  calc
    (((lam h)⁻¹ : ℂˣ) : ℂ) * X =
        (((lam h₀ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ)) *
          ((((lam h)⁻¹ : ℂˣ) : ℂ) * X) := by
      rw [hcancel, one_mul]
    _ = ((lam h₀ : ℂˣ) : ℂ) *
        ((((lam h)⁻¹ : ℂˣ) : ℂ) * (((lam h₀)⁻¹ : ℂˣ) : ℂ) * X) := by
      ring

/-- The subgroup-character averaging map fixes every function in the associated submodule.
@isnad1 id=eq.1h4v.s8.0f753d532443 from=translated src=- shape=fe773c4b vocab=e3fc8be0
-/
lemma subgroupCharacterAveraging_eq_self {f : G → ℂ}
    (hf : f ∈ subgroupCharacterFunctionSubmodule H lam) :
    subgroupCharacterAveraging H lam f = f := by
  funext g
  rw [subgroupCharacterAveraging_apply]
  have hterm : ∀ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) * f (h.val * g) = f g := by
    intro h
    rw [hf h g, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-! Trace transport. -/

/-- A family of linear maps from all complex-valued functions on the group into the
subgroup-character function submodule.-/
def toSubgroupCharacterFunctionSubmoduleAt (a : G) :
    (G → ℂ) →ₗ[ℂ] ↥(subgroupCharacterFunctionSubmodule H lam) :=
  LinearMap.codRestrict (subgroupCharacterFunctionSubmodule H lam)
    (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a)
    fun _ => subgroupCharacterAveraging_mem H lam _

/-- Restricting the map into the subgroup-character function submodule agrees with the associated
representation action.
@isnad1 id=eq.0h4v.s11.a3839fbc124a from=translated src=- shape=9a923a4d vocab=ccbcd361
-/
lemma toSubgroupCharacterFunctionSubmoduleAt_comp_subtype (a : G) :
    toSubgroupCharacterFunctionSubmoduleAt H lam a ∘ₗ
        (subgroupCharacterFunctionSubmodule H lam).subtype =
      subgroupCharacterFunctionRepresentation H lam a := by
  apply LinearMap.ext; intro f
  apply Subtype.ext
  change subgroupCharacterAveraging H lam (rightTranslationLinearMap a f.val) =
    rightTranslationLinearMap a f.val
  exact subgroupCharacterAveraging_eq_self H lam
    (rightTranslationLinearMap_mem H lam f.2 a)

/-- Including the submodule-valued map into all functions equals subgroup-character averaging
after right translation.
@isnad1 id=eq.0h4v.s9.963aa390423a from=translated src=- shape=b26cf2af vocab=7b778b7f
-/
lemma subtype_comp_toSubgroupCharacterFunctionSubmoduleAt (a : G) :
    (subgroupCharacterFunctionSubmodule H lam).subtype ∘ₗ
        toSubgroupCharacterFunctionSubmoduleAt H lam a =
      subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a := rfl

/-- The trace of the subgroup-character function representation equals the trace of averaging
composed with right translation on the full function space.
@isnad1 id=eq.0h4v.s12.9c08984622cd from=translated src=- shape=be7b194f vocab=13fc22ba
-/
lemma trace_subgroupCharacterFunctionRepresentation_eq (a : G) :
    LinearMap.trace ℂ _ (subgroupCharacterFunctionRepresentation H lam a) =
      LinearMap.trace ℂ (G → ℂ)
        (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a) := by
  rw [← toSubgroupCharacterFunctionSubmoduleAt_comp_subtype H lam a,
    LinearMap.trace_comp_comm' (subgroupCharacterFunctionSubmodule H lam).subtype
      (toSubgroupCharacterFunctionSubmoduleAt H lam a),
    subtype_comp_toSubgroupCharacterFunctionSubmoduleAt]

/-! Diagonal trace calculation. -/

/-- The diagonal summand is supported at the uniquely determined subgroup element.-/
private lemma sum_indicator [DecidableEq G] (a g : G) :
    ∑ h : ↥H, (((lam h)⁻¹ : ℂˣ) : ℂ) *
        (if (h : G) * g * a = g then (1 : ℂ) else 0) =
      if hm : g * a⁻¹ * g⁻¹ ∈ H then
        (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0 := by
  by_cases hm : g * a⁻¹ * g⁻¹ ∈ H
  · rw [dite_eq_left hm]
    set h₀ : ↥H := ⟨g * a⁻¹ * g⁻¹, hm⟩ with hh₀
    have hcond : ∀ h : ↥H, ((h : G) * g * a = g) ↔ h = h₀ := by
      intro h
      constructor
      · intro hh
        apply Subtype.ext
        change (h : G) = g * a⁻¹ * g⁻¹
        have h2 : (h : G) * (g * a) = g := by rw [← mul_assoc]; exact hh
        rw [eq_mul_inv_of_mul_eq h2]
        group
      · rintro rfl
        change (g * a⁻¹ * g⁻¹) * g * a = g
        group
    rw [Finset.sum_congr rfl fun h _ => by rw [if_congr (hcond h) rfl rfl],
      Finset.sum_eq_single h₀
        (fun h _ hne => by rw [ite_eq_right hne, mul_zero])
        (fun hnm => absurd (Finset.mem_univ h₀) hnm),
      ite_eq_left rfl, mul_one]
  · rw [dite_eq_right hm]
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [ite_eq_right, mul_zero]
    intro hh
    apply hm
    have h2 : (h : G) * (g * a) = g := by rw [← mul_assoc]; exact hh
    have h3 : (h : G) = g * a⁻¹ * g⁻¹ := by rw [eq_mul_inv_of_mul_eq h2]; group
    exact h3 ▸ h.2

/-- Compute the trace of averaged right translation in the standard function basis.-/
private lemma trace_proj_comp (a : G) :
    LinearMap.trace ℂ (G → ℂ)
        (subgroupCharacterAveraging H lam ∘ₗ rightTranslationLinearMap a) =
      (Fintype.card ↥H : ℂ)⁻¹ * ∑ g : G,
        if hm : g * a⁻¹ * g⁻¹ ∈ H then
          (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ)
        else 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  change subgroupCharacterAveraging H lam (rightTranslationLinearMap a (Pi.single g 1)) g = _
  rw [subgroupCharacterAveraging_apply, ← sum_indicator H lam a g]
  refine congrArg _ (Finset.sum_congr rfl fun h _ => ?_)
  rw [rightTranslationLinearMap_apply, Pi.single_apply]

/-! Character and dimension formulas. -/

/-- An auxiliary result involving the representation associated with subgroup character data.
@isnad1 id=eq.0h4v.s9.2cc04f475652 from=translated src=- shape=6fd37ce2 vocab=8f968ee2
-/
theorem auxiliary_representationFromSubgroupCharacter (a : G) :
    (representationFromSubgroupCharacter H lam).character a =
      (Fintype.card ↥H : ℂ)⁻¹ * ∑ x : G,
        if hm : x⁻¹ * a * x ∈ H then
          ((lam ⟨x⁻¹ * a * x, hm⟩ : ℂˣ) : ℂ) else 0 := by
  change LinearMap.trace ℂ _ (subgroupCharacterFunctionRepresentation H lam a) = _
  rw [trace_subgroupCharacterFunctionRepresentation_eq, trace_proj_comp]
  refine congrArg _ (Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_)
  change (if hm : g * a⁻¹ * g⁻¹ ∈ H then
      (((lam ⟨g * a⁻¹ * g⁻¹, hm⟩)⁻¹ : ℂˣ) : ℂ) else 0) =
    if hm : g⁻¹⁻¹ * a * g⁻¹ ∈ H then
      ((lam ⟨g⁻¹⁻¹ * a * g⁻¹, hm⟩ : ℂˣ) : ℂ) else 0
  have hinv : (g * a⁻¹ * g⁻¹)⁻¹ = g⁻¹⁻¹ * a * g⁻¹ := by group
  by_cases hm : g * a⁻¹ * g⁻¹ ∈ H
  · have hm' : g⁻¹⁻¹ * a * g⁻¹ ∈ H := hinv ▸ H.inv_mem hm
    rw [dite_eq_left hm, dite_eq_left hm',
      show (⟨g⁻¹⁻¹ * a * g⁻¹, hm'⟩ : ↥H) =
          (⟨g * a⁻¹ * g⁻¹, hm⟩ : ↥H)⁻¹ from
        Subtype.ext hinv.symm,
      map_inv]
  · have hm' : ¬ (g⁻¹⁻¹ * a * g⁻¹ ∈ H) := fun hc => hm (by
      have := H.inv_mem hc
      rwa [show (g⁻¹⁻¹ * a * g⁻¹)⁻¹ = g * a⁻¹ * g⁻¹ from by group] at this)
    rw [dite_eq_right hm, dite_eq_right hm']

/-- The dimension of the representation associated with subgroup character data is the group
cardinality divided by the subgroup cardinality.
@isnad1 id=eq.0h3v.s8.94b2ebc28c17 from=translated src=- shape=6160eea9 vocab=c04cefeb
-/
theorem finrank_representationFromSubgroupCharacter :
    Module.finrank ℂ (representationFromSubgroupCharacter H lam) =
      Fintype.card G / Fintype.card ↥H := by
  have hdvd : Fintype.card ↥H ∣ Fintype.card G := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  obtain ⟨m, hm⟩ := hdvd
  have hpos : (0 : ℕ) < Fintype.card ↥H := Fintype.card_pos
  have hchar := auxiliary_representationFromSubgroupCharacter H lam 1
  rw [FDRep.char_one] at hchar
  have hsum : ∑ x : G,
      (if hmem : x⁻¹ * (1 : G) * x ∈ H then
        ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
        else 0) = (Fintype.card G : ℂ) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => show
        (if hmem : x⁻¹ * (1 : G) * x ∈ H then
          ((lam ⟨x⁻¹ * (1 : G) * x, hmem⟩ : ℂˣ) : ℂ)
          else 0) = (1 : ℂ) from by
      have hx : x⁻¹ * (1 : G) * x = 1 := by group
      simp only [hx, dite_eq_left H.one_mem]
      rw [show (⟨(1 : G), H.one_mem⟩ : ↥H) = 1 from rfl, map_one, Units.val_one],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, hm] at hchar
  have hne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hcast : (Module.finrank ℂ (representationFromSubgroupCharacter H lam) : ℂ) =
      (m : ℂ) := by
    rw [hchar]; push_cast;
    field_simp
  have hfin : Module.finrank ℂ (representationFromSubgroupCharacter H lam) = m :=
    Nat.cast_injective hcast
  rw [hfin, hm, Nat.mul_div_cancel_left m hpos]

end RepresentationTheory.FDRep.SubgroupCharacterFunctions

/-- An auxiliary statement whose displayed formal type is unavailable.
@isnad1 id=eq.0h4v.s9.2cc04f475652 from=translated src=- shape=6fd37ce2 vocab=8f968ee2
-/
alias _root_.RepresentationTheory.FDRep.SubgroupCharacterFunctions.Auxiliary.statement004835 := _root_.RepresentationTheory.FDRep.SubgroupCharacterFunctions.auxiliary_representationFromSubgroupCharacter
