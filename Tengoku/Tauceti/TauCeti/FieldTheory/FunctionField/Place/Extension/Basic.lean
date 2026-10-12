/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.FieldTheory.FunctionField.Place.Basic
public import Tengoku.Tauceti.TauCeti.RingTheory.Valuation.Discrete.Normalize
-- Proof-only: nontriviality survives restriction along an algebraic extension.
import Tengoku.Tauceti.TauCeti.RingTheory.Valuation.NontrivialComap

/-!
# Extensions of places: the ramification index and the relative degree

Let `F' / k'` be a field extension lying over `F / k`, with `F'` algebraic over `F`. Restricting
the valuation of a place `P'` of `F' / k'` to `F` gives a valuation of `F` that is trivial on the
constants and — because `F'` is algebraic over `F`, so that a valuation ring of `F'` containing
`F` would be all of `F'` — nontrivial. Normalizing it produces a place `P = P'.restrict k F` of
`F / k`, the place of `F` that `P'` *lies over*, and the index divided out in the normalization
is the **ramification index** `e(P' | P)`. The residue field of `P` embeds in the residue field
of `P'`, and the degree of that extension is the **relative degree** `f(P' | P)`.

The constant field may grow along with `F`: if `k'` is integral over `k` then a valuation of `F'`
is trivial on `k` exactly when it is trivial on `k'`, so the places of `F' / k` and of `F' / k'`
are literally the same objects. That is `TauCeti.Place.constantsEquiv`, which lets a place of
`F' / k'` be produced from data that only sees the smaller constant field `k`.

The main theorem is the bound `e(P' | P) · f(P' | P) ≤ [F' : F]`: residues of elements of `𝒪_{P'}`
that are independent over `F_P`, multiplied by the powers `t^j` of a prime element for `P'` with
`0 ≤ j < e`, are independent over `F`, because the orders of the resulting blocks are pairwise
distinct modulo `e`.

The file also records the action of the valuation ring `𝒪_P` of a place `P` of `F / k` on the
extension field `F'`, through `F`.  That action is not a global instance — for `F' = F` it would
compete with the action of a valuation subring on its own field — so it, and the scalar tower it
sits in, are provided to be reinstalled by consumers with `attribute [local instance 10]`.
For a finite extension, it also records the standard local integral-closure model
`𝒪_P ⊆ 𝒪'_P`: `F'` is the fraction field and the localization of `𝒪'_P` at `(𝒪_P)⁰`; for a
separable extension, `𝒪'_P` is Dedekind and module-finite over `𝒪_P`, and separability transports
to the canonical fraction fields used by Mathlib's different API.

## Main definitions

* `TauCeti.Place.constantsEquiv`: the places of `F' / k` are the places of `F' / k'`, for `k'`
  integral over `k`; enlarging the constants by an algebraic extension changes nothing.
* `TauCeti.Place.algebraIntegersExtension` and `TauCeti.Place.isScalarTowerIntegersExtension`: the
  action of the valuation ring of a place of `F / k` on an extension field `F'`, to be installed
  with `attribute [local instance 10]`.
* `TauCeti.Place.restrict`: the place of `F / k` that a place of `F' / k'` lies over.
* `TauCeti.Place.ramificationIdx`: the ramification index `e(P' | P)`.
* `TauCeti.Place.relativeDegree`: the relative degree `f(P' | P) = [F'_{P'} : F_P]`.

## Main results

* `TauCeti.Place.ord_algebraMap_restrict`: the defining property `ord_{P'} = e · ord_P` on `F`.
* `TauCeti.Place.restrict_eq_iff_integers_le`, `TauCeti.Place.restrict_eq_iff_forall_ord_pos`
  and `TauCeti.Place.restrict_eq_iff_exists_ord_eq`: the three characterizations of `P' ∣ P`
  (Stichtenoth, Proposition 3.1.4), by the containment of valuation rings, by the containment of
  maximal ideals, and by the scaling of the order functions. Together with
  `TauCeti.Place.restrict` they say that every place of `F'` lies over exactly one place of `F`.
* `TauCeti.Place.restrict_eq_iff_isEquiv_comap`: `P' ∣ P` exactly when the restricted valuation
  is equivalent to that of `P`.
* `TauCeti.Place.linearIndependent_mul_pow_of_linearIndependent_residue`: the independence
  statement carrying the fundamental inequality, together with the three ingredients of its
  proof — `TauCeti.Place.ord_sum_eq_zero_of_isUnit`,
  `TauCeti.Place.sum_ne_zero_of_linearIndependent_residue` and
  `TauCeti.Place.ramificationIdx_dvd_ord_sum_of_linearIndependent_residue` — and the
  ultrametric estimate `TauCeti.Place.sum_ne_zero_of_ord_eq_mul_add_natCast` with
  `TauCeti.Place.ord_sum_le_of_ord_eq_mul_add_natCast` that combines them.
* `TauCeti.Place.ramificationIdx_mul_relativeDegree_le_finrank`: `e(P' ∣ P) · f(P' ∣ P) ≤
  [F' : F]`, with `TauCeti.Place.ramificationIdx_le_finrank` and
  `TauCeti.Place.relativeDegree_le_finrank` its two halves (Stichtenoth, Corollary 3.1.12).
* `TauCeti.Place.finiteDimensional_residueField_restrict`: the relative degree is finite, so it
  is not the junk value of `Module.finrank`; `TauCeti.Place.one_le_relativeDegree` and
  `TauCeti.Place.ramificationIdx_pos` are the matching lower bounds.
* `TauCeti.Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict`:
  `[k' : k] · deg P' = f(P' ∣ P) · deg P`, the comparison of the degrees of `P'` and of the place
  it lies over.
* `TauCeti.Place.isFractionRing_integralClosure`,
  `TauCeti.Place.isLocalization_integralClosure`,
  `TauCeti.Place.isDedekindDomain_integralClosure`,
  `TauCeti.Place.moduleFinite_integralClosure`, and
  `TauCeti.Place.isSeparable_fractionRing_integralClosure`: the fraction-field, localization,
  Dedekind, finiteness, and separability properties of the local integral closure `𝒪'_P`.
* `TauCeti.Place.isIntegral_algebraMap_iff_mem_integers`: the local integral closure `𝒪'_P`
  contracts to `𝒪_P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1.
-/

public section

open IsDedekindDomain

open scoped WithZero
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

section LocalModel

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F']

variable (F') (P : Place k F)

/-- **The valuation ring of a place of `F / k` acts on an extension field `F'`**, through `F`.

This is not a global instance: for `F' = F` it would compete with the action of a valuation
subring on its own field.  Install it, together with
`TauCeti.Place.isScalarTowerIntegersExtension`, with `attribute [local instance 10]` in any file
that works with the local model of the extension at `P` — at low priority, so that the case
`F' = F` still resolves to the valuation subring's own action, as the fraction-field instances
expect. -/
@[instance_reducible]
noncomputable def algebraIntegersExtension : Algebra (P.integers) F' :=
  ((algebraMap F F').comp (algebraMap (P.integers) F)).toAlgebra

attribute [local instance 10] algebraIntegersExtension

/-- The action of `TauCeti.Place.algebraIntegersExtension` on `F'` factors through `F`. -/
theorem isScalarTowerIntegersExtension : IsScalarTower (P.integers) F F' :=
  .of_algebraMap_eq fun _ ↦ rfl

attribute [local instance 10] isScalarTowerIntegersExtension

theorem algebraMap_integersExtension_injective :
    Function.Injective (algebraMap (P.integers) F') := by
  rw [IsScalarTower.algebraMap_eq (P.integers) F F', RingHom.coe_comp]
  exact (algebraMap F F').injective.comp (FaithfulSMul.algebraMap_injective (P.integers) F)

/-- **`𝒪'_P` contracts to `𝒪_P`**: a function of `F` is integral over `𝒪_P` in the extension `F'`
exactly when it is regular at `P`. So enlarging the field does not enlarge the ring of functions
of `F` integral over `𝒪_P`, and `𝒪'_P ∩ F = 𝒪_P`. -/
@[simp]
theorem isIntegral_algebraMap_iff_mem_integers {x : F} :
    IsIntegral ↥P.integers (algebraMap F F' x) ↔ x ∈ P.integers :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥P.integers F F')
      (algebraMap F F').injective (x := x)).trans
    ⟨fun hx ↦ P.mem_integers_of_isIntegral (fun r ↦ r.2) hx,
      fun hx ↦ isIntegral_algebraMap (x := (⟨x, hx⟩ : P.integers))⟩

instance isTorsionFree_integersExtension : Module.IsTorsionFree (P.integers) F' :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (algebraMap_integersExtension_injective F' P)

end LocalModel

section LocalIntegralClosure

omit [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [IsScalarTower k k' F']
  [IsScalarTower k F F']

variable (F') (P : Place k F)

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable [FiniteDimensional F F']

/-- The local model `𝒪'_P` — the integral closure of `𝒪_P` in `F'` — has fraction field `F'`. -/
instance isFractionRing_integralClosure :
    IsFractionRing (integralClosure (P.integers) F') F' :=
  IsIntegralClosure.isFractionRing_of_finite_extension (P.integers) F F' _

variable [Algebra.IsSeparable F F']

/-- The local model `𝒪'_P` is a Dedekind domain. -/
instance isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure (P.integers) F') :=
  integralClosure.isDedekindDomain (A := P.integers) (K := F) (L := F')

/-- The local model `𝒪'_P` is module-finite over `𝒪_P`. -/
instance moduleFinite_integralClosure :
    Module.Finite (P.integers) (integralClosure (P.integers) F') :=
  IsIntegralClosure.finite (A := P.integers) (K := F) (L := F') _

/-- Separability of `F' / F`, transported to the canonical fraction fields used by the
integral-closure API. -/
instance isSeparable_fractionRing_integralClosure :
    Algebra.IsSeparable (FractionRing (P.integers))
      (FractionRing (integralClosure (P.integers) F')) := by
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (P.integers) F).symm.toRingEquiv
    (FractionRing.algEquiv (integralClosure (P.integers) F') F').symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext (P.integers)⁰
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply (P.integers) (integralClosure (P.integers) F') F',
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end LocalIntegralClosure

section Constants

variable (k k' F') [Algebra.IsIntegral k k']

/-- **Enlarging an algebraic constant field does not change the places**: a valuation of `F'` is
trivial on `k` exactly when it is trivial on `k'`, because every nonzero element of `k'` is
algebraic over `k` and every nonzero element of `k` is one of `k'`.  So the places of `F' / k` and
the places of `F' / k'` are the same, with the same valuations. -/
def constantsEquiv : Place k F' ≃ Place k' F' where
  toFun Q :=
    { valuation := Q.valuation
      valuation_surjective := Q.valuation_surjective
      isTrivialOn := ⟨fun c hc ↦ Q.valuation_eq_one_of_isAlgebraic
        (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).isAlgebraic
        fun h ↦ hc ((algebraMap k' F').injective (by rw [h, map_zero]))⟩ }
  invFun Q :=
    { valuation := Q.valuation
      valuation_surjective := Q.valuation_surjective
      isTrivialOn := ⟨fun c hc ↦ by
        rw [IsScalarTower.algebraMap_apply k k' F']
        exact Q.isTrivialOn.eq_one _ fun h ↦
          hc ((algebraMap k k').injective (by rw [h, map_zero]))⟩ }
  left_inv _ := rfl
  right_inv _ := rfl

variable {k k' F'}

@[simp]
theorem valuation_constantsEquiv (Q : Place k F') :
    (constantsEquiv k k' F' Q).valuation = Q.valuation := (rfl)

@[simp]
theorem valuation_constantsEquiv_symm (Q : Place k' F') :
    ((constantsEquiv k k' F').symm Q).valuation = Q.valuation := (rfl)

@[simp]
theorem integers_constantsEquiv (Q : Place k F') :
    (constantsEquiv k k' F' Q).integers = Q.integers :=
  SetLike.ext fun x ↦ by rw [mem_integers_iff, mem_integers_iff, valuation_constantsEquiv]

@[simp]
theorem integers_constantsEquiv_symm (Q : Place k' F') :
    ((constantsEquiv k k' F').symm Q).integers = Q.integers :=
  SetLike.ext fun x ↦ by rw [mem_integers_iff, mem_integers_iff, valuation_constantsEquiv_symm]

end Constants

section Restrict

variable (k F) (P' : Place k' F')

/-- The valuation of `P'` restricted to `F` is trivial on the constants of `F`. -/
private theorem isTrivialOn_comap : (P'.valuation.comap (algebraMap F F')).IsTrivialOn k where
  eq_one c hc := by
    have hmap : algebraMap F F' (algebraMap k F c) = algebraMap k' F' (algebraMap k k' c) := by
      rw [← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k k' F']
    have hc' : algebraMap k k' c ≠ 0 := fun h ↦ hc
      ((algebraMap k k').injective (by rw [h, map_zero]))
    simpa only [Valuation.comap_apply, hmap] using P'.isTrivialOn.eq_one _ hc'

/-- The order function of `P'` restricted to `F` is the order function of the restricted
valuation. -/
private theorem ord_comap (f : F) :
    Valuation.ord (P'.valuation.comap (algebraMap F F')) f = P'.ord (algebraMap F F' f) := by
  rw [Valuation.ord_def, ord_def, Valuation.comap_apply]

/-- The valuation of `P'` restricted to `F` is nontrivial: an algebraic extension of a field
contained in a valuation ring is contained in that valuation ring, so a place of `F'` trivial on
`F` would have all of `F'` as its valuation ring. -/
private theorem ordIndex_comap_ne_zero [Algebra.IsIntegral F F'] :
    Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) ≠ 0 :=
  haveI := Valuation.isNontrivial_of_surjective P'.valuation_surjective
  haveI := Valuation.isNontrivial_comap_algebraMap (K := F) P'.valuation
  Valuation.ordIndex_ne_zero_of_isNontrivial _

variable [Algebra.IsIntegral F F']

/-- **The place of `F / k` that a place of `F' / k'` lies over**: the normalization of the
restriction of its valuation to `F` (Stichtenoth, Definition 3.1.2). Every place of `F'` lies
over exactly one place of `F`; which place is characterized in
`TauCeti.Place.restrict_eq_iff_integers_le`. -/
noncomputable def restrict : Place k F where
  valuation := (P'.valuation.comap (algebraMap F F')).normalization
  valuation_surjective :=
    Valuation.normalization_surjective _ (ordIndex_comap_ne_zero F P')
  isTrivialOn := by
    have := isTrivialOn_comap k F P'
    exact Valuation.IsTrivialOn.normalization _

/-- **The ramification index** `e(P' ∣ P)` of a place `P'` of `F' / k'` over the place `P` of
`F / k` it lies over: the factor by which the order function at `P'` scales the order function
at `P` (Stichtenoth, Definition 3.1.5). -/
noncomputable def ramificationIdx : ℕ :=
  Valuation.ordIndex (P'.valuation.comap (algebraMap F F'))

omit [Algebra.IsIntegral F F'] in
/-- The ramification index is the order index of the restricted valuation. -/
lemma ramificationIdx_def :
    ramificationIdx F P' = Valuation.ordIndex (P'.valuation.comap (algebraMap F F')) := by
  rw [ramificationIdx]

/-- The ramification index of a restricted place is positive. -/
theorem ramificationIdx_pos : 0 < ramificationIdx F P' :=
  Nat.pos_of_ne_zero (ordIndex_comap_ne_zero F P')

private theorem valuation_restrict :
    (P'.restrict k F).valuation = (P'.valuation.comap (algebraMap F F')).normalization := (rfl)

/-- **The defining property of the ramification index** (Stichtenoth, Definition 3.1.5): on `F`
the order function at `P'` is `e(P' ∣ P)` times the order function at `P`. -/
theorem ord_algebraMap_restrict (f : F) :
    P'.ord (algebraMap F F' f) = ramificationIdx F P' * (P'.restrict k F).ord f := by
  have key : (P'.restrict k F).ord f =
      Valuation.ord (P'.valuation.comap (algebraMap F F')).normalization f := by
    rw [ord_def, valuation_restrict, Valuation.ord_def]
  rw [← ord_comap F P' f, ramificationIdx, key,
    ← Valuation.ord_normalization_mul_ordIndex _ f, mul_comm]

/-- An element of `F` is integral at the restriction exactly when it is integral at `P'`. -/
theorem mem_integers_restrict_iff (f : F) :
    f ∈ (P'.restrict k F).integers ↔ algebraMap F F' f ∈ P'.integers := by
  rw [mem_integers_iff_ord_nonneg, mem_integers_iff_ord_nonneg, ord_algebraMap_restrict k F P' f]
  exact ⟨fun h ↦ mul_nonneg (by positivity) h,
    fun h ↦ nonneg_of_mul_nonneg_right h (by exact_mod_cast ramificationIdx_pos F P')⟩

/-- **`P' ∣ P` by valuation rings** (Stichtenoth, Proposition 3.1.4): the place of `F / k` that
`P'` lies over is the unique place whose valuation ring is carried into the valuation ring of
`P'`. -/
theorem restrict_eq_iff_integers_le (P : Place k F) :
    P'.restrict k F = P ↔ ∀ f ∈ P.integers, algebraMap F F' f ∈ P'.integers := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl f hf
    exact (mem_integers_restrict_iff k F P' f).mp hf
  · refine (eq_of_integers_le (SetLike.le_def.mpr fun f hf ↦ ?_)).symm
    exact (mem_integers_restrict_iff k F P' f).mpr (h f hf)

/-- **`P' ∣ P` by maximal ideals** (Stichtenoth, Proposition 3.1.4): it is enough that the
functions vanishing at `P` vanish at `P'`. -/
theorem restrict_eq_iff_forall_ord_pos (P : Place k F) :
    P'.restrict k F = P ↔ ∀ f : F, 0 < P.ord f → 0 < P'.ord (algebraMap F F' f) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl f hf
    rw [ord_algebraMap_restrict k F P' f]
    exact mul_pos (by exact_mod_cast ramificationIdx_pos F P') hf
  rw [restrict_eq_iff_integers_le]
  intro f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  rw [P.isUniformizer_iff_ord_eq_one] at ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hb : 0 < P'.ord (algebraMap F F' t) := h t (by omega)
  have hmap0 : algebraMap F F' f ≠ 0 := by simpa using hf0
  have hmapt0 : algebraMap F F' t ≠ 0 := by simpa using ht0
  refine P'.mem_integers_iff_ord_nonneg.mpr ?_
  by_contra hneg
  rw [not_le] at hneg
  set m := (P'.ord (algebraMap F F' t)).toNat with hm
  have hpos := h (f ^ m * t) (by
    rw [P.ord_mul (pow_ne_zero _ hf0) ht0, P.ord_pow, ht]
    have := P.mem_integers_iff_ord_nonneg.mp hf
    positivity)
  rw [map_mul, map_pow, P'.ord_mul (pow_ne_zero _ hmap0) hmapt0, P'.ord_pow] at hpos
  have hle : (m : ℤ) * P'.ord (algebraMap F F' f) ≤ -(m : ℤ) := by
    have : P'.ord (algebraMap F F' f) ≤ -1 := by omega
    nlinarith [Int.natCast_nonneg m]
  omega

/-- **`P' ∣ P` by the scaling of orders** (Stichtenoth, Proposition 3.1.4): the place `P'` lies
over `P` exactly when the order function at `P'` is a positive multiple of the order function at
`P` along `F`, and the multiple is then the ramification index. -/
theorem restrict_eq_iff_exists_ord_eq (P : Place k F) :
    P'.restrict k F = P ↔
      ∃ e : ℕ, 0 < e ∧ ∀ f : F, P'.ord (algebraMap F F' f) = e * P.ord f := by
  refine ⟨fun h ↦ ⟨ramificationIdx F P', ramificationIdx_pos F P', fun f ↦ ?_⟩, ?_⟩
  · rw [ord_algebraMap_restrict k F P' f, h]
  · rintro ⟨e, he, h⟩
    rw [restrict_eq_iff_forall_ord_pos]
    intro f hf
    rw [h f]
    exact mul_pos (by exact_mod_cast he) hf

end Restrict

section ResidueField

variable (k F) (P' : Place k' F') [Algebra.IsIntegral F F']

/-- The valuation ring of the restriction is carried into the valuation ring of `P'`, so the
latter is an algebra over the former. -/
noncomputable instance instAlgebraIntegers : Algebra (P'.restrict k F).integers P'.integers :=
  (((algebraMap F F').comp (algebraMap (P'.restrict k F).integers F)).codRestrict
    P'.integers fun x ↦ (mem_integers_restrict_iff k F P' (x : F)).mp x.2).toAlgebra

@[simp]
theorem coe_algebraMap_integers (x : (P'.restrict k F).integers) :
    ((algebraMap (P'.restrict k F).integers P'.integers x : P'.integers) : F') =
      algebraMap F F' (x : F) := (rfl)

/-- The valuation-ring algebra map is local, so it induces the residue-field extension used by
`relativeDegree`. -/
instance instIsLocalHomIntegers :
    IsLocalHom (algebraMap (P'.restrict k F).integers P'.integers) where
  map_nonunit a ha := by
    have ha0 : (a : F) ≠ 0 := by
      rintro h
      have ha_eq_zero : a = 0 := Subtype.ext h
      rw [ha_eq_zero] at ha
      simp at ha
    have hmap0 : algebraMap F F' (a : F) ≠ 0 := by simpa using ha0
    have h1 : P'.ord (algebraMap F F' (a : F)) = 0 :=
      (P'.isUnit_iff_ord_eq_zero (x := algebraMap _ P'.integers a) (by simpa using hmap0)).mp ha
    rw [ord_algebraMap_restrict k F P' (a : F)] at h1
    have he : (ramificationIdx F P' : ℤ) ≠ 0 := by
      have := ramificationIdx_pos F P'
      omega
    exact ((P'.restrict k F).isUnit_iff_ord_eq_zero ha0).mpr
      ((mul_eq_zero.mp h1).resolve_left he)

/-- The **relative degree** `f(P' ∣ P) = [F'_{P'} : F_P]` of a place `P'` of `F' / k'` over the
place `P` of `F / k` it lies over (Stichtenoth, Definition 3.1.5). -/
noncomputable def relativeDegree : ℕ :=
  Module.finrank (P'.restrict k F).ResidueField P'.ResidueField

/-- The relative degree is the finrank of the extension of residue fields. -/
theorem relativeDegree_def :
    relativeDegree k F P' = Module.finrank (P'.restrict k F).ResidueField P'.ResidueField := by
  rw [relativeDegree]

end ResidueField

section Independence

variable (k F) (P' : Place k' F') [Algebra.IsIntegral F F']

end Independence

section RamificationIdxBound

variable (F) (P' : Place k' F')

variable [FiniteDimensional F F']

end RamificationIdxBound

section Bound

variable (k F) (P' : Place k' F') [FiniteDimensional F F']

end Bound

section Self

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- **A place restricts to itself along the identity extension.** Restriction normalizes the
valuation pulled back along `algebraMap F F`, which is the identity, and a place's valuation is
already surjective, hence already normalized. -/
@[simp]
theorem restrict_self : restrict k F P = P := by
  refine Place.ext ?_
  rw [valuation_restrict, Algebra.algebraMap_self, Valuation.comap_id,
    Valuation.normalization_eq_self_of_surjective _ P.valuation_surjective]

/-- **The identity extension is unramified**: `e(P ∣ P) = 1`. -/
@[simp]
theorem ramificationIdx_self : ramificationIdx F P = 1 := by
  rw [ramificationIdx_def, Algebra.algebraMap_self, Valuation.comap_id,
    Valuation.ordIndex_eq_one_of_surjective _ P.valuation_surjective]

end Self

end Place

end TauCeti
