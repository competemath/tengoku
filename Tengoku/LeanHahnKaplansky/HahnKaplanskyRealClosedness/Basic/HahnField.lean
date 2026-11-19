/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hahn field primitives and valuation normalization
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

/-- The lexicographically ordered full Hahn field `k((Γ))`.-/
abbrev HahnField (k Γ : Type*) [LinearOrder Γ] [Zero k] :=
  Lex k⟦Γ⟧

namespace HahnField

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

instance instField : Field (HahnField k Γ) :=
  inferInstance

instance instLinearOrder : LinearOrder (HahnField k Γ) :=
  inferInstance

instance instIsStrictOrderedRing : IsStrictOrderedRing (HahnField k Γ) :=
  inferInstance

/-- The ring homomorphism forgetting the `Lex` type synonym.-/
def ofLexRingHom : HahnField k Γ →+* k⟦Γ⟧ where
  toFun := ofLex
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem ofLexRingHom_apply (x : HahnField k Γ) :
    ofLexRingHom k Γ x = ofLex x :=
  rfl

/-- The natural additive valuation on the lexicographically ordered Hahn field.-/
def addVal : AddValuation (HahnField k Γ) (WithTop Γ) :=
  (HahnSeries.addVal Γ k).comap (ofLexRingHom k Γ)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem addVal_apply (x : HahnField k Γ) :
    addVal k Γ x = (ofLex x).orderTop :=
  rfl

/-- The natural Hahn valuation in multiplicative convention.-/
def valuation : Valuation (HahnField k Γ) (Multiplicative (WithTop Γ)ᵒᵈ) :=
  AddValuation.toValuation (addVal k Γ)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem valuation_apply (x : HahnField k Γ) :
    valuation k Γ x = Multiplicative.ofAdd (OrderDual.toDual (addVal k Γ x)) :=
  rfl

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- If the value group is subsingleton, a Hahn series is just its coefficient at `0`.-/
noncomputable def hahnSeriesSubsingletonRingEquiv [Subsingleton Γ] : k⟦Γ⟧ ≃+* k where
  toFun x := x.coeff 0
  invFun r := HahnSeries.single 0 r
  left_inv x := by
    ext γ
    have hγ : γ = 0 := Subsingleton.elim γ 0
    simp [hγ]
  right_inv r := by
    simp [HahnSeries.coeff_single_same]
  map_mul' x y := by
    have hx : x = HahnSeries.single 0 (x.coeff 0) := by
      ext γ
      have hγ : γ = 0 := Subsingleton.elim γ 0
      simp [hγ]
    have hy : y = HahnSeries.single 0 (y.coeff 0) := by
      ext γ
      have hγ : γ = 0 := Subsingleton.elim γ 0
      simp [hγ]
    rw [hx, hy, HahnSeries.single_mul_single]
    simp [HahnSeries.coeff_single_same]
  map_add' x y := by
    simp [HahnSeries.coeff_add]

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- If the value group is subsingleton, the lexicographically ordered Hahn field is ring
equivalent to the coefficient field.-/
noncomputable def subsingletonValueGroupRingEquiv [Subsingleton Γ] :
    HahnField k Γ ≃+* k where
  toFun x := (ofLex x).coeff 0
  invFun r := toLex (HahnSeries.single 0 r)
  left_inv x := by
    apply toLex.injective
    exact (hahnSeriesSubsingletonRingEquiv k Γ).left_inv (ofLex x)
  right_inv r := by
    exact (hahnSeriesSubsingletonRingEquiv k Γ).right_inv r
  map_mul' x y := by
    exact (hahnSeriesSubsingletonRingEquiv k Γ).map_mul' (ofLex x) (ofLex y)
  map_add' x y := by
    exact (hahnSeriesSubsingletonRingEquiv k Γ).map_add' (ofLex x) (ofLex y)

@[simp]
theorem addVal_single (γ : Γ) :
    addVal k Γ (toLex (HahnSeries.single γ (1 : k))) = (γ : WithTop Γ) := by
  rw [addVal_apply]
  exact HahnSeries.orderTop_single one_ne_zero

/-- The coefficient-one Hahn monomial of exponent `γ`, viewed in the lexicographically ordered
Hahn field.-/
def hahnMonomial (γ : Γ) : HahnField k Γ :=
  toLex (HahnSeries.single γ (1 : k))

omit [LinearOrder k] [IsStrictOrderedRing k] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
@[simp]
theorem hahnMonomial_apply (γ : Γ) :
    hahnMonomial k Γ γ = toLex (HahnSeries.single γ (1 : k)) :=
  rfl

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
@[simp]
theorem hahnMonomial_ne_zero (γ : Γ) : hahnMonomial k Γ γ ≠ 0 := by
  simp [hahnMonomial]

@[simp]
theorem addVal_hahnMonomial (γ : Γ) :
    addVal k Γ (hahnMonomial k Γ γ) = (γ : WithTop Γ) := by
  exact addVal_single k Γ γ

omit [LinearOrder k] [IsStrictOrderedRing k] in
theorem addVal_single_of_ne {γ : Γ} {r : k} (hr : r ≠ 0) :
    addVal k Γ (toLex (HahnSeries.single γ r)) = (γ : WithTop Γ) := by
  rw [addVal_apply]
  exact HahnSeries.orderTop_single hr

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- The monomial with coefficient `1` is positive in the lexicographic Hahn order.-/
theorem single_one_pos (γ : Γ) :
    0 < (toLex (HahnSeries.single γ (1 : k)) : HahnField k Γ) := by
  rw [← HahnSeries.leadingCoeff_pos_iff]
  simp [HahnSeries.leadingCoeff_of_single]

/-- Multiplication by a positive Hahn monomial preserves positivity.-/
theorem single_one_mul_pos_iff (γ : Γ) (x : HahnField k Γ) :
    0 < toLex (HahnSeries.single γ (1 : k)) * x ↔ 0 < x := by
  exact mul_pos_iff_of_pos_left (single_one_pos k Γ γ)

/-- The inverse-value monomial used for normalization preserves positivity.-/
theorem normalized_monomial_mul_pos_iff (γ : Γ) (x : HahnField k Γ) :
    0 < toLex (HahnSeries.single (-γ) (1 : k)) * x ↔ 0 < x :=
  single_one_mul_pos_iff k Γ (-γ) x

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- Divisibility of the value group lets us divide a positive value by a positive natural.-/
theorem exists_pos_nsmul_eq [DivisibleBy Γ ℕ] {m : ℕ} {γ : Γ}
    (hm : 0 < m) (hγ : 0 < γ) :
    ∃ δ : Γ, 0 < δ ∧ m • δ = γ := by
  let δ : Γ := DivisibleBy.div γ m
  have hδeq : m • δ = γ := DivisibleBy.div_cancel γ (Nat.ne_zero_of_lt hm)
  refine ⟨δ, ?_, hδeq⟩
  apply (nsmul_pos_iff (Nat.ne_zero_of_lt hm)).mp
  simpa [hδeq] using hγ

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- In a nontrivial linearly ordered additive group, a finite set has a strict lower bound.-/
theorem exists_lt_all_finset [Nontrivial Γ] (s : Finset Γ) :
    ∃ δ : Γ, ∀ a ∈ s, δ < a := by
  classical
  by_cases hs : s.Nonempty
  · rcases exists_lt (s.min' hs) with ⟨δ, hδ⟩
    refine ⟨δ, ?_⟩
    intro a ha
    exact lt_of_lt_of_le hδ (Finset.min'_le s a ha)
  · refine ⟨0, ?_⟩
    intro a ha
    exact False.elim (hs ⟨a, ha⟩)

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- A finite family in a nontrivial linearly ordered additive group has a strict lower bound.-/
theorem exists_lt_all_finset_image [Nontrivial Γ] {ι : Type*} (s : Finset ι)
    (f : ι → Γ) :
    ∃ δ : Γ, ∀ i ∈ s, δ < f i := by
  classical
  rcases exists_lt_all_finset (Γ := Γ) (s.image f) with ⟨δ, hδ⟩
  refine ⟨δ, ?_⟩
  intro i hi
  exact hδ (f i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- Strict comparison with a divisible quotient, in additive notation.-/
theorem nsmul_lt_of_lt_div [DivisibleBy Γ ℕ] {m : ℕ} (hm : m ≠ 0) {δ a : Γ}
    (hδ : δ < DivisibleBy.div a m) :
    m • δ < a := by
  calc
    m • δ < m • DivisibleBy.div a m := nsmul_lt_nsmul_right hm hδ
    _ = a := DivisibleBy.div_cancel a hm

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- Algebraic rearrangement used by top-degree scaling.-/
theorem scaledValue_sub_eq {n i : ℕ} (hi : i ≤ n) (γn vi δ : Γ) :
    -(γn + n • δ) + vi + i • δ = vi - γn - (n - i) • δ := by
  have hn : n = n - i + i := by omega
  nth_rw 1 [hn]
  rw [add_nsmul]
  abel

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- The top coefficient has scaled value zero when `lam = γn + n • δ`.-/
theorem scaledValue_natDegree_eq_zero (n : ℕ) (γn δ : Γ) :
    -(γn + n • δ) + γn + n • δ = 0 := by
  abel

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- Dominance of the natural-degree slope gives strict positivity of a lower scaled value.-/
theorem scaledValue_pos_of_dominating {n i : ℕ} (hi : i ≤ n) {γn vi δ : Γ}
    (hdom : (n - i) • δ < vi - γn) :
    0 < -(γn + n • δ) + vi + i • δ := by
  calc
    0 < vi - γn - (n - i) • δ := sub_pos.mpr hdom
    _ = -(γn + n • δ) + vi + i • δ := (scaledValue_sub_eq (Γ := Γ) hi γn vi δ).symm

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- WithTop form of `scaledValue_natDegree_eq_zero`.-/
theorem withTop_scaledValue_natDegree_eq_zero (n : ℕ) (γn δ : Γ) :
    (-(γn + n • δ : Γ) : WithTop Γ) + (γn : WithTop Γ) +
        n • (δ : WithTop Γ) =
      0 := by
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  rw [← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_add]
  change ((-(γn + n • δ) + γn + n • δ : Γ) : WithTop Γ) =
    ((0 : Γ) : WithTop Γ)
  rw [scaledValue_natDegree_eq_zero]

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- WithTop form of lower scaled-value positivity.-/
theorem withTop_scaledValue_pos_of_dominating {n i : ℕ} (hi : i ≤ n)
    {γn vi δ : Γ} (hdom : (n - i) • δ < vi - γn) :
    (0 : WithTop Γ) <
      (-(γn + n • δ : Γ) : WithTop Γ) + (vi : WithTop Γ) + i • (δ : WithTop Γ) := by
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  rw [← WithTop.coe_nsmul, ← WithTop.coe_add, ← WithTop.coe_add]
  exact WithTop.coe_lt_coe.mpr (scaledValue_pos_of_dominating (Γ := Γ) hi hdom)

/-- The finite Hahn value of a nonzero polynomial coefficient, packaged using membership in the
polynomial support.-/
noncomputable def coeffValueOfMemSupport (F : (HahnField k Γ)[X]) {i : ℕ}
    (hi : i ∈ F.support) : Γ :=
  (addVal k Γ (F.coeff i)).untop
    (by
      have hcoeff : F.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
      simpa [AddValuation.ne_top_iff] using hcoeff)

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- `coeffValueOfMemSupport` really is the additive valuation of the coefficient.-/
theorem addVal_coeff_eq_coeffValueOfMemSupport (F : (HahnField k Γ)[X]) {i : ℕ}
    (hi : i ∈ F.support) :
    addVal k Γ (F.coeff i) = (coeffValueOfMemSupport k Γ F hi : WithTop Γ) := by
  dsimp [coeffValueOfMemSupport]
  exact (WithTop.coe_untop _ _).symm

/-- The finite Newton weight `v(F_i) + iγ` of a nonzero coefficient.-/
noncomputable def newtonWeightOfMemSupport (F : (HahnField k Γ)[X]) (γ : Γ) {i : ℕ}
    (hi : i ∈ F.support) : Γ :=
  coeffValueOfMemSupport k Γ F hi + i • γ

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- The `WithTop` expression for a coefficient weight is finite on the support.-/
theorem withTop_newtonWeightOfMemSupport_eq (F : (HahnField k Γ)[X]) (γ : Γ)
    {i : ℕ} (hi : i ∈ F.support) :
    addVal k Γ (F.coeff i) + i • (γ : WithTop Γ) =
      (newtonWeightOfMemSupport k Γ F γ hi : WithTop Γ) := by
  rw [addVal_coeff_eq_coeffValueOfMemSupport k Γ F hi, ← WithTop.coe_nsmul,
    ← WithTop.coe_add]
  rfl

/-- The `WithTop` Newton weight `v(F_i) + iγ`, also defined for zero coefficients.-/
noncomputable def newtonWeight (F : (HahnField k Γ)[X]) (γ : Γ) (i : ℕ) : WithTop Γ :=
  addVal k Γ (F.coeff i) + i • (γ : WithTop Γ)

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- On the support, `newtonWeight` agrees with the finite Newton weight.-/
theorem newtonWeight_eq_of_mem_support (F : (HahnField k Γ)[X]) (γ : Γ)
    {i : ℕ} (hi : i ∈ F.support) :
    newtonWeight k Γ F γ i = (newtonWeightOfMemSupport k Γ F γ hi : WithTop Γ) :=
  withTop_newtonWeightOfMemSupport_eq k Γ F γ hi

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem newtonWeight_eq_top_of_notMem_support (F : (HahnField k Γ)[X]) (γ : Γ)
    {i : ℕ} (hi : i ∉ F.support) :
    newtonWeight k Γ F γ i = ⊤ := by
  rw [newtonWeight, Polynomial.notMem_support_iff.mp hi, AddValuation.map_zero]
  simp

/-- The finite support indices whose Newton weight is exactly `μ`.-/
noncomputable def newtonInitialSupport (F : (HahnField k Γ)[X]) (γ μ : Γ) : Finset ℕ :=
  F.support.filter fun i => newtonWeight k Γ F γ i = (μ : WithTop Γ)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem mem_newtonInitialSupport (F : (HahnField k Γ)[X]) (γ μ : Γ) {i : ℕ} :
    i ∈ newtonInitialSupport k Γ F γ μ ↔
      i ∈ F.support ∧ newtonWeight k Γ F γ i = (μ : WithTop Γ) := by
  simp [newtonInitialSupport]

/-- The coefficient contributed by `F_i` to the initial polynomial at slope `γ` and weight `μ`.-/
noncomputable def newtonInitialCoeff (F : (HahnField k Γ)[X]) (γ μ : Γ) (i : ℕ) : k :=
  if i ∈ newtonInitialSupport k Γ F γ μ then
    (ofLex (F.coeff i)).coeff (μ - i • γ)
  else 0

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem newtonInitialCoeff_of_notMem (F : (HahnField k Γ)[X]) (γ μ : Γ) {i : ℕ}
    (hi : i ∉ newtonInitialSupport k Γ F γ μ) :
    newtonInitialCoeff k Γ F γ μ i = 0 := by
  simp [newtonInitialCoeff, hi]

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem newtonInitialCoeff_of_mem (F : (HahnField k Γ)[X]) (γ μ : Γ) {i : ℕ}
    (hi : i ∈ newtonInitialSupport k Γ F γ μ) :
    newtonInitialCoeff k Γ F γ μ i = (ofLex (F.coeff i)).coeff (μ - i • γ) := by
  simp [newtonInitialCoeff, hi]

/-- The initial polynomial at slope `γ` and weight `μ`, formed from the coefficients whose
Newton weight is exactly `μ`.-/
noncomputable def newtonInitialPolynomial (F : (HahnField k Γ)[X]) (γ μ : Γ) : k[X] :=
  ∑ i ∈ newtonInitialSupport k Γ F γ μ,
    Polynomial.C (newtonInitialCoeff k Γ F γ μ i) * Polynomial.X ^ i

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem coeff_newtonInitialPolynomial (F : (HahnField k Γ)[X]) (γ μ : Γ) (i : ℕ) :
    (newtonInitialPolynomial k Γ F γ μ).coeff i = newtonInitialCoeff k Γ F γ μ i := by
  classical
  rw [newtonInitialPolynomial, Polynomial.finsetSum_coeff]
  by_cases hi : i ∈ newtonInitialSupport k Γ F γ μ
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul_X_pow]
      simp
    · intro j hj hji
      rw [Polynomial.coeff_C_mul_X_pow]
      simp [Ne.symm hji]
    · intro hnot
      exact False.elim (hnot hi)
  · rw [Finset.sum_eq_zero]
    · rw [newtonInitialCoeff_of_notMem k Γ F γ μ hi]
    · intro j hj
      rw [Polynomial.coeff_C_mul_X_pow]
      have hne : i ≠ j := by
        intro hij
        subst j
        exact hi hj
      simp [hne]

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- Every index in the initial support contributes a nonzero coefficient.-/
theorem newtonInitialCoeff_ne_zero_of_mem (F : (HahnField k Γ)[X]) (γ μ : Γ)
    {i : ℕ} (hi : i ∈ newtonInitialSupport k Γ F γ μ) :
    newtonInitialCoeff k Γ F γ μ i ≠ 0 := by
  rcases (mem_newtonInitialSupport k Γ F γ μ).mp hi with ⟨hisupp, hweight⟩
  have hweight' :
      (newtonWeightOfMemSupport k Γ F γ hisupp : WithTop Γ) = (μ : WithTop Γ) := by
    rw [← newtonWeight_eq_of_mem_support k Γ F γ hisupp]
    exact hweight
  have hweightΓ : newtonWeightOfMemSupport k Γ F γ hisupp = μ :=
    WithTop.coe_injective hweight'
  have hvalue :
      coeffValueOfMemSupport k Γ F hisupp = μ - i • γ := by
    rw [← hweightΓ]
    dsimp [newtonWeightOfMemSupport]
    abel
  have hval :
      addVal k Γ (F.coeff i) = ((μ - i • γ : Γ) : WithTop Γ) := by
    rw [addVal_coeff_eq_coeffValueOfMemSupport k Γ F hisupp, hvalue]
  rw [newtonInitialCoeff_of_mem k Γ F γ μ hi]
  exact HahnSeries.coeff_orderTop_ne (by simpa [addVal_apply] using hval)

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- An erased support index is strictly below the natural degree.-/
theorem lt_natDegree_of_mem_support_erase_natDegree {R : Type*} [Semiring R]
    {F : R[X]} {i : ℕ} (hi : i ∈ F.support.erase F.natDegree) :
    i < F.natDegree := by
  rcases Finset.mem_erase.mp hi with ⟨hine, hisupp⟩
  exact lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hisupp) hine

omit [Field k] [LinearOrder k] [IsStrictOrderedRing k] in
/-- A support index below the natural degree gives a nonzero natural difference.-/
theorem natDegree_sub_ne_zero_of_mem_support_erase_natDegree {R : Type*} [Semiring R]
    {F : R[X]} {i : ℕ} (hi : i ∈ F.support.erase F.natDegree) :
    F.natDegree - i ≠ 0 := by
  exact Nat.ne_of_gt (Nat.sub_pos_of_lt (lt_natDegree_of_mem_support_erase_natDegree hi))

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- Divisibility of the value group gives exact `n`-th roots of coefficient-one monomials.-/
theorem single_one_pow_div_eq_single [DivisibleBy Γ ℕ] {n : ℕ} (hn : n ≠ 0) (γ : Γ) :
    (toLex (HahnSeries.single (DivisibleBy.div γ n) (1 : k)) : HahnField k Γ) ^ n =
      toLex (HahnSeries.single γ (1 : k)) := by
  change toLex (HahnSeries.single (DivisibleBy.div γ n) (1 : k) ^ n) =
    toLex (HahnSeries.single γ (1 : k))
  rw [HahnSeries.single_pow, DivisibleBy.div_cancel γ hn]
  simp

/-- Multiplying by the inverse-value monomial normalizes a series of finite value to value zero.-/
theorem addVal_single_neg_mul_of_addVal_eq {x : HahnField k Γ} {γ : Γ}
    (hx : addVal k Γ x = (γ : WithTop Γ)) :
    addVal k Γ (toLex (HahnSeries.single (-γ) (1 : k)) * x) = 0 := by
  rw [AddValuation.map_mul, addVal_single, hx]
  simp

/-- Scale a Hahn-field polynomial by replacing `X` with `T^δ X` and multiplying all
coefficients by `T^{-lam}`.  This is the polynomial-side operation used in the top-degree cluster
normalization.-/
noncomputable def scalePolynomial (F : (HahnField k Γ)[X]) (δ lam : Γ) :
    (HahnField k Γ)[X] :=
  Polynomial.C (hahnMonomial k Γ (-lam)) *
    F.comp (Polynomial.C (hahnMonomial k Γ δ) * Polynomial.X)

omit [LinearOrder k] [IsStrictOrderedRing k] in
@[simp]
theorem eval_scalePolynomial (F : (HahnField k Γ)[X]) (δ lam : Γ) (y : HahnField k Γ) :
    (scalePolynomial k Γ F δ lam).eval y =
      hahnMonomial k Γ (-lam) * F.eval (hahnMonomial k Γ δ * y) := by
  simp [scalePolynomial, Polynomial.eval_comp]

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- Coefficients of `scalePolynomial`: the `n`-th coefficient is multiplied by
`T^{-lam} * T^{nδ}`.-/
@[simp]
theorem coeff_scalePolynomial (F : (HahnField k Γ)[X]) (δ lam : Γ) (n : ℕ) :
    (scalePolynomial k Γ F δ lam).coeff n =
      hahnMonomial k Γ (-lam) * F.coeff n * (hahnMonomial k Γ δ) ^ n := by
  rw [scalePolynomial, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  ring

/-- A root of a scaled polynomial pulls back to a root of the original polynomial.-/
theorem isRoot_of_scalePolynomial_isRoot {F : (HahnField k Γ)[X]} {δ lam : Γ}
    {y : HahnField k Γ} (hy : (scalePolynomial k Γ F δ lam).IsRoot y) :
    F.IsRoot (hahnMonomial k Γ δ * y) := by
  rw [Polynomial.IsRoot] at hy ⊢
  rw [eval_scalePolynomial] at hy
  exact (mul_eq_zero.mp hy).resolve_left (hahnMonomial_ne_zero k Γ (-lam))

/-- Existential root transport for `scalePolynomial`.-/
theorem exists_root_of_scalePolynomial_root {F : (HahnField k Γ)[X]} {δ lam : Γ}
    (hroot : ∃ y : HahnField k Γ, (scalePolynomial k Γ F δ lam).IsRoot y) :
    ∃ x : HahnField k Γ, F.IsRoot x := by
  rcases hroot with ⟨y, hy⟩
  exact ⟨hahnMonomial k Γ δ * y, isRoot_of_scalePolynomial_isRoot k Γ hy⟩

/-- A nonzero Hahn-field polynomial admits a scalar normalization whose coefficients all have
nonnegative valuation and at least one coefficient has valuation zero.-/
theorem exists_coeff_normalizing_scalar {f : (HahnField k Γ)[X]} (hf : f ≠ 0) :
    ∃ c : HahnField k Γ, c ≠ 0 ∧
      (∀ n : ℕ, (0 : WithTop Γ) ≤ addVal k Γ (c * f.coeff n)) ∧
      ∃ n : ℕ, addVal k Γ (c * f.coeff n) = 0 := by
  classical
  rcases Finset.exists_min_image f.support (fun n => addVal k Γ (f.coeff n))
      ((Polynomial.support_nonempty (p := f)).mpr hf) with
    ⟨n₀, hn₀, hmin⟩
  have hcoeff₀_ne : f.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  let γ : Γ := (addVal k Γ (f.coeff n₀)).untop
    (by simpa [AddValuation.ne_top_iff] using hcoeff₀_ne)
  have hval₀ : addVal k Γ (f.coeff n₀) = (γ : WithTop Γ) := by
    dsimp [γ]
    exact (WithTop.coe_untop _ _).symm
  let c : HahnField k Γ := toLex (HahnSeries.single (-γ) (1 : k))
  refine ⟨c, by dsimp [c]; simp, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ f.support
    · have hcoeff_ne : f.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
      let δ : Γ := (addVal k Γ (f.coeff n)).untop
        (by simpa [AddValuation.ne_top_iff] using hcoeff_ne)
      have hvaln : addVal k Γ (f.coeff n) = (δ : WithTop Γ) := by
        dsimp [δ]
        exact (WithTop.coe_untop _ _).symm
      have hγδ : γ ≤ δ := by
        apply WithTop.coe_le_coe.mp
        rw [← hval₀, ← hvaln]
        exact hmin n hn
      rw [AddValuation.map_mul, addVal_single, hvaln]
      change (0 : WithTop Γ) ≤ ((-γ + δ : Γ) : WithTop Γ)
      exact WithTop.coe_le_coe.mpr (by
        rw [add_comm, ← sub_eq_add_neg]
        exact sub_nonneg.mpr hγδ)
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero, AddValuation.map_zero]
      exact le_top
  · refine ⟨n₀, ?_⟩
    rw [AddValuation.map_mul, addVal_single, hval₀]
    simp

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- A Hahn series with finite value `γ` has leading coefficient equal to its `γ`-coefficient.-/
theorem leadingCoeff_eq_coeff_of_addVal_eq {x : HahnField k Γ} {γ : Γ}
    (hx : addVal k Γ x = (γ : WithTop Γ)) :
    (ofLex x).leadingCoeff = (ofLex x).coeff γ := by
  have hxne : x ≠ 0 := by
    intro h
    simp [h] at hx
  rw [HahnSeries.leadingCoeff_of_ne_zero (by simpa using hxne)]
  apply congrArg (fun γ => (ofLex x).coeff γ)
  apply WithTop.coe_injective
  rw [WithTop.coe_untop]
  exact hx

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- A Hahn series of value zero has leading coefficient equal to its constant coefficient.-/
theorem leadingCoeff_eq_coeff_zero_of_addVal_eq_zero {x : HahnField k Γ}
    (hx : addVal k Γ x = 0) :
    (ofLex x).leadingCoeff = (ofLex x).coeff 0 := by
  exact leadingCoeff_eq_coeff_of_addVal_eq k Γ hx

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- If all terms below `γ` vanish and the coefficient at `γ` also vanishes, then the valuation is
strictly larger than `γ`.-/
theorem lt_addVal_of_le_addVal_of_coeff_eq_zero {x : HahnField k Γ} {γ : Γ}
    (hle : (γ : WithTop Γ) ≤ addVal k Γ x) (hcoeff : (ofLex x).coeff γ = 0) :
    (γ : WithTop Γ) < addVal k Γ x := by
  refine lt_of_le_of_ne hle ?_
  intro heq
  have horder : (ofLex x).orderTop = γ := by
    simpa [addVal_apply] using heq.symm
  exact HahnSeries.coeff_orderTop_ne horder hcoeff

omit [LinearOrder k] [IsStrictOrderedRing k] in
/-- A common valuation lower bound is preserved by addition.-/
theorem le_addVal_add_of_le_addVal {x y : HahnField k Γ} {γ : WithTop Γ}
    (hx : γ ≤ addVal k Γ x) (hy : γ ≤ addVal k Γ y) :
    γ ≤ addVal k Γ (x + y) := by
  rw [addVal_apply]
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro j hj
  change (ofLex x + ofLex y).coeff j = 0
  rw [HahnSeries.coeff_add]
  have hxj : (ofLex x).coeff j = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    simpa [addVal_apply] using hj.trans_le hx
  have hyj : (ofLex y).coeff j = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    simpa [addVal_apply] using hj.trans_le hy
  simp [hxj, hyj]

/-- The natural additive Hahn valuation is onto `WithTop Γ`.-/
theorem addVal_surjective : Function.Surjective (addVal k Γ) := by
  intro γ
  cases γ with
  | top =>
      exact ⟨0, by simp⟩
  | coe γ =>
      exact ⟨toLex (HahnSeries.single γ (1 : k)), addVal_single k Γ γ⟩

/-- The natural multiplicative Hahn valuation is onto its chosen codomain.-/
theorem valuation_surjective : Function.Surjective (valuation k Γ) := by
  intro γ
  rcases addVal_surjective k Γ (OrderDual.ofDual (Multiplicative.toAdd γ)) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [valuation_apply, hx]
  simp

/-- The value group of the natural Hahn valuation.-/
abbrev valueGroup : Type _ :=
  MonoidWithZeroHom.ValueGroup₀ (valuation k Γ).toMonoidWithZeroHom

/-- The canonical embedding of the value group into the chosen codomain is onto.-/
theorem valueGroupEmbedding_surjective :
    Function.Surjective
      (MonoidWithZeroHom.ValueGroup₀.embedding
        (f := (valuation k Γ).toMonoidWithZeroHom)) := by
  intro γ
  rcases valuation_surjective k Γ γ with ⟨x, hx⟩
  refine ⟨(valuation k Γ).restrict x, ?_⟩
  change
    MonoidWithZeroHom.ValueGroup₀.embedding
      (MonoidWithZeroHom.ValueGroup₀.restrict₀ (valuation k Γ).toMonoidWithZeroHom x) = γ
  exact (MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀
    (f := (valuation k Γ).toMonoidWithZeroHom) x).trans hx

/-- The valuation subring of the natural Hahn valuation, written using the additive valuation.

Its elements are exactly the Hahn series whose leading exponent is nonnegative, together with `0`.-/
def valuationSubring : Subring (HahnField k Γ) where
  carrier := {x | (0 : WithTop Γ) ≤ addVal k Γ x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy := (addVal k Γ).map_le_add hx hy
  neg_mem' {x} hx := by
    change (0 : WithTop Γ) ≤ addVal k Γ x at hx
    change (0 : WithTop Γ) ≤ addVal k Γ (-x)
    simpa only [AddValuation.map_neg] using hx
  mul_mem' {x y} hx hy := by
    change (0 : WithTop Γ) ≤ addVal k Γ (x * y)
    rw [AddValuation.map_mul]
    exact add_nonneg hx hy

@[simp]
theorem mem_valuationSubring_iff (x : HahnField k Γ) :
    x ∈ valuationSubring k Γ ↔ (0 : WithTop Γ) ≤ addVal k Γ x :=
  Iff.rfl

/-- After scalar normalization, a nonzero Hahn-field polynomial is the image of a nonzero
polynomial over the natural valuation subring.-/
theorem exists_integral_scalar_multiple {f : (HahnField k Γ)[X]} (hf : f ≠ 0) :
    ∃ c : HahnField k Γ, c ≠ 0 ∧
      ∃ g : (valuationSubring k Γ)[X],
        g.map (algebraMap (valuationSubring k Γ) (HahnField k Γ)) = Polynomial.C c * f ∧
          g ≠ 0 := by
  rcases exists_coeff_normalizing_scalar k Γ hf with ⟨c, hc0, hcoeff, n₀, hn₀⟩
  have hlifts :
      Polynomial.C c * f ∈
        Polynomial.lifts (algebraMap (valuationSubring k Γ) (HahnField k Γ)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨c * f.coeff n, ?_⟩, ?_⟩
    · change (0 : WithTop Γ) ≤ addVal k Γ (c * f.coeff n)
      exact hcoeff n
    · rw [Polynomial.coeff_C_mul]
      rfl
  rcases (Polynomial.mem_lifts (f := algebraMap (valuationSubring k Γ) (HahnField k Γ))
      (Polynomial.C c * f)).mp hlifts with ⟨g, hg⟩
  refine ⟨c, hc0, g, hg, ?_⟩
  intro hg0
  have hcoeff_zero : (Polynomial.C c * f).coeff n₀ = 0 := by
    rw [← hg, hg0]
    simp
  rw [Polynomial.coeff_C_mul] at hcoeff_zero
  have htop : addVal k Γ (c * f.coeff n₀) = ⊤ := by
    rw [hcoeff_zero, AddValuation.map_zero]
  rw [hn₀] at htop
  exact (WithTop.coe_ne_top : ((0 : Γ) : WithTop Γ) ≠ ⊤) htop

/-- The natural Hahn valuation subring, packaged as mathlib's `ValuationSubring`.-/
def valuationSubringValuationSubring : ValuationSubring (HahnField k Γ) :=
  ValuationSubring.ofSubring (valuationSubring k Γ) fun x => by
    by_cases hx : x ∈ valuationSubring k Γ
    · exact Or.inl hx
    · right
      change (0 : WithTop Γ) ≤ addVal k Γ x⁻¹
      by_cases hx0 : x = 0
      · simp [hx0]
      by_contra hinv
      have hxlt : addVal k Γ x < 0 := lt_of_not_ge hx
      have hinvlt : addVal k Γ x⁻¹ < 0 := lt_of_not_ge hinv
      have hmul_lt : addVal k Γ (x * x⁻¹) < (0 : WithTop Γ) + 0 := by
        rw [AddValuation.map_mul]
        exact WithTop.add_lt_add hxlt hinvlt
      rw [mul_inv_cancel₀ hx0, AddValuation.map_one] at hmul_lt
      simp at hmul_lt

@[simp]
theorem mem_valuationSubringValuationSubring (x : HahnField k Γ) :
    x ∈ valuationSubringValuationSubring k Γ ↔ x ∈ valuationSubring k Γ :=
  Iff.rfl

@[simp]
theorem valuationSubringValuationSubring_toSubring :
    (valuationSubringValuationSubring k Γ).toSubring = valuationSubring k Γ :=
  rfl

/-- The valuation subring associated by mathlib to the multiplicative natural valuation is the
same valuation subring constructed from the additive valuation.-/
theorem valuation_valuationSubring_eq :
    (valuation k Γ).valuationSubring = valuationSubringValuationSubring k Γ := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, mem_valuationSubringValuationSubring,
    mem_valuationSubring_iff]
  change Multiplicative.ofAdd (OrderDual.toDual (ofLex x).orderTop) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop Γ)) ↔
    0 ≤ (ofLex x).orderTop
  rw [Multiplicative.ofAdd_le]
  exact OrderDual.toDual_le_toDual

/-- Elements of the valuation subring have no terms of negative exponent.-/
theorem coeff_eq_zero_of_mem_valuationSubring_of_neg {x : HahnField k Γ}
    (hx : x ∈ valuationSubring k Γ) {γ : Γ} (hγ : γ < 0) :
    (ofLex x).coeff γ = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hγ) hx

/-- A nonzero coefficient of an element of the valuation subring can only occur in
nonnegative degree.-/
theorem nonneg_of_mem_valuationSubring_coeff_ne_zero {x : HahnField k Γ}
    (hx : x ∈ valuationSubring k Γ) {γ : Γ} (hγ : (ofLex x).coeff γ ≠ 0) :
    0 ≤ γ := by
  contrapose! hγ
  exact coeff_eq_zero_of_mem_valuationSubring_of_neg k Γ hx hγ

end HahnField

end

end HahnKaplanskyRealClosedness
