/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Divisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residues at places

The residue tower for the dimension bounds of the Riemann–Roch layer
(issue #13, P3): over an algebraically closed base every place has
residue field `k`, expressed element-wise without constructing the
quotient ring.

* `exists_sub_valuation_lt_one_of_mem_adjoin` — the reduce lemma:
  an integral element of `k(x)` (at a place where `x` is small) is
  congruent to a base constant modulo the maximal ideal;
* `linearIndependent_of_residue_independent` — elements of the valuation
  ring whose residues admit no nontrivial vanishing `k`-combination are
  linearly independent over `k(x)`.

The full reduction theorem (every integral element is congruent to a
unique constant) factors polynomials over the algebraically closed base
and lands in the next layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open Polynomial IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable {O : ValuationSubring F}

/-- **The reduce lemma**: an element of `k(x)` that is integral at a
place where `x` is small is congruent to a base constant modulo the
maximal ideal.
@isnad1 id=ex.5h5v.s9.a0f9472febb4 from=translated src=- shape=e8c56b67 vocab=1b608bc6
-/
theorem exists_sub_valuation_lt_one_of_mem_adjoin
    (hk : ∀ c : k, algebraMap k F c ∈ O) {x : F}
    (hxtr : Transcendental k x) (hx : O.valuation x < 1) {a : F}
    (ha : a ∈ adjoin k ({x} : Set F)) (hav : O.valuation a ≤ 1) :
    ∃ c : k, O.valuation (a - algebraMap k F c) < 1 := by
  classical
  have hx0 : x ≠ 0 := fun h ↦ hxtr (h ▸ isAlgebraic_zero)
  have hxv : O.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  rcases eq_or_ne a 0 with rfl | ha0
  · refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, Valuation.map_zero]
    exact zero_lt_one
  rw [IntermediateField.mem_adjoin_simple_iff] at ha
  obtain ⟨p, q, hpq⟩ := ha
  have hq0 : aeval x q ≠ 0 := by
    intro h0
    rw [hpq, h0, div_zero] at ha0
    exact ha0 rfl
  have hp0 : aeval x p ≠ 0 := by
    intro h0
    rw [hpq, h0, zero_div] at ha0
    exact ha0 rfl
  have hpne : p ≠ 0 := fun h ↦ hp0 (by rw [h, map_zero])
  have hqne : q ≠ 0 := fun h ↦ hq0 (by rw [h, map_zero])
  -- Split off the root multiplicities at zero.
  obtain ⟨p', hp', hp'nd⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpne 0
  obtain ⟨q', hq', hq'nd⟩ :=
    q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hqne 0
  rw [map_zero, sub_zero] at hp' hp'nd hq' hq'nd
  have hp'0 : p'.coeff 0 ≠ 0 := fun h ↦ hp'nd (Polynomial.X_dvd_iff.2 h)
  have hq'0 : q'.coeff 0 ≠ 0 := fun h ↦ hq'nd (Polynomial.X_dvd_iff.2 h)
  set mp := p.rootMultiplicity 0 with hmp
  set mq := q.rootMultiplicity 0 with hmq
  have hap'0 : aeval x p' ≠ 0 := by
    intro h0
    refine hp0 ?_
    rw [hp', map_mul, h0, mul_zero]
  have haq'0 : aeval x q' ≠ 0 := by
    intro h0
    refine hq0 ?_
    rw [hq', map_mul, h0, mul_zero]
  -- The valuation of `a` fixes the multiplicity comparison.
  have hvala : O.valuation a =
      O.valuation x ^ (mp : ℤ) / O.valuation x ^ (mq : ℤ) := by
    rw [hpq, map_div₀, valuation_aeval_eq_pow_rootMultiplicity hk hx hpne,
      valuation_aeval_eq_pow_rootMultiplicity hk hx hqne, ← hmp, ← hmq,
      zpow_natCast, zpow_natCast]
  have hmqle : mq ≤ mp := by
    by_contra hc
    push Not at hc
    have h1 : (1 : _) < O.valuation a := by
      rw [hvala, lt_div_iff₀ (zero_lt_iff.2 (zpow_ne_zero _ hxv)), one_mul]
      exact zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hxv) hx
        (by exact_mod_cast hc)
    exact h1.not_ge hav
  rcases Nat.lt_or_ge mq mp with hlt | hge
  · -- Strictly smaller: `a` itself is in the maximal ideal.
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hvala,
      div_lt_one₀ (zero_lt_iff.2 (zpow_ne_zero _ hxv))]
    exact zpow_lt_zpow_right_of_lt_one₀ (zero_lt_iff.2 hxv) hx
      (by exact_mod_cast hlt)
  · -- Equal multiplicities: reduce the constant terms.
    have hmpq : mp = mq := le_antisymm hge hmqle
    -- `a` is the ratio of the primed parts.
    have ha' : a = aeval x p' / aeval x q' := by
      rw [hpq, hp', hq', map_mul, map_mul, map_pow, map_pow, aeval_X,
        hmpq]
      rw [mul_div_mul_left _ _ (pow_ne_zero _ hx0)]
    refine ⟨p'.coeff 0 / q'.coeff 0, ?_⟩
    -- The difference is a polynomial with vanishing constant term over
    -- the unit denominator.
    set r : Polynomial k := p' * Polynomial.C (q'.coeff 0) -
      Polynomial.C (p'.coeff 0) * q' with hr
    have hr0 : r.coeff 0 = 0 := by
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_mul_C,
        Polynomial.coeff_C_mul, mul_comm]
      ring
    have hdiff : a - algebraMap k F (p'.coeff 0 / q'.coeff 0) =
        aeval x r / (aeval x q' * algebraMap k F (q'.coeff 0)) := by
      rw [ha', hr, map_sub, map_mul, map_mul, aeval_C, aeval_C,
        map_div₀ (algebraMap k F),
        div_sub_div _ _ haq'0 ((map_ne_zero (algebraMap k F)).2 hq'0)]
      congr 1
      ring
    rw [hdiff]
    rcases eq_or_ne r 0 with hrz | hrz
    · rw [hrz, map_zero, zero_div, Valuation.map_zero]
      exact zero_lt_one
    have hden : O.valuation (aeval x q' * algebraMap k F (q'.coeff 0)) =
        1 := by
      rw [Valuation.map_mul, valuation_aeval_eq_one hk hx hq'0,
        valuation_algebraMap_eq_one hk hq'0, mul_one]
    rw [map_div₀, hden, div_one,
      valuation_aeval_eq_pow_rootMultiplicity hk hx hrz]
    have hrmul : 0 < r.rootMultiplicity 0 := by
      rw [Polynomial.rootMultiplicity_pos hrz, Polynomial.IsRoot.def,
        ← Polynomial.coeff_zero_eq_eval_zero]
      exact hr0
    exact pow_lt_one₀ zero_le hx hrmul.ne'

set_option maxHeartbeats 800000 in
-- The normalized-coefficient bookkeeping over the adjoin-subtype makes
-- several `isDefEq` checks expensive.
/-- **The residue-independence lift**: elements of the valuation ring
whose residues admit no nontrivial vanishing `k`-combination are linearly
independent over `k(x)`. Normalize a vanishing combination by the
coefficient of minimal order, reduce the coefficients to constants, and
contradict.
@isnad1 id=linearin.5h6v.s9.445ad64ccc29 from=translated src=- shape=cdf9c376 vocab=146a3fa4
-/
theorem linearIndependent_of_residue_independent
    (hk : ∀ c : k, algebraMap k F c ∈ O) {x : F}
    (hxtr : Transcendental k x) (hx : O.valuation x < 1)
    {s : ℕ} {w : Fin s → F} (hwO : ∀ i, O.valuation (w i) ≤ 1)
    (hres : ∀ c : Fin s → k, (∃ i, c i ≠ 0) →
      O.valuation (∑ i, algebraMap k F (c i) * w i) = 1) :
    LinearIndependent (↥(adjoin k ({x} : Set F))) w := by
  classical
  have hx0 : x ≠ 0 := fun h ↦ hxtr (h ▸ isAlgebraic_zero)
  have hxv : O.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
  have hxvpos : (0 : _) < O.valuation x := zero_lt_iff.2 hxv
  rw [Fintype.linearIndependent_iff]
  intro g hsum i₀'
  by_contra hg₀
  set s' : Finset (Fin s) := Finset.univ.filter (fun i ↦ g i ≠ 0)
    with hs'def
  have hi₀s' : i₀' ∈ s' := by simp [hs'def, hg₀]
  have hcoe0 : ∀ i ∈ s', ((g i : F)) ≠ 0 := by
    intro i hi
    rw [hs'def, Finset.mem_filter] at hi
    simpa using hi.2
  -- Orders of the coefficients and the minimal one.
  have hords : ∀ i ∈ s', ∃ m : ℤ,
      O.valuation ((g i : F)) = O.valuation x ^ m := fun i hi ↦
    exists_valuation_eq_zpow_of_mem_adjoin hk hx0 hx
      (SetLike.coe_mem (g i)) (hcoe0 i hi)
  choose! m hm using hords
  obtain ⟨i₀, hi₀, hi₀min⟩ := s'.exists_min_image m ⟨i₀', hi₀s'⟩
  -- Normalized coefficients: integral, with a unit at the minimum.
  set b : Fin s → F := fun i ↦ (g i : F) * (x ^ m i₀)⁻¹ with hbdef
  have hxm0 : (x ^ m i₀ : F) ≠ 0 := zpow_ne_zero _ hx0
  have hbval : ∀ i ∈ s', O.valuation (b i) =
      O.valuation x ^ (m i - m i₀) := by
    intro i hi
    have hbi : b i = (g i : F) * (x ^ m i₀)⁻¹ := rfl
    rw [hbi, Valuation.map_mul, map_inv₀, hm i hi, map_zpow₀,
      zpow_sub₀ hxv, div_eq_mul_inv]
  have hble : ∀ i ∈ s', O.valuation (b i) ≤ 1 := by
    intro i hi
    rw [hbval i hi]
    calc O.valuation x ^ (m i - m i₀)
        ≤ O.valuation x ^ (0 : ℤ) :=
          zpow_le_zpow_right_of_le_one₀ hxvpos hx.le (by
            have := hi₀min i hi
            omega)
      _ = 1 := zpow_zero _
  have hb₀ : O.valuation (b i₀) = 1 := by
    rw [hbval i₀ hi₀, sub_self, zpow_zero]
  have hbmem : ∀ i, b i ∈ adjoin k ({x} : Set F) := by
    intro i
    have hx_mem : x ∈ adjoin k ({x} : Set F) := subset_adjoin k _ rfl
    have hzp : (x ^ m i₀ : F) ∈ adjoin k ({x} : Set F) :=
      zpow_mem hx_mem _
    have hzpi : ((x ^ m i₀ : F))⁻¹ ∈ adjoin k ({x} : Set F) := inv_mem hzp
    exact mul_mem (SetLike.coe_mem (g i)) hzpi
  -- Reduce the normalized coefficients to constants.
  have hred : ∀ i ∈ s', ∃ c : k,
      O.valuation (b i - algebraMap k F c) < 1 := fun i hi ↦
    exists_sub_valuation_lt_one_of_mem_adjoin hk hxtr hx (hbmem i)
      (hble i hi)
  choose! c hc using hred
  set c' : Fin s → k := fun i ↦ if i ∈ s' then c i else 0 with hc'def
  have hc'₀ : c' i₀ ≠ 0 := by
    have hci : c' i₀ = c i₀ := ite_eq_left hi₀
    rw [hci]
    intro h0
    have h1 := hc i₀ hi₀
    rw [h0, map_zero, sub_zero, hb₀] at h1
    exact h1.ne rfl
  -- The constant combination coincides with the reduction error.
  have hkey : ∑ i, algebraMap k F (c' i) * w i =
      ∑ i ∈ s', (algebraMap k F (c i) - b i) * w i := by
    have h1 : ∑ i, algebraMap k F (c' i) * w i =
        ∑ i ∈ s', algebraMap k F (c i) * w i := by
      refine (Finset.sum_subset (Finset.subset_univ s') fun i _ hi ↦ ?_).symm.trans ?_
      · have hci : c' i = 0 := ite_eq_right hi
        rw [hci, map_zero, zero_mul]
      · refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hci : c' i = c i := ite_eq_left hi
        rw [hci]
    have h2 : ∑ i ∈ s', b i * w i = 0 := by
      have h3 : ∀ i ∈ s', b i * w i =
          (x ^ m i₀)⁻¹ * ((g i : F) * w i) := by
        intro i _
        have hbi : b i = (g i : F) * (x ^ m i₀)⁻¹ := rfl
        rw [hbi]
        ring
      rw [Finset.sum_congr rfl h3, ← Finset.mul_sum]
      have h4 : ∑ i ∈ s', (g i : F) * w i = 0 := by
        rw [← hsum]
        rw [show ∑ i, g i • w i = ∑ i, (g i : F) * w i from
          Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def]; rfl]
        refine Finset.sum_subset (Finset.subset_univ s') fun i _ hi ↦ ?_
        rw [hs'def, Finset.mem_filter, not_and, not_not] at hi
        rw [hi (Finset.mem_univ i), ZeroMemClass.coe_zero, zero_mul]
      rw [h4, mul_zero]
    calc ∑ i, algebraMap k F (c' i) * w i
        = ∑ i ∈ s', algebraMap k F (c i) * w i := h1
      _ = ∑ i ∈ s', ((algebraMap k F (c i) - b i) * w i + b i * w i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
      _ = ∑ i ∈ s', (algebraMap k F (c i) - b i) * w i +
          ∑ i ∈ s', b i * w i := Finset.sum_add_distrib
      _ = ∑ i ∈ s', (algebraMap k F (c i) - b i) * w i := by
          rw [h2, add_zero]
  -- The reduction error is small; the residue hypothesis says unit.
  have hsmall : O.valuation (∑ i ∈ s',
      (algebraMap k F (c i) - b i) * w i) < 1 := by
    refine O.valuation.map_sum_lt one_ne_zero fun i hi ↦ ?_
    rw [Valuation.map_mul]
    have h5 : O.valuation (algebraMap k F (c i) - b i) < 1 := by
      rw [Valuation.map_sub_swap]
      exact hc i hi
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hwO i)) h5
  have hunit := hres c' ⟨i₀, hc'₀⟩
  rw [hkey] at hunit
  exact hsmall.ne hunit

section ResidueField

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **Residue fields are the base field** (Stichtenoth 1.1.15 over an
algebraically closed base): every element integral at a place is
congruent to a base constant modulo the maximal ideal. If not, the
powers of the element would have independent residues — a minimal
vanishing combination factors over the algebraically closed base, and a
small-valued linear factor yields a reduction — contradicting the
degree bound.
@isnad1 id=ex.1h4v.s9.e5ff392dfdfb from=translated src=- shape=581b9b8c vocab=787f6c62
-/
theorem Place.exists_residue (P : Place k F) {u : F}
    (hu : P.val.valuation u ≤ 1) :
    ∃ c : k, P.val.valuation (u - algebraMap k F c) < 1 := by
  classical
  by_contra hno
  push Not at hno
  -- Every difference with a constant is then exactly a unit.
  have hsub1 : ∀ c : k, P.val.valuation (u - algebraMap k F c) = 1 := by
    intro c
    have hle : P.val.valuation (u - algebraMap k F c) ≤ 1 := by
      refine le_trans (Valuation.map_sub _ _ _) ?_
      rw [max_le_iff]
      exact ⟨hu, (P.val.valuation_le_one_iff _).2 (P.algebraMap_mem c)⟩
    exact le_antisymm hle (hno c)
  -- The transcendence data for the independence bound.
  obtain ⟨x, hx0, hx⟩ := exists_valuation_lt_one_of_ne_top P.ne_top
  have hxtr := transcendental_of_valuation_lt_one P.algebraMap_mem
    (fun y hy ↦ exists_algebraMap_eq_of_isAlgebraic hy) hx0 hx
  haveI := finiteDimensional_adjoin_of_transcendental (k := k) hxtr
  set n := Module.finrank (↥(adjoin k ({x} : Set F))) F with hn
  -- The residues of the powers of `u` are independent.
  have hres : ∀ c : Fin (n + 1) → k, (∃ i, c i ≠ 0) →
      P.val.valuation (∑ i, algebraMap k F (c i) * u ^ (i : ℕ)) = 1 := by
    intro c hc
    set p : Polynomial k := ∑ i : Fin (n + 1), Polynomial.C (c i) *
      Polynomial.X ^ (i : ℕ) with hpdef
    obtain ⟨i₀, hi₀⟩ := hc
    have hp0 : p ≠ 0 := by
      intro h0
      refine hi₀ ?_
      have h1 := congrArg (fun q ↦ Polynomial.coeff q (i₀ : ℕ)) h0
      simp only [hpdef, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1
      rw [Finset.sum_eq_single i₀] at h1
      · simpa using h1
      · intro j _ hji
        exact ite_eq_right fun h ↦ hji (Fin.val_injective h).symm
      · intro h
        exact absurd (Finset.mem_univ i₀) h
    have hsum : ∑ i, algebraMap k F (c i) * u ^ (i : ℕ) =
        Polynomial.aeval u p := by
      rw [hpdef, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    rw [hsum]
    -- Normalize monic and factor over the algebraically closed base.
    have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hp0
    set q : Polynomial k := p * Polynomial.C p.leadingCoeff⁻¹ with hqdef
    have hqmonic : q.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
    have hqsplit : q.Splits := IsAlgClosed.splits q
    have hfac : q = (q.roots.map fun a ↦ Polynomial.X -
        Polynomial.C a).prod := hqsplit.eq_prod_roots_of_monic hqmonic
    -- Each root gives a unit difference; the product is a unit.
    have haq : Polynomial.aeval u q =
        (q.roots.map fun a ↦ u - algebraMap k F a).prod := by
      conv_lhs => rw [hfac]
      rw [show (Polynomial.aeval u : Polynomial k →ₐ[k] F) _ =
        ((Polynomial.aeval u : Polynomial k →ₐ[k] F) :
          Polynomial k →* F) _ from rfl, map_multiset_prod,
        Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ ↦ ?_)
      simp [Polynomial.aeval_C]
    have hvq : P.val.valuation (Polynomial.aeval u q) = 1 := by
      rw [haq, map_multiset_prod]
      refine Multiset.prod_eq_one ?_
      intro γ hγ
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hγ
      obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hb
      exact hsub1 a
    have hpq : p = q * Polynomial.C p.leadingCoeff := by
      rw [hqdef, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc,
        Polynomial.C_1, mul_one]
    rw [hpq, map_mul, Polynomial.aeval_C, Valuation.map_mul, hvq, one_mul]
    exact valuation_algebraMap_eq_one P.algebraMap_mem hlc
  -- Independence of the powers contradicts the finrank bound.
  have hwO : ∀ i : Fin (n + 1), P.val.valuation (u ^ (i : ℕ)) ≤ 1 := by
    intro i
    rw [Valuation.map_pow]
    exact pow_le_one₀ zero_le hu
  have hind := linearIndependent_of_residue_independent P.algebraMap_mem
    hxtr hx hwO hres
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end ResidueField

end

end AclGeom
