/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import Tengoku.Seed.Algebra.CharP.Invertible
public import Tengoku.Seed.Algebra.Order.Ring.Star
public import Tengoku.Seed.Analysis.Normed.Field.Lemmas
public import Tengoku.Seed.Analysis.Real.OfDigits
public import Tengoku.Seed.Data.Finsupp.Multiset
public import Tengoku.Seed.Data.Fintype.Fin
public import Tengoku.Seed.Data.Nat.Digits.Lemmas
public import Tengoku.Seed.Data.Rat.Star
public import Tengoku.Seed.SetTheory.Cardinal.Finite
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sparseness and `(c, n)`-sparseness

This file formalizes Section 3 of the paper. It introduces the combinatorial model of base-`p`
digit expansions used to phrase the sparseness condition on supports of `p`-adic Hahn series, and
proves that sets with pairwise-disjoint digit supports are sparse.

## Main definitions

- `FormalizedSparse.Sparse.DigitSeries`: the direct sum `⨁_{ℕ₊} ℕ`, modeling base-`p` digit
  expansions.
- `FormalizedSparse.Sparse.IsCSparse`: the `(c, n)`-sparseness condition (Definition 3.5).
- `FormalizedSparse.IsSparse`: sparseness for subsets of `[0, 1) ∩ ℚ` (Definition 1.4).

## Main statements

- `FormalizedSparse.IsSparse_of_digit_disjoint`: sets built from pairwise-disjoint digit supports
  are sparse (Example 3.7).

## Tags

sparse, digit expansion, p-adic, Hahn series
-/

@[expose] public section

namespace FormalizedSparse

namespace Sparse

/-- A **digit series**: the direct sum `⨁_{ℕ₊} ℕ`, i.e. a function `ℕ+ → ℕ` with finite support.
It models the base-`p` digit expansion `∑ᵢ (f i) · p^{-i}` of a rational in `[0, 1)`.-/
@[ext]
structure DigitSeries where
  /-- The underlying digit function, sending a position `i : ℕ+` to its digit value.-/
  toFun : ℕ+ → ℕ
  /-- The digit function has finite support.-/
  fin_supp : toFun.support.Finite

instance : FunLike (DigitSeries) ℕ+ ℕ where
  coe := DigitSeries.toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ hfg
    simp only at hfg
    congr

/--
@isnad1 id=eq.1h1v.s4.5020a8b319ca from=translated src=- shape=55f66744 vocab=33fdd67d
-/
@[simp] theorem DigitSeries.coe_mk (f : ℕ+ → ℕ) (h) :
    ⇑(⟨f, h⟩ : DigitSeries) = f := rfl

/--
@isnad1 id=eq.0h1v.s4.337076d7e349 from=translated src=- shape=6dbcd907 vocab=ecac59e9
-/
@[simp] theorem DigitSeries.toFun_eq_coe (f : DigitSeries) : f.toFun = ⇑f := rfl

namespace DigitSeries

/-- The largest position at which a digit series is nonzero (`0` if the series vanishes).-/
noncomputable def maxIndex (f : DigitSeries) : ℕ :=
  f.fin_supp.toFinset.sup fun i => (i : ℕ)

/-- The list of the first `n` digit values `[f 1, f 2, …, f n]` of a raw digit function, in
reverse order (least significant last), suitable for `Nat.ofDigits`.-/
def coeffs (f : ℕ+ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => f (Nat.succPNat n) :: coeffs f n

/-- The base-`p` value of the first `n` digits of `f`, i.e. `Nat.ofDigits p (coeffs f n)`.-/
noncomputable def value (p : ℕ) (f : DigitSeries) (n : ℕ) : ℕ :=
  Nat.ofDigits p (coeffs f n)

/-- The first `n` positive-integer positions `{1, 2, …, n}` as a `Finset ℕ+`.-/
def indices (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩

/--
@isnad1 id=eq.0h2v.s3.9bd4c5120713 from=translated src=- shape=5322d808 vocab=6425de38
-/
@[simp] lemma coeffs_length (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

/--
@isnad1 id=eq.0h2v.s4.8fb4f6384eb3 from=translated src=- shape=2dade4aa vocab=b4b3466c
-/
@[simp] lemma coeffs_sum (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).sum = Finset.sum (indices n) f := by
  induction n with
  | zero => simp [coeffs, indices]
  | succ n ih =>
      rw [coeffs, List.sum_cons]
      rw [show indices (n + 1) = insert (Nat.succPNat n) (indices n) by
        ext i
        simp [indices, Finset.range_add_one, eq_comm]]
      rw [Finset.sum_insert]
      · simp [ih]
      · simp [indices]

/--
@isnad1 id=iff.0h2v.s4.7d10d3e57152 from=translated src=- shape=740b59f7 vocab=028766d5
-/
@[simp] lemma mem_indices (n k : ℕ) :
    Nat.succPNat k ∈ indices n ↔ k < n := by
  simp [indices]

/--
@isnad1 id=eq.0h1v.s4.26643cbcae0e from=translated src=- shape=fe098d52 vocab=70e1786d
-/
@[simp] lemma indices_succ (n : ℕ) :
    indices (n + 1) = insert (Nat.succPNat n) (indices n) := by
  ext i
  simp [indices, Finset.range_add_one, eq_comm]

/--
@isnad1 id=le.1h2v.s4.a04928b1949a from=translated src=- shape=ef3a04ae vocab=b8503a7d
-/
lemma le_maxIndex_of_mem_support (f : DigitSeries) {n : ℕ+} (hn : f n ≠ 0) :
    (n : ℕ) ≤ f.maxIndex := by
  classical
  refine Finset.le_sup ?_
  simpa using hn

lemma eq_zero_of_maxIndex_lt (f : DigitSeries) {n : ℕ} (hn : f.maxIndex < n + 1) :
    f (Nat.succPNat n) = 0 := by
  by_contra hne
  exact (not_lt_of_ge (f.le_maxIndex_of_mem_support hne)) hn

/--
@isnad1 id=eq.0h2v.s6.8f4eaa42f214 from=translated src=- shape=af3442fe vocab=cde2e8cd
-/
lemma cast_mul_zpow_neg_succ (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    (p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)) = (p : ℚ) ^ (-(n : ℤ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  rw [zpow_neg, zpow_neg]
  norm_num
  field_simp [hp0]
  have hpow : (p : ℚ) ^ (↑n + 1) = (p : ℚ) * (p : ℚ) ^ n := by simpa using (pow_succ' (p : ℚ) n)
  exact hpow.symm

/--
@isnad1 id=eq.0h2v.s5.7ffb4f625e68 from=translated src=- shape=2a1539b6 vocab=e4229140
-/
lemma cast_pow_mul_zpow_neg (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    ((p : ℚ) ^ n) * (p : ℚ) ^ (-(n : ℤ)) = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  rw [zpow_neg, zpow_natCast]
  field_simp [hp0]

/--
@isnad1 id=eq.1h4v.s5.c0ce596dd1b5 from=translated src=- shape=7f7a15d7 vocab=3bec598d
-/
lemma coeffs_update_above (f : ℕ+ → ℕ) (n m : ℕ) (hm : m ≤ n) (a : ℕ) :
    coeffs (Function.update f (Nat.succPNat n) a) m = coeffs f m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm' : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
      have hne : Nat.succPNat m ≠ Nat.succPNat n := by
        exact fun h => (Nat.lt_of_succ_le hm).ne (Nat.succPNat_injective h)
      simp [coeffs, Function.update, hne, ih hm']

/-- Build a digit series from a list of digit values `[a₁, a₂, …, aₙ]`, placing `aᵢ` at
position `i`. This is a left inverse to `coeffs` on lists of the right length.-/
noncomputable def ofCoeffs : List ℕ → DigitSeries
  | [] =>
      { toFun := 0
        fin_supp := by simp }
  | a :: L =>
      let f := ofCoeffs L
      { toFun := Function.update f (Nat.succPNat L.length) a
        fin_supp := by
          classical
          refine Set.Finite.subset (f.fin_supp.insert (Nat.succPNat L.length)) ?_
          intro i hi
          by_cases h : i = Nat.succPNat L.length
          · simp [h]
          · right; simpa [Function.update, h] using hi }

/--
@isnad1 id=eq.0h1v.s4.1ae005e27655 from=translated src=- shape=2b9d2956 vocab=c022f288
-/
@[simp] lemma coeffs_ofCoeffs : ∀ L : List ℕ, coeffs (ofCoeffs L) L.length = L
  | [] => rfl
  | a :: L => by
      simp only [ofCoeffs, coeffs, List.length_cons]
      rw [List.cons.injEq]
      constructor
      · change Function.update (ofCoeffs L) (Nat.succPNat L.length) a (Nat.succPNat L.length) = a
        simp
      · change coeffs (Function.update (ofCoeffs L) (Nat.succPNat L.length) a) L.length = L
        rw [coeffs_update_above (f := ofCoeffs L) (n := L.length) (m := L.length) le_rfl (a := a)]
        rw [coeffs_ofCoeffs L]

/--
@isnad1 id=lt.1h3v.s5.428e4246fa3e from=translated src=- shape=3b99442d vocab=dfc1d113
-/
lemma ofCoeffs_lt {p : ℕ} [Fact (Nat.Prime p)] :
    ∀ {L : List ℕ}, (∀ x ∈ L, x < p) → ∀ i, ofCoeffs L i < p
  | [], h, i => by
      simpa [ofCoeffs] using (Fact.out : Nat.Prime p).pos
  | a :: L, h, i => by
      by_cases hi : i = Nat.succPNat L.length
      · subst hi
        change Function.update (ofCoeffs L) (Nat.succPNat L.length) a (Nat.succPNat L.length) < p
        simpa using h a List.mem_cons_self
      · change Function.update (ofCoeffs L) (Nat.succPNat L.length) a i < p
        simpa [Function.update, hi] using
          ofCoeffs_lt (p := p) (L := L) (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

/--
@isnad1 id=le.1h2v.s4.815e8172da4e from=translated src=- shape=27fb0261 vocab=24392ae1
-/
lemma le_length_of_mem_support_ofCoeffs : ∀ {L : List ℕ} {i : ℕ+},
    ofCoeffs L i ≠ 0 → (i : ℕ) ≤ L.length
  | [], i, hi => by cases hi rfl
  | a :: L, i, hi => by
      by_cases htop : i = Nat.succPNat L.length
      · subst htop
        simp
      · have hi' : ofCoeffs L i ≠ 0 := by
          change Function.update (ofCoeffs L) (Nat.succPNat L.length) a i ≠ 0 at hi
          simpa [Function.update, htop] using hi
        exact Nat.le_trans (le_length_of_mem_support_ofCoeffs hi') (Nat.le_succ _)

/--
@isnad1 id=lt.0h1v.s4.18595335ae54 from=translated src=- shape=adb4f9d9 vocab=1d1e5035
-/
lemma maxIndex_ofCoeffs_lt (L : List ℕ) : (ofCoeffs L).maxIndex < L.length + 1 := by
  classical
  have hle : (ofCoeffs L).maxIndex ≤ L.length := by
    refine Finset.sup_le ?_
    intro i hi
    exact le_length_of_mem_support_ofCoeffs (by simpa using hi)
  exact Nat.lt_succ_of_le hle

/--
@isnad1 id=lt.0h1v.s4.b6d204593324 from=translated src=- shape=1173d5cd vocab=19540e01
-/
lemma maxIndex_ofCoeffs_zero_cons_lt (L : List ℕ) :
    (ofCoeffs (0 :: L)).maxIndex < L.length + 1 := by
  classical
  have hle : (ofCoeffs (0 :: L)).maxIndex ≤ L.length := by
    refine Finset.sup_le ?_
    intro i hi
    have hne : ofCoeffs (0 :: L) i ≠ 0 := by
      simpa using hi
    by_cases htop : i = Nat.succPNat L.length
    · subst htop
      exfalso
      change
        Function.update (ofCoeffs L) (Nat.succPNat L.length) 0 (Nat.succPNat L.length) ≠ 0 at hne
      exact hne (by simp)
    · have hi' : ofCoeffs L i ≠ 0 := by
        change Function.update (ofCoeffs L) (Nat.succPNat L.length) 0 i ≠ 0 at hne
        simpa [Function.update, htop] using hne
      exact le_length_of_mem_support_ofCoeffs hi'
  exact Nat.lt_succ_of_le hle

lemma eq_on_of_coeffs_eq : ∀ {f g : ℕ+ → ℕ} {n : ℕ}, coeffs f n = coeffs g n →
    ∀ i : ℕ+, (i : ℕ) ≤ n → f i = g i
  | f, g, 0, h, i, hi => by
      exfalso
      exact (Nat.not_lt_of_ge hi) i.2
  | f, g, n + 1, h, i, hi => by
      have h' : f (Nat.succPNat n) = g (Nat.succPNat n) ∧ coeffs f n = coeffs g n := by
        simpa [coeffs] using h
      rcases Nat.lt_or_eq_of_le hi with hi_lt | hi_eq
      · exact eq_on_of_coeffs_eq h'.2 i (Nat.le_of_lt_succ hi_lt)
      · have : i = Nat.succPNat n := Subtype.ext hi_eq
        simpa [this] using h'.1

end DigitSeries

namespace DigitSeries
/-- The predicate `ℙ` (Definition 3.1 (2)): a digit series is a **proper** base-`p` expansion,
i.e. every digit is `< p`.-/
def IsP (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ n, f n < p

end DigitSeries

/--
@isnad1 id=eq.0h2v.s5.ae76c091eb07 from=translated src=- shape=8986ab43 vocab=6c716162
-/
lemma ofDigits_carry_last_eq (p x : ℕ) :
    Nat.ofDigits p [x] = Nat.ofDigits p [x % p, x / p] := by
  simp [Nat.ofDigits_cons, Nat.mod_add_div]

/--
@isnad1 id=eq.0h4v.s5.a9f39e280cbe from=translated src=- shape=16cfee0b vocab=b4d8085a
-/
lemma ofDigits_carry_eq (p x y : ℕ) (L : List ℕ) :
    Nat.ofDigits p (x :: y :: L) = Nat.ofDigits p (x % p :: (x / p + y) :: L) := by
  calc
    Nat.ofDigits p (x :: y :: L) = x + p * y + p * (p * Nat.ofDigits p L) := by
      simp [Nat.ofDigits_cons, Nat.mul_add, Nat.add_assoc]
    _ = x % p + p * (x / p) + p * y + p * (p * Nat.ofDigits p L) := by
      rw [Nat.mod_add_div]
    _ = Nat.ofDigits p (x % p :: (x / p + y) :: L) := by
      simp [Nat.ofDigits_cons, Nat.mul_add, Nat.add_assoc]

/--
@isnad1 id=eq.1h2v.s5.298ad7f35ea2 from=translated src=- shape=9515e876 vocab=5284c00e
-/
lemma ofDigits_eq_zero_of_sum_eq_zero (p : ℕ) {L : List ℕ} (hsum : L.sum = 0) :
    Nat.ofDigits p L = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      have hsum' : x + xs.sum = 0 := by simpa [List.sum_cons] using hsum
      have hx : x = 0 := Nat.eq_zero_of_add_eq_zero_right hsum'
      have hxs : xs.sum = 0 := Nat.eq_zero_of_add_eq_zero_left hsum'
      simp [Nat.ofDigits_cons, hx, ih hxs]

/--
@isnad1 id=ex.2h2v.s6.90bef6c8cc49 from=translated src=- shape=05e03c08 vocab=aece0135
-/
lemma exists_small_sum_ofDigits_eq_of_exists_ge (p : ℕ) (hp : 1 < p) :
    ∀ {L : List ℕ}, (∃ x ∈ L, p ≤ x) →
      ∃ E : List ℕ, Nat.ofDigits p E = Nat.ofDigits p L ∧ E.sum < L.sum
  | [] => by
      intro hbad
      rcases hbad with ⟨x, hx, _⟩
      cases hx
  | x :: [] => by
      intro hbad
      rcases hbad with ⟨w, hw, hwge⟩
      have hwx : w = x := by simpa using hw
      subst w
      have hx0 : 0 < x / p := Nat.div_pos hwge (Nat.zero_lt_of_lt hp)
      have hdecrease : x % p + x / p < x := by
        have hmul : x / p < p * (x / p) := by
          simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hp hx0
        calc
          x % p + (x / p) < x % p + p * (x / p) := by exact Nat.add_lt_add_left hmul _
          _ = x := by simpa [Nat.add_comm] using (Nat.mod_add_div x p)
      refine ⟨[x % p, x / p], (ofDigits_carry_last_eq p x).symm, ?_⟩
      simp only [List.sum_cons, List.sum_nil]
      exact hdecrease
  | x :: y :: L => by
      intro hbad
      by_cases hx : p ≤ x
      · have hx0 : 0 < x / p := Nat.div_pos hx (Nat.zero_lt_of_lt hp)
        have hdecrease : x % p + x / p < x := by
          have hmul : x / p < p * (x / p) := by
            simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hp hx0
          calc
            x % p + (x / p) < x % p + p * (x / p) := by exact Nat.add_lt_add_left hmul _
            _ = x := by simpa [Nat.add_comm] using (Nat.mod_add_div x p)
        refine ⟨x % p :: (x / p + y) :: L, (ofDigits_carry_eq p x y L).symm, ?_⟩
        simpa [List.sum_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_lt_add_right hdecrease (y + L.sum)
      · have hybad : ∃ z ∈ y :: L, p ≤ z := by
          rcases hbad with ⟨z, hz, hzp⟩
          have hz' : z = x ∨ z ∈ y :: L := by simpa [List.mem_cons] using hz
          rcases hz' with rfl | hzL
          · exact (hx hzp).elim
          · exact ⟨z, hzL, hzp⟩
        rcases exists_small_sum_ofDigits_eq_of_exists_ge (p := p) hp hybad with ⟨E, hEeq, hEsum⟩
        refine ⟨x :: E, ?_, ?_⟩
        · simp [Nat.ofDigits_cons, hEeq]
        · simpa [List.sum_cons] using Nat.add_lt_add_left hEsum x

/--
@isnad1 id=le.1h2v.s5.fab0f6d6220e from=translated src=- shape=da3f5cdc vocab=e1e108ec
-/
lemma digit_sum_ofDigits_le_sum (p : ℕ) (hp : 1 < p) :
    ∀ L : List ℕ, (Nat.digits p (Nat.ofDigits p L)).sum ≤ L.sum := by
  intro L
  suffices hmain :
      ∀ n : ℕ, ∀ K : List ℕ, K.sum ≤ n → (Nat.digits p (Nat.ofDigits p K)).sum ≤ K.sum by
    exact hmain L.sum L le_rfl
  intro n
  induction n with
  | zero =>
      intro K hK
      have hsum0 : K.sum = 0 := Nat.eq_zero_of_le_zero hK
      have hof0 : Nat.ofDigits p K = 0 := ofDigits_eq_zero_of_sum_eq_zero p hsum0
      simp [hof0]
  | succ n ih =>
      intro K hK
      by_cases hbad : ∃ x ∈ K, p ≤ x
      · rcases exists_small_sum_ofDigits_eq_of_exists_ge p hp hbad with ⟨E, hEeq, hEsum⟩
        have hEn : E.sum ≤ n := Nat.lt_succ_iff.mp (lt_of_lt_of_le hEsum hK)
        have hEle : (Nat.digits p (Nat.ofDigits p E)).sum ≤ E.sum := ih E hEn
        rw [hEeq] at hEle
        exact le_trans hEle (Nat.le_of_lt hEsum)
      · have hlt : ∀ x ∈ K, x < p := by
          intro x hx
          exact lt_of_not_ge fun hxp => hbad ⟨x, hx, hxp⟩
        have hdigits : (Nat.digits p (Nat.ofDigits p K)).sum = K.sum := by
          simpa using Nat.sum_digits_ofDigits_eq_sum hp ⟨rfl, hlt⟩
        exact hdigits.le

/--
@isnad1 id=lt.2h2v.s5.28e8ff2e807f from=translated src=- shape=99d6bfe7 vocab=30fb9217
-/
lemma digit_sum_ofDigits_lt_sum_of_exists_ge (p : ℕ) (hp : 1 < p) {L : List ℕ}
    (hbad : ∃ x ∈ L, p ≤ x) :
    (Nat.digits p (Nat.ofDigits p L)).sum < L.sum := by
  rcases exists_small_sum_ofDigits_eq_of_exists_ge p hp hbad with ⟨E, hEeq, hEsum⟩
  have hEle : (Nat.digits p (Nat.ofDigits p E)).sum ≤ E.sum := digit_sum_ofDigits_le_sum p hp E
  rw [hEeq] at hEle
  exact lt_of_le_of_lt hEle hEsum

/--
@isnad1 id=lt.3h3v.s5.4e80d08a6dbf from=translated src=- shape=27e55237 vocab=f8bf6c86
-/
lemma forall_lt_of_digit_sum_ofDigits_eq_sum (p : ℕ) (hp : 1 < p) {L : List ℕ}
    (hEq : (Nat.digits p (Nat.ofDigits p L)).sum = L.sum) :
    ∀ x ∈ L, x < p := by
  intro x hx
  by_contra hxp
  have hbad : ∃ y ∈ L, p ≤ y := ⟨x, hx, Nat.not_lt.mp hxp⟩
  have hlt := digit_sum_ofDigits_lt_sum_of_exists_ge p hp hbad
  rw [hEq] at hlt
  exact Nat.lt_irrefl _ hlt

namespace DigitSeries

/-- The first `n` digit values of a proper (`IsP p`) digit series are all `< p`.
@isnad1 id=lt.2h4v.s5.f85be89e3dbb from=translated src=- shape=ae8b4377 vocab=7eb56790
-/
lemma coeffs_lt {p : ℕ} [Fact (Nat.Prime p)] (f : DigitSeries) (hf : f.IsP p) (n : ℕ) :
    ∀ x ∈ DigitSeries.coeffs f n, x < p := by
  intro x hx
  induction n generalizing x with
  | zero => cases hx
  | succ n ih =>
      simp only [DigitSeries.coeffs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using hf (Nat.succPNat n)
      · exact ih _ hx

end DigitSeries

variable (p : ℕ) [Fact (Nat.Prime p)]

namespace DigitSeries
-- `τ` in `Lemma 3.2`

end DigitSeries

/-- The `p`-adic **digits** of a rational `q` (Definition 1.3): `decDigits p q n` is the `n`-th
base-`p` digit of the fractional part of `q`.-/
noncomputable abbrev decDigits (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) : ℕ+ → Fin p :=
  fun n => Real.digits (Int.fract q) p ((n : ℕ) - 1)

open Classical in
/-- The **`p`-digit sum** `𝔑ₚ(q)` of a rational `q` (Definition 1.3 (1)): the sum of its base-`p`
digits, or `⊤` if the expansion has infinite support.-/
noncomputable def pDigitSum (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) : WithTop ℕ :=
  if h : (Function.support (decDigits p q)).Infinite then ⊤
  else ∑ n ∈ (Set.not_infinite.1 h).toFinset, (decDigits p q n).val

/-- The **dominant `p`-digit sum** of a set `S` (Definition 1.3 (2)): the supremum of the `p`-digit
sums of its elements.-/
noncomputable def dom (p : ℕ) [Fact (Nat.Prime p)] (S : Set ℚ) : WithTop ℕ :=
  sSup {pDigitSum p  q | q ∈ S}

/-- The **`p`-digit dominant part** of a set `S` (Definition 1.3 (2)): the elements of `S` whose
`p`-digit sum attains the dominant value `dom p S`.-/
noncomputable def Dom (p : ℕ) [Fact (Nat.Prime p)] (S : Set ℚ) : Set ℚ :=
  {q ∈ S | pDigitSum p q = dom p S}

/-- The **sparseness** condition (Definition 1.4) for a set `S ⊆ [0, 1) ∩ ℚ`: its dominant part is
finite, and for infinitely many `n` there are `n` elements of `Dom p S` that add without carry and
whose carry-free sum is rigid up to permutation.-/
def IsSparse (p : ℕ) [Fact (Nat.Prime p)] (S : Set ℚ) : Prop :=
  S ⊆ Set.Ico 0 1 ∧ dom p S < ⊤ ∧
  ∃ D : Set ℕ+, D.Infinite ∧ (
    ∀ n ∈ D, ∃ d : Fin n → Dom p S,
    (
      ∀ i : ℕ+, ∑ (j : Fin n), (decDigits p (d j) i).val < p
      -- No carrying when adding d₁, d₂, ..., dₙ together.
    )
    ∧
    (
      ∀ e : Fin n → Dom p S,
      (∑ i, (d i).val -∑ i, (e i).val).isInt →
        ∃ perm : Equiv.Perm (Fin n), ∀ i, d i = e (perm i)
    )
  )

/-! ## Helper lemmas bridging `decDigits`/`pDigitSum` and `DigitSeries`

The two main lemmas below (`IsSparse_iff_IsCNSparse` and `IsSparse_of_digit_disjoint`)
require translating between the real-valued digit machinery
(`decDigits p q`, defined via `Real.digits (Int.fract q) p`) and the
combinatorial `DigitSeries` framework. The helpers below capture the key
bridges. The deep technical bridges (linking `Real.ofDigits` tsums with finite
DigitSeries sums) are left as sub-sorries with clear statements; once those are
discharged, the main theorems follow structurally. -/

/-- A digit `(decDigits p q n)` is `< p` by `Fin p` typing.
@isnad1 id=lt.0h3v.s4.2614c62d8692 from=translated src=- shape=2ff5cac2 vocab=866d8fe1
-/
@[simp] lemma decDigits_val_lt (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) (n : ℕ+) :
    (decDigits p q n).val < p := (decDigits p q n).isLt

/-- `pDigitSum p q ≠ ⊤` iff `decDigits p q` has finite support.
@isnad1 id=iff.0h2v.s5.7586c8744702 from=translated src=- shape=4cbfec16 vocab=51ce6e0d
-/
lemma pDigitSum_ne_top_iff (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ) :
    pDigitSum p q ≠ ⊤ ↔ (Function.support (decDigits p q)).Finite := by
  classical
  constructor
  · intro hne
    by_contra hnotfin
    apply hne
    have hinf : (Function.support (decDigits p q)).Infinite :=
      Set.not_finite.mp hnotfin
    change pDigitSum p q = ⊤
    simp [pDigitSum, hinf]
  · intro hfin hne
    have heq : pDigitSum p q =
        ((∑ n ∈ hfin.toFinset, (decDigits p q n).val : ℕ) : WithTop ℕ) := by
      simp [pDigitSum, Set.not_infinite.mpr hfin]
    rw [heq] at hne
    exact WithTop.coe_ne_top hne

/-- Package the digits of a rational `q` with finite digit sum as a `DigitSeries`.-/
noncomputable def DigitSeries.ofRat (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ)
    (hq : pDigitSum p q ≠ ⊤) : DigitSeries where
  toFun n := (decDigits p q n).val
  fin_supp := by
    have hfin : (Function.support (decDigits p q)).Finite :=
      (pDigitSum_ne_top_iff p q).mp hq
    refine hfin.subset ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hzero
    apply hn
    rw [hzero]
    rfl

/-- `DigitSeries.ofRat` has all digits `< p`.
@isnad1 id=isp.1h2v.s4.b0de70f3a154 from=translated src=- shape=e1168106 vocab=75e6a0b5
-/
lemma DigitSeries.ofRat_IsP (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ)
    (hq : pDigitSum p q ≠ ⊤) : (DigitSeries.ofRat p q hq).IsP p := by
  intro n
  exact (decDigits p q n).isLt

/-- Indicator DigitSeries for a finite set of positive naturals.-/
noncomputable def indicatorSeries (A : Set ℕ) (hA_fin : A.Finite) : DigitSeries where
  toFun n := haveI := Classical.propDecidable ((n : ℕ) ∈ A);
    if (n : ℕ) ∈ A then 1 else 0
  fin_supp := by
    classical
    have hsupp_eq : Function.support (fun n : ℕ+ =>
        haveI := Classical.propDecidable ((n : ℕ) ∈ A);
        if (n : ℕ) ∈ A then (1 : ℕ) else 0) =
        (Subtype.val : ℕ+ → ℕ) ⁻¹' A := by
      ext n
      classical
      simp only [Function.mem_support, ne_eq]
      by_cases hin : (n : ℕ) ∈ A
      · simp only [hin, ↓reduceIte, one_ne_zero, not_false_eq_true, true_iff]
        exact hin
      · simp only [hin, ↓reduceIte, not_true_eq_false, false_iff]
        exact hin
    have hpre_fin : ((Subtype.val : ℕ+ → ℕ) ⁻¹' A).Finite :=
      hA_fin.preimage (PNat.coe_injective.injOn)
    exact hsupp_eq ▸ hpre_fin

/-- The indicator series at position n is 1 iff (n : ℕ) ∈ A.
@isnad1 id=eq.1h2v.s5.edea2488f5e9 from=translated src=- shape=1a566358 vocab=b1dd4753
-/
lemma indicatorSeries_apply (A : Set ℕ) (hA_fin : A.Finite) (n : ℕ+) :
    (indicatorSeries A hA_fin : ℕ+ → ℕ) n =
      haveI := Classical.propDecidable ((n : ℕ) ∈ A);
      (if (n : ℕ) ∈ A then 1 else 0) := rfl

/-- The indicator series is IsP for any prime p ≥ 2.
@isnad1 id=isp.1h2v.s4.943b6b8694a2 from=translated src=- shape=18a9a952 vocab=db758efc
-/
lemma indicatorSeries_IsP (p : ℕ) [Fact (Nat.Prime p)] (A : Set ℕ) (hA_fin : A.Finite) :
    (indicatorSeries A hA_fin).IsP p := by
  classical
  intro n
  rw [indicatorSeries_apply]
  split_ifs
  · exact (Fact.out : Nat.Prime p).one_lt
  · exact (Fact.out : Nat.Prime p).pos

end Sparse

end FormalizedSparse
