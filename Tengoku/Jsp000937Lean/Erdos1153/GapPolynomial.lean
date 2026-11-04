import Tengoku.Jsp000937Lean.Erdos1153.NodeOrder
import Tengoku.Seed.Order.Interval.Finset.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Signed polynomials on nodal gaps

For strictly ordered interpolation nodes, every Lagrange fundamental function
has a constant sign on each closed nodal gap.  This file fixes one sign
convention and packages the polynomial which agrees with the Lebesgue
function on that gap.

The convention is source-compatible with the polynomials `F_i` in Section 2
of de Boor--Pinkus (1978): the coefficient of a cardinal polynomial is `-1`
once for every node strictly between its index and the gap, and `+1` at both
endpoints of the gap.  In particular, adjacent gap polynomials sum to twice
the cardinal polynomial at their common node.
-/

namespace Erdos1153

open Polynomial
open scoped BigOperators

noncomputable section

/-- The left node index of the gap indexed by `g : Fin (n - 1)`.

This explicit embedding avoids relying on the non-definitional equality
`n - 1 + 1 = n`.-/
def gapLeftIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val, by omega⟩

/-- The right node index of the gap indexed by `g : Fin (n - 1)`.-/
def gapRightIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val + 1, by omega⟩

/--
@isnad1 id=eq.0h2v.s5.f9ac67d29ea8 from=translated src=- shape=ef12c50a vocab=c4031367
-/
@[simp]
lemma gapLeftIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapLeftIndex g).val = g.val :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.ea1aab8bc180 from=translated src=- shape=6cf84995 vocab=11392b3c
-/
@[simp]
lemma gapRightIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (gapRightIndex g).val = g.val + 1 :=
  rfl

/--
@isnad1 id=lt.0h2v.s4.7175bfd023cd from=translated src=- shape=da863e3e vocab=238c3244
-/
lemma gapLeftIndex_lt_rightIndex {n : ℕ} (g : Fin (n - 1)) :
    gapLeftIndex g < gapRightIndex g := by
  simp [Fin.lt_def]

/-- The closed real interval belonging to a nodal gap.-/
def closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Icc (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

/-- The open real interval belonging to a nodal gap.-/
def openGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : Set ℝ :=
  Set.Ioo (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

/--
@isnad1 id=lt.0h3v.s5.5a8730257e13 from=translated src=- shape=c77adde6 vocab=f7b2abb3
-/
lemma gap_left_lt_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    nodes.point (gapLeftIndex g) < nodes.point (gapRightIndex g) :=
  nodes.point_lt (gapLeftIndex_lt_rightIndex g)

/--
@isnad1 id=nonempty.0h3v.s4.c7c07c7814cc from=translated src=- shape=0d15d7bd vocab=66a3bec6
-/
lemma closedGap_nonempty {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (closedGap nodes g).Nonempty :=
  Set.nonempty_Icc.mpr (gap_left_lt_right nodes g).le

/--
@isnad1 id=nonempty.0h3v.s4.b6393bdef5df from=translated src=- shape=0d15d7bd vocab=f5963b42
-/
lemma openGap_nonempty {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (openGap nodes g).Nonempty :=
  Set.nonempty_Ioo.mpr (gap_left_lt_right nodes g)

/-- Whether the factor belonging to `j` contributes a negative sign to the
`k`th cardinal polynomial on gap `g`.

The two disjuncts say respectively that `j` lies between the gap and `k` on
the right, or between `k` and the gap on the left.-/
def gapNegative {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : Prop :=
  (j < k ∧ g.val < j.val) ∨ (k < j ∧ j.val ≤ g.val)

instance gapNegativeDecidable {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    Decidable (gapNegative g k j) := by
  unfold gapNegative
  infer_instance

/-- The sign of one normalized linear factor on a gap.-/
def gapSignFactor {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) : ℝ :=
  if gapNegative g k j then -1 else 1

/-- The sign of the `k`th Lagrange fundamental function on gap `g`.-/
def gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, gapSignFactor g k j

/--
@isnad1 id=or.0h4v.s5.9e2ec4812eed from=translated src=- shape=dac6b692 vocab=44740b59
-/
lemma gapSignFactor_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    gapSignFactor g k j = 1 ∨ gapSignFactor g k j = -1 := by
  simp only [gapSignFactor]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h4v.s5.ffc149f30926 from=translated src=- shape=7eeba603 vocab=75a7e29d
-/
@[simp]
lemma abs_gapSignFactor {n : ℕ} (g : Fin (n - 1)) (k j : Fin n) :
    |gapSignFactor g k j| = 1 := by
  rcases gapSignFactor_eq_one_or_neg_one g k j with h | h <;> simp [h]

/--
@isnad1 id=or.0h3v.s5.5935c193fc1f from=translated src=- shape=2c15a1b6 vocab=6bf4cde1
-/
lemma gapCoefficient_eq_one_or_neg_one {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k = 1 ∨ gapCoefficient g k = -1 := by
  classical
  rw [gapCoefficient]
  generalize Finset.univ.erase k = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      rcases gapSignFactor_eq_one_or_neg_one g k j with h | h <;>
        rcases ih with h' | h' <;> simp [h, h']

/--
@isnad1 id=eq.0h3v.s5.463f9f686b83 from=translated src=- shape=8a022a59 vocab=847f0aa4
-/
@[simp]
lemma abs_gapCoefficient {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    |gapCoefficient g k| = 1 := by
  rcases gapCoefficient_eq_one_or_neg_one g k with h | h <;> simp [h]

/--
@isnad1 id=ne.0h3v.s5.96e5b467e8cc from=translated src=- shape=cf10a08e vocab=1b79c7b2
-/
lemma gapCoefficient_ne_zero {n : ℕ} (g : Fin (n - 1)) (k : Fin n) :
    gapCoefficient g k ≠ 0 := by
  intro h
  have habs := abs_gapCoefficient g k
  simp [h] at habs

private lemma prod_gapSignFactor_eq_pow_card_filter {n : ℕ}
    (g : Fin (n - 1)) (k : Fin n) (s : Finset (Fin n)) :
    (∏ j ∈ s, gapSignFactor g k j) =
      (-1 : ℝ) ^ (s.filter (gapNegative g k)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs, Finset.filter_insert, ih]
      by_cases hj : gapNegative g k j
      · have hjfilter : j ∉ s.filter (gapNegative g k) := by simp [hjs]
        simp [hj, hjfilter, gapSignFactor, pow_succ]
      · simp [hj, gapSignFactor]

private lemma negative_filter_eq_Ioc {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioc k (gapLeftIndex g) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioc, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · have : j.val < k.val := hjklt
      omega
    · exact ⟨hkj, by simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg⟩
  · rintro ⟨hkj, hjg⟩
    refine ⟨hkj.ne', Or.inr ⟨hkj, ?_⟩⟩
    simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hjg

private lemma negative_filter_eq_Ioo {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    (Finset.univ.erase k).filter (gapNegative g k) =
      Finset.Ioo (gapLeftIndex g) k := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_Ioo, gapNegative]
  constructor
  · rintro ⟨hjk, (⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩)⟩
    · exact ⟨by simpa only [Fin.lt_def, gapLeftIndex_val] using hgj, hjklt⟩
    · have : k.val < j.val := hkj
      omega
  · rintro ⟨hgj, hjk⟩
    refine ⟨hjk.ne, Or.inl ⟨hjk, ?_⟩⟩
    simpa only [Fin.lt_def, gapLeftIndex_val] using hgj

/-- Closed form of the gap sign to the left of (or at) the left endpoint.
@isnad1 id=eq.1h3v.s6.7eeeb6def9e8 from=translated src=- shape=c7e60e71 vocab=00c20088
-/
lemma gapCoefficient_of_le {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hkg : k.val ≤ g.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (g.val - k.val) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioc g k hkg, Fin.card_Ioc]
  rfl

/-- Closed form of the gap sign to the right of the left endpoint.
@isnad1 id=eq.1h3v.s6.2f6ba712e308 from=translated src=- shape=18d4392a vocab=c59fbcef
-/
lemma gapCoefficient_of_lt {n : ℕ} (g : Fin (n - 1)) (k : Fin n)
    (hgk : g.val < k.val) :
    gapCoefficient g k = (-1 : ℝ) ^ (k.val - g.val - 1) := by
  classical
  rw [gapCoefficient, prod_gapSignFactor_eq_pow_card_filter,
    negative_filter_eq_Ioo g k hgk, Fin.card_Ioo]
  rfl

/--
@isnad1 id=eq.0h2v.s4.74e8d4ce0959 from=translated src=- shape=99c4cfb9 vocab=1272b25e
-/
@[simp]
lemma gapCoefficient_left {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapLeftIndex g) = 1 := by
  rw [gapCoefficient_of_le]
  · simp
  · simp

/--
@isnad1 id=eq.0h2v.s4.ef0db0b7e43d from=translated src=- shape=99c4cfb9 vocab=8f44b553
-/
@[simp]
lemma gapCoefficient_right {n : ℕ} (g : Fin (n - 1)) :
    gapCoefficient g (gapRightIndex g) = 1 := by
  rw [gapCoefficient_of_lt]
  · simp
  · simp

/-- Away from its own gap, the nodal values of a gap polynomial alternate in
sign.  This is the first sign pattern used in the source interlacing proof.
@isnad1 id=eq.1h3v.s6.f556595b7a7f from=translated src=- shape=013afe9f vocab=1c9121f4
-/
lemma gapCoefficient_right_eq_neg_left_of_ne {n : ℕ}
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    gapCoefficient g (gapRightIndex h) =
      -gapCoefficient g (gapLeftIndex h) := by
  rcases lt_or_gt_of_ne hhg with hhglt | hghlt
  · have hright_le : (gapRightIndex h).val ≤ g.val := by
      simp only [gapRightIndex_val]
      omega
    have hleft_le : (gapLeftIndex h).val ≤ g.val := by
      simp only [gapLeftIndex_val]
      omega
    rw [gapCoefficient_of_le g _ hright_le,
      gapCoefficient_of_le g _ hleft_le]
    have hexp : g.val - (gapLeftIndex h).val =
        (g.val - (gapRightIndex h).val) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring
  · have hgleft : g.val < (gapLeftIndex h).val := by
      simp only [gapLeftIndex_val]
      omega
    have hgright : g.val < (gapRightIndex h).val := by
      simp only [gapRightIndex_val]
      omega
    rw [gapCoefficient_of_lt g _ hgright,
      gapCoefficient_of_lt g _ hgleft]
    have hexp : (gapRightIndex h).val - g.val - 1 =
        ((gapLeftIndex h).val - g.val - 1) + 1 := by
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    rw [hexp, pow_succ]
    ring

/-- The lower gap in a pair of consecutive gaps.-/
def lowerAdjacentGap {n : ℕ} (q : Fin (n - 2)) : Fin (n - 1) :=
  ⟨q.val, by omega⟩

/-- The upper gap in a pair of consecutive gaps.-/
def upperAdjacentGap {n : ℕ} (q : Fin (n - 2)) : Fin (n - 1) :=
  ⟨q.val + 1, by omega⟩

/-- The common node in a pair of consecutive gaps.-/
def adjacentCommonNode {n : ℕ} (q : Fin (n - 2)) : Fin n :=
  ⟨q.val + 1, by omega⟩

/--
@isnad1 id=eq.0h2v.s5.0e5e7bb2ad38 from=translated src=- shape=9fd2ebc8 vocab=6c99ad95
-/
@[simp]
lemma lowerAdjacentGap_val {n : ℕ} (q : Fin (n - 2)) :
    (lowerAdjacentGap q).val = q.val :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.abb7163a4d3b from=translated src=- shape=fad8ba99 vocab=4d5321f6
-/
@[simp]
lemma upperAdjacentGap_val {n : ℕ} (q : Fin (n - 2)) :
    (upperAdjacentGap q).val = q.val + 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.599d452a7b2e from=translated src=- shape=6cf84995 vocab=0ab0c1cc
-/
@[simp]
lemma adjacentCommonNode_val {n : ℕ} (q : Fin (n - 2)) :
    (adjacentCommonNode q).val = q.val + 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.094250dfaa24 from=translated src=- shape=fe68457b vocab=5a7900bd
-/
lemma gapCoefficient_add_adjacent {n : ℕ} (q : Fin (n - 2)) (k : Fin n) :
    gapCoefficient (lowerAdjacentGap q) k +
        gapCoefficient (upperAdjacentGap q) k =
      if k = adjacentCommonNode q then 2 else 0 := by
  by_cases hleft : k.val ≤ q.val
  · have hlow : k.val ≤ (lowerAdjacentGap q).val := by simpa using hleft
    have hupp : k.val ≤ (upperAdjacentGap q).val := by simp only [upperAdjacentGap_val]; omega
    rw [gapCoefficient_of_le _ _ hlow, gapCoefficient_of_le _ _ hupp]
    have hexp : (upperAdjacentGap q).val - k.val =
        ((lowerAdjacentGap q).val - k.val) + 1 := by
      simp only [lowerAdjacentGap_val, upperAdjacentGap_val]
      omega
    rw [hexp, pow_succ]
    have hkne : k ≠ adjacentCommonNode q := by
      intro h
      have := congrArg Fin.val h
      simp only [adjacentCommonNode_val] at this
      omega
    simp [hkne]
  · have hqk : q.val < k.val := Nat.lt_of_not_ge hleft
    by_cases hcommon : k = adjacentCommonNode q
    · subst k
      have hlower : adjacentCommonNode q = gapRightIndex (lowerAdjacentGap q) := by
        apply Fin.ext
        simp
      have hupper : adjacentCommonNode q = gapLeftIndex (upperAdjacentGap q) := by
        apply Fin.ext
        simp
      have hlowCoeff : gapCoefficient (lowerAdjacentGap q) (adjacentCommonNode q) = 1 := by
        rw [hlower, gapCoefficient_right]
      have huppCoeff : gapCoefficient (upperAdjacentGap q) (adjacentCommonNode q) = 1 := by
        rw [hupper, gapCoefficient_left]
      norm_num [hlowCoeff, huppCoeff]
    · have hklarge : q.val + 1 < k.val := by
        have hneval : k.val ≠ q.val + 1 := by
          intro h
          apply hcommon
          apply Fin.ext
          simpa using h
        omega
      have hlow : (lowerAdjacentGap q).val < k.val := by simp; omega
      have hupp : (upperAdjacentGap q).val < k.val := by simp; omega
      rw [gapCoefficient_of_lt _ _ hlow, gapCoefficient_of_lt _ _ hupp,
        ite_eq_right hcommon]
      have hexp : k.val - (lowerAdjacentGap q).val - 1 =
          (k.val - (upperAdjacentGap q).val - 1) + 1 := by
        simp only [lowerAdjacentGap_val, upperAdjacentGap_val]
        omega
      rw [hexp, pow_succ]
      ring

/-- With at least three nodes, every gap sign vector contains a negative
coefficient.  The two-node exception is real: its Lebesgue function is
identically one on the only gap.
@isnad1 id=ex.1h2v.s5.cd0c299d8ac5 from=translated src=- shape=6a53d75b vocab=647ffda9
-/
lemma exists_gapCoefficient_eq_neg_one {n : ℕ} (hn : 3 ≤ n) (g : Fin (n - 1)) :
    ∃ k : Fin n, gapCoefficient g k = -1 := by
  by_cases hg0 : g.val = 0
  · let k : Fin n := ⟨2, by omega⟩
    refine ⟨k, ?_⟩
    have hgk : g.val < k.val := by simp [k, hg0]
    rw [gapCoefficient_of_lt g k hgk]
    simp [k, hg0]
  · let k : Fin n := ⟨g.val - 1, by omega⟩
    refine ⟨k, ?_⟩
    have hkg : k.val ≤ g.val := by simp [k]
    rw [gapCoefficient_of_le g k hkg]
    have hexp : g.val - k.val = 1 := by
      simp only [k]
      omega
    rw [hexp]
    norm_num

/-- The signed interpolation polynomial which agrees with the Lebesgue
function on the gap.-/
def gapPolynomial {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ[X] :=
  Lagrange.interpolate Finset.univ nodes.point (gapCoefficient g)

/--
@isnad1 id=eq.0h4v.s5.312d620ecac6 from=translated src=- shape=159ba562 vocab=c98883e2
-/
lemma gapPolynomial_eval_node {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1))
    (k : Fin n) :
    (gapPolynomial nodes g).eval (nodes.point k) = gapCoefficient g k := by
  simpa only [gapPolynomial] using
    (Lagrange.eval_interpolate_at_node (r := gapCoefficient g)
      nodes.injective.injOn (Finset.mem_univ k))

/-- Source adjacent-gap identity: consecutive signed gap polynomials sum to
twice the cardinal polynomial at their common node.
@isnad1 id=eq.0h3v.s6.31205110d01d from=translated src=- shape=de993683 vocab=ed8e7b0c
-/
lemma gapPolynomial_add_adjacent {n : ℕ} (nodes : OrderedNodes n)
    (q : Fin (n - 2)) :
    gapPolynomial nodes (lowerAdjacentGap q) +
        gapPolynomial nodes (upperAdjacentGap q) =
      Polynomial.C 2 * lagrangeBasis nodes.toNodeFamily (adjacentCommonNode q) := by
  classical
  simp only [gapPolynomial, Lagrange.interpolate_apply]
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_mul, ← Polynomial.C_add]
  rw [Finset.sum_eq_single (adjacentCommonNode q)]
  · rw [gapCoefficient_add_adjacent]
    simp [lagrangeBasis]
  · intro k _ hk
    rw [gapCoefficient_add_adjacent, ite_eq_right hk]
    simp
  · simp

/--
@isnad1 id=eq.0h3v.s5.9e5c4a7cdf35 from=translated src=- shape=4ece8a59 vocab=39b03ec6
-/
@[simp]
lemma gapPolynomial_eval_left {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapLeftIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_left]

/--
@isnad1 id=eq.0h3v.s5.35d41863735c from=translated src=- shape=4ece8a59 vocab=77d99292
-/
@[simp]
lemma gapPolynomial_eval_right {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapRightIndex g)) = 1 := by
  rw [gapPolynomial_eval_node, gapCoefficient_right]

/--
@isnad1 id=le.0h3v.s5.0b2572dc0d16 from=translated src=- shape=bd30260d vocab=1f663bde
-/
lemma degree_gapPolynomial_le {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).degree ≤ (n - 1 : ℕ) := by
  simpa only [gapPolynomial, Finset.card_univ, Fintype.card_fin] using
    (Lagrange.degree_interpolate_le (s := Finset.univ) (r := gapCoefficient g)
      nodes.injective.injOn)

private lemma numerator_nonneg_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ closedGap nodes g) :
    0 ≤ t - nodes.point j := by
  rw [sub_nonneg]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans ht.1

private lemma numerator_nonpos_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ closedGap nodes g) :
    t - nodes.point j ≤ 0 := by
  rw [sub_nonpos]
  exact ht.2.trans (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))

private lemma numerator_pos_of_le_gap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hjg : j.val ≤ g.val)
    (ht : t ∈ openGap nodes g) :
    0 < t - nodes.point j := by
  rw [sub_pos]
  exact (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simpa using hjg))).trans_lt ht.1

private lemma numerator_neg_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {j : Fin n} {t : ℝ} (hgj : g.val < j.val)
    (ht : t ∈ openGap nodes g) :
    t - nodes.point j < 0 := by
  rw [sub_neg]
  exact ht.2.trans_le (nodes.strictMono.monotone
    (Fin.le_iff_val_le_val.mpr (by simp only [gapRightIndex_val]; omega)))

private lemma denominator_pos_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hjk : j < k) :
    0 < nodes.point k - nodes.point j := by
  rw [sub_pos]
  exact nodes.point_lt hjk

private lemma denominator_neg_of_lt {n : ℕ} (nodes : OrderedNodes n) {j k : Fin n}
    (hkj : k < j) :
    nodes.point k - nodes.point j < 0 := by
  rw [sub_neg]
  exact nodes.point_lt hkj

/-- Each normalized linear factor has the sign encoded by `gapSignFactor` on
the closed gap.
@isnad1 id=le.2h6v.s6.0f98ee7df6fe from=translated src=- shape=6cd197b5 vocab=c2c4bf8d
-/
lemma gapSignFactor_mul_div_nonneg {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, ite_eq_left hneg, neg_one_mul]
    apply neg_nonneg.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_nonpos_of_nonpos_of_nonneg
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt).le
    · exact div_nonpos_of_nonneg_of_nonpos
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj).le
  · rw [gapSignFactor, ite_eq_right hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_nonneg
        (numerator_nonneg_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt).le
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_nonneg_of_nonpos
        (numerator_nonpos_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj).le

/-- In the open gap none of the factors vanish, so the signed factor is
strictly positive.
@isnad1 id=lt.2h6v.s6.96ee419a7774 from=translated src=- shape=6cd197b5 vocab=4e225369
-/
lemma gapSignFactor_mul_div_pos {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {k j : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapSignFactor g k j *
      ((t - nodes.point j) / (nodes.point k - nodes.point j)) := by
  by_cases hneg : gapNegative g k j
  · rw [gapSignFactor, ite_eq_left hneg, neg_one_mul]
    apply neg_pos.mpr
    rcases hneg with ⟨hjklt, hgj⟩ | ⟨hkj, hjg⟩
    · exact div_neg_of_neg_of_pos
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_pos_of_lt nodes hjklt)
    · exact div_neg_of_pos_of_neg
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_neg_of_lt nodes hkj)
  · rw [gapSignFactor, ite_eq_right hneg, one_mul]
    rcases lt_or_gt_of_ne hjk with hjklt | hkj
    · have hjg : j.val ≤ g.val := by
        by_contra h
        apply hneg
        exact Or.inl ⟨hjklt, Nat.lt_of_not_ge h⟩
      exact div_pos
        (numerator_pos_of_le_gap nodes g hjg ht)
        (denominator_pos_of_lt nodes hjklt)
    · have hgj : g.val < j.val := by
        by_contra h
        apply hneg
        exact Or.inr ⟨hkj, Nat.le_of_not_gt h⟩
      exact div_pos_of_neg_of_neg
        (numerator_neg_of_gap_lt nodes g hgj ht)
        (denominator_neg_of_lt nodes hkj)

/-- The signed fundamental function is nonnegative on its closed gap.
@isnad1 id=le.1h5v.s6.3236fad7364d from=translated src=- shape=e65219ab vocab=c881d6e5
-/
lemma gapCoefficient_mul_lagrangeFundamental_nonneg {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    0 ≤ gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_nonneg fun j hj =>
    gapSignFactor_mul_div_nonneg nodes g (Finset.mem_erase.mp hj).1 ht

/-- Strict signed positivity in the open gap.
@isnad1 id=lt.1h5v.s6.e9357200d4a9 from=translated src=- shape=e65219ab vocab=ceee5256
-/
lemma gapCoefficient_mul_lagrangeFundamental_pos {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ openGap nodes g) :
    0 < gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  rw [gapCoefficient, lagrangeFundamental, ← Finset.prod_mul_distrib]
  exact Finset.prod_pos fun j hj =>
    gapSignFactor_mul_div_pos nodes g (Finset.mem_erase.mp hj).1 ht

/-- Absolute value removes exactly the coefficient selected for the gap.
@isnad1 id=eq.1h5v.s6.0306387eef89 from=translated src=- shape=8399646d vocab=8176a1b7
-/
lemma abs_lagrangeFundamental_eq_gapCoefficient_mul {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (k : Fin n) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    |lagrangeFundamental nodes.toNodeFamily k t| =
      gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t := by
  calc
    |lagrangeFundamental nodes.toNodeFamily k t| =
        |gapCoefficient g k| * |lagrangeFundamental nodes.toNodeFamily k t| := by simp
    _ = |gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t| :=
      (abs_mul _ _).symm
    _ = gapCoefficient g k * lagrangeFundamental nodes.toNodeFamily k t :=
      abs_of_nonneg (gapCoefficient_mul_lagrangeFundamental_nonneg nodes g k ht)

/--
@isnad1 id=eq.0h4v.s5.e61ac95e86cf from=translated src=- shape=6dee0b4c vocab=4a888b9a
-/
lemma gapPolynomial_eval_eq_sum {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (t : ℝ) :
    (gapPolynomial nodes g).eval t =
      ∑ k : Fin n, gapCoefficient g k *
        lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  simp only [gapPolynomial, Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  change gapCoefficient g k * (lagrangeBasis nodes.toNodeFamily k).eval t = _
  rw [lagrangeBasis_eval]

/-- The Lagrange fundamental functions form a partition of unity.
@isnad1 id=eq.1h3v.s5.94a42f3de45c from=translated src=- shape=25ffc1cd vocab=ae0748bd
-/
lemma sum_lagrangeFundamental_eq_one {n : ℕ} (nodes : OrderedNodes n)
    (hn : 0 < n) (t : ℝ) :
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t = 1 := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hbasis := Lagrange.sum_basis nodes.injective.injOn huniv
  have heval := congrArg (Polynomial.eval t) hbasis
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_one] at heval
  calc
    ∑ k : Fin n, lagrangeFundamental nodes.toNodeFamily k t =
        ∑ k : Fin n, (Lagrange.basis Finset.univ nodes.point k).eval t := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← lagrangeBasis_eval]
      rfl
    _ = 1 := by simpa using heval

/-- On the whole closed nodal gap, the signed polynomial is the Lebesgue
function.  Endpoint inclusion is useful later when taking compact maxima.
@isnad1 id=eq.1h4v.s5.d34e288c1e12 from=translated src=- shape=2c0841a6 vocab=03ee018f
-/
lemma lebesgueFunction_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    lebesgueFunction nodes.toNodeFamily t = (gapPolynomial nodes g).eval t := by
  rw [lebesgueFunction, gapPolynomial_eval_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact abs_lagrangeFundamental_eq_gapCoefficient_mul nodes g k ht

/-- For at least three nodes the Lebesgue/gap polynomial is strictly greater
than one in the open gap.  The explicit cardinality hypothesis records the
genuine two-node exception.
@isnad1 id=lt.2h4v.s5.36a20890100f from=translated src=- shape=20e06a42 vocab=24930775
-/
lemma one_lt_eval_gapPolynomial_of_mem_openGap {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ openGap nodes g) :
    1 < (gapPolynomial nodes g).eval t := by
  obtain ⟨k, hcoeff⟩ := exists_gapCoefficient_eq_neg_one hn g
  let f : Fin n → ℝ := fun j => lagrangeFundamental nodes.toNodeFamily j t
  have hfk : f k < 0 := by
    have hpos := gapCoefficient_mul_lagrangeFundamental_pos nodes g k ht
    rw [hcoeff, neg_one_mul] at hpos
    exact neg_pos.mp hpos
  have hsum : ∑ j : Fin n, f j = 1 := by
    exact sum_lagrangeFundamental_eq_one nodes (by omega) t
  have hsumErase : ∑ j ∈ Finset.univ.erase k, f j = 1 - f k := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ k)] at hsum
    linarith
  have habsErase :
      |∑ j ∈ Finset.univ.erase k, f j| ≤
        ∑ j ∈ Finset.univ.erase k, |f j| :=
    Finset.abs_sum_le_sum_abs f (Finset.univ.erase k)
  have hlower : 1 - 2 * f k ≤ lebesgueFunction nodes.toNodeFamily t := by
    rw [lebesgueFunction, ← Finset.add_sum_erase Finset.univ
      (fun j => |f j|) (Finset.mem_univ k)]
    calc
      1 - 2 * f k = |f k| + |∑ j ∈ Finset.univ.erase k, f j| := by
        rw [abs_of_neg hfk, hsumErase, abs_of_pos (by linarith)]
        ring
      _ ≤ |f k| + ∑ j ∈ Finset.univ.erase k, |f j| :=
        add_le_add (le_refl _) habsErase
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g
    ⟨ht.1.le, ht.2.le⟩]
  linarith

/-- The local Lebesgue height on the `g`th closed gap.-/
def gapHeight {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  lebesgueOn nodes.toNodeFamily
    (nodes.point (gapLeftIndex g)) (nodes.point (gapRightIndex g))

/-- The compact gap height is attained by the signed gap polynomial.
@isnad1 id=ex.0h3v.s6.09c36f729ef0 from=translated src=- shape=5dc07e6c vocab=b65fa2fe
-/
lemma exists_gapHeight_eq_eval_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    ∃ t ∈ closedGap nodes g,
      gapHeight nodes g = (gapPolynomial nodes g).eval t ∧
        ∀ u ∈ closedGap nodes g,
          (gapPolynomial nodes g).eval u ≤ (gapPolynomial nodes g).eval t := by
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
    (gap_left_lt_right nodes g).le
  refine ⟨t, ht, ?_, ?_⟩
  · rw [gapHeight, heq, ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
  · intro u hu
    rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g hu,
      ← lebesgueFunction_eq_eval_gapPolynomial nodes g ht]
    exact hmax u hu

end

end Erdos1153
