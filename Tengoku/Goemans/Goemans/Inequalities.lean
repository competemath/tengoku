/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.RhoStar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The core inequalities of Theorem A

Model-free real-arithmetic lemmas, the algebraic hearts of the paper's proofs:

* `pair_bound` — Lemma 2: a blocked pair forces `z_i + z_j ≤ 1`;
* `splitLP_shifted`, `splitLP` — Lemma 3 (the split LP): all pairs blocked
  forces `z₁ + z₂ + z₃ ≤ 4 - 2√2`; the shift `(dᵢ, fᵢ) ↦ (D, fᵢ + D - dᵢ)`
  reduces to the case `d₁ = d₃ = D`, and the one-variable maximization is
  witnessed by the square `(√2·δ - D)² ≥ 0` (AM–GM at `δ = D/√2`);
* `weight_core_a/b/c/d` — the four cases of Lemma 5a (the weight inequality),
  stated abstractly in `r` with the only `ρ*`-facts used being `1 ≤ r` and
  the endpoint inequalities `1 ≤ r(aᵢ + aⱼ)`, `2 ≤ r(a₁ + a₂ + a₃)`.

Each proof is a nonnegative-combination certificate (checked by
`nlinarith`/`linarith` from explicitly provided product terms), exactly the
combinations written out in the paper.
-/

namespace Goemans

open Real

/-! ### Lemma 2: blocked pairs -/

/-- **Lemma 2 pattern.** If a pair is blocked, `f₁ + f₂ ≤ d₁ + d₂ - D`
(closure form), then the cheap fractions satisfy `f₁/d₁ + f₂/d₂ ≤ 1`.-/
theorem pair_bound {d1 d2 f1 f2 D : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2)
    (hD1 : d1 ≤ D) (hD2 : d2 ≤ D)
    (hblock : f1 + f2 ≤ d1 + d2 - D) :
    f1 / d1 + f2 / d2 ≤ 1 := by
  rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2), div_le_one (mul_pos hd1 hd2)]
  rcases le_total d1 d2 with h | h
  · nlinarith [mul_nonneg hf2 (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 hD2) hd2.le,
      mul_le_mul_of_nonneg_left hblock hd2.le]
  · nlinarith [mul_nonneg hf1 (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 hD1) hd1.le,
      mul_le_mul_of_nonneg_left hblock hd1.le]

/-- Strict form of `pair_bound`, retaining the slack in a blocked-pair
constraint.-/
theorem pair_bound_lt {d1 d2 f1 f2 D : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2)
    (hD1 : d1 ≤ D) (hD2 : d2 ≤ D)
    (hblock : f1 + f2 < d1 + d2 - D) :
    f1 / d1 + f2 / d2 < 1 := by
  rw [div_add_div _ _ (ne_of_gt hd1) (ne_of_gt hd2),
    div_lt_one (mul_pos hd1 hd2)]
  rcases le_total d1 d2 with h | h
  · have hb := mul_lt_mul_of_pos_right hblock hd2
    nlinarith [mul_nonneg hf2 (sub_nonneg.2 h),
      mul_nonneg (sub_nonneg.2 hD2) hd2.le]
  · have hb := mul_lt_mul_of_pos_right hblock hd1
    nlinarith [mul_nonneg hf1 (sub_nonneg.2 h),
      mul_nonneg (sub_nonneg.2 hD1) hd1.le]

/-! ### Lemma 3: the split LP -/

/-- **Lemma 3, shifted core.** With `d₁ = d₃ = D` and `δ = d₂`, the all-blocked
closure system forces `Σ z ≤ 4 - 2√2`. The extremal certificate is
`(√2·δ - D)² ≥ 0`.-/
theorem splitLP_shifted {D δ f1 f2 f3 : ℝ} (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hf2δ : f2 ≤ δ)
    (h12 : f1 + f2 ≤ δ) (h23 : f2 + f3 ≤ δ) (h123 : f1 + f2 + f3 ≤ D) :
    f1 / D + f2 / δ + f3 / D ≤ 4 - 2 * Real.sqrt 2 := by
  have hexp : f1 / D + f2 / δ + f3 / D = (f1 * δ + f2 * D + f3 * δ) / (D * δ) := by
    field_simp
  rw [hexp, div_le_iff₀ (mul_pos hD hδ)]
  have hsq : 0 ≤ 2 * δ ^ 2 - 2 * Real.sqrt 2 * δ * D + D ^ 2 := by
    have hexp2 : (Real.sqrt 2 * δ - D) ^ 2 =
        2 * δ ^ 2 - 2 * Real.sqrt 2 * δ * D + D ^ 2 := by
      linear_combination (δ ^ 2) * sqrt2_mul_self
    exact hexp2 ▸ sq_nonneg _
  have hs2 := sqrt2_mul_self
  rcases le_total D (2 * δ) with hcase | hcase
  · -- D ≤ 2δ: combination (2δ-D)·s₁ + (D-δ)·s₂ + (√2δ-D)²
    have t1 : 0 ≤ (2 * δ - D) * (D - f2 - (f1 + f3)) :=
      mul_nonneg (by linarith) (by linarith)
    have t2 : 0 ≤ (D - δ) * (2 * δ - 2 * f2 - (f1 + f3)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [t1, t2, hsq]
  · -- 2δ ≤ D: combination δ·s₂ + (δ-f2)(D-2δ) + (3-2√2)Dδ
    have h3 : 0 ≤ 3 - 2 * Real.sqrt 2 := by
      nlinarith [sq_nonneg (2 * Real.sqrt 2 - 3), hs2]
    have t1 : 0 ≤ δ * (2 * δ - 2 * f2 - (f1 + f3)) :=
      mul_nonneg hδ.le (by linarith)
    have t2 : 0 ≤ (δ - f2) * (D - 2 * δ) :=
      mul_nonneg (by linarith) (by linarith)
    have t3 : 0 ≤ (3 - 2 * Real.sqrt 2) * (D * δ) :=
      mul_nonneg h3 (mul_pos hD hδ).le
    nlinarith [t1, t2, t3]

/-- **Lemma 3 (the split LP).** If all three pairs are blocked (closure form),
then `z₁ + z₂ + z₃ ≤ 4 - 2√2`. The proof shifts `(d₁, f₁)` and `(d₃, f₃)` up
to demand `D` — which only increases each `zᵢ` — and applies the shifted
core with `δ = d₂`.-/
theorem splitLP {d1 d2 d3 f1 f2 f3 D : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hf1d : f1 ≤ d1) (hf2d : f2 ≤ d2) (hf3d : f3 ≤ d3)
    (hD1 : d1 ≤ D) (hD2 : d2 ≤ D) (hD3 : d3 ≤ D)
    (h12 : f1 + f2 ≤ d1 + d2 - D) (h23 : f2 + f3 ≤ d2 + d3 - D)
    (h13 : f1 + f2 + f3 ≤ d1 + d3 - D) :
    f1 / d1 + f2 / d2 + f3 / d3 ≤ 4 - 2 * Real.sqrt 2 := by
  have hD : 0 < D := lt_of_lt_of_le hd1 hD1
  have key := splitLP_shifted (D := D) (δ := d2)
    (f1 := f1 + (D - d1)) (f2 := f2) (f3 := f3 + (D - d3))
    hD hd2 hD2 hf2d
    (by linarith) (by linarith) (by linarith)
  have mono1 : f1 / d1 ≤ (f1 + (D - d1)) / D := by
    rw [div_le_div_iff₀ hd1 hD]
    nlinarith [mul_nonneg (sub_nonneg.2 hf1d) (sub_nonneg.2 hD1)]
  have mono3 : f3 / d3 ≤ (f3 + (D - d3)) / D := by
    rw [div_le_div_iff₀ hd3 hD]
    nlinarith [mul_nonneg (sub_nonneg.2 hf3d) (sub_nonneg.2 hD3)]
  linarith [key, mono1, mono3]

/-- Strict form of the split LP. Increasing the first shifted flow by a
positive amount smaller than the two relevant constraint slacks reduces the
claim to the closed split LP while strictly increasing its objective.-/
theorem splitLP_lt {d1 d2 d3 f1 f2 f3 D : ℝ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3)
    (hf1 : 0 ≤ f1) (hf3 : 0 ≤ f3)
    (hf1d : f1 ≤ d1) (hf2d : f2 ≤ d2) (hf3d : f3 ≤ d3)
    (hD1 : d1 ≤ D) (hD2 : d2 ≤ D) (hD3 : d3 ≤ D)
    (h12 : f1 + f2 < d1 + d2 - D)
    (h23 : f2 + f3 ≤ d2 + d3 - D)
    (h13 : f1 + f2 + f3 < d1 + d3 - D) :
    f1 / d1 + f2 / d2 + f3 / d3 < 4 - 2 * Real.sqrt 2 := by
  have hD : 0 < D := lt_of_lt_of_le hd1 hD1
  let g1 := f1 + (D - d1)
  let g3 := f3 + (D - d3)
  let ε := min (d2 - (g1 + f2)) (D - (g1 + f2 + g3)) / 2
  have hs12 : 0 < d2 - (g1 + f2) := by
    dsimp [g1]
    linarith
  have hs13 : 0 < D - (g1 + f2 + g3) := by
    dsimp [g1, g3]
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε12 : ε ≤ d2 - (g1 + f2) := by
    dsimp [ε]
    have hmin := min_le_left (d2 - (g1 + f2)) (D - (g1 + f2 + g3))
    have hmin0 : 0 ≤ min (d2 - (g1 + f2)) (D - (g1 + f2 + g3)) :=
      le_of_lt (lt_min hs12 hs13)
    linarith
  have hε13 : ε ≤ D - (g1 + f2 + g3) := by
    dsimp [ε]
    have hmin := min_le_right (d2 - (g1 + f2)) (D - (g1 + f2 + g3))
    have hmin0 : 0 ≤ min (d2 - (g1 + f2)) (D - (g1 + f2 + g3)) :=
      le_of_lt (lt_min hs12 hs13)
    linarith
  have hg10 : 0 ≤ g1 := by
    dsimp [g1]
    linarith
  have hg30 : 0 ≤ g3 := by
    dsimp [g3]
    linarith
  have key := splitLP_shifted (D := D) (δ := d2)
    (f1 := g1 + ε) (f2 := f2) (f3 := g3)
    hD hd2 hD2 hf2d
    (by linarith) (by
      dsimp [g3]
      linarith) (by linarith)
  have mono1 : f1 / d1 ≤ g1 / D := by
    dsimp [g1]
    rw [div_le_div_iff₀ hd1 hD]
    nlinarith [mul_nonneg (sub_nonneg.2 hf1d) (sub_nonneg.2 hD1)]
  have mono3 : f3 / d3 ≤ g3 / D := by
    dsimp [g3]
    rw [div_le_div_iff₀ hd3 hD]
    nlinarith [mul_nonneg (sub_nonneg.2 hf3d) (sub_nonneg.2 hD3)]
  have hinc : g1 / D < (g1 + ε) / D :=
    (div_lt_div_iff_of_pos_right hD).2 (by linarith)
  linarith

/-! ### Lemma 5a: the weight inequality, case by case

Throughout, `aᵢ = 1 - zᵢ ∈ [0,1]` are the expensive fractions and `mᵢ ≥ 0`
the (nonnegative) savings. The four cases of the paper's Lemma 5a; the
minimum over admissible routings is bounded by exhibiting an explicit
routing in each case, so each core takes the form `LHS ≤ r·(Σ mᵢaᵢ)` for the
appropriate exhibited left side. -/

/-- **Case (a) core** (all pairs blocked; routing the largest saving `m₃`
cheap). Given the endpoint facts `1 ≤ r(a₁+a₃)` and `2 ≤ r(a₁+a₂+a₃)`, with
`m₂ ≤ m₁ ≤ m₃`: `m₁ + m₂ ≤ r(m₁a₁ + m₂a₂ + m₃a₃)`. This is the affinity-in-β
argument of the paper.-/
theorem weight_core_a {r a1 a2 a3 m1 m2 m3 : ℝ}
    (hm2 : 0 ≤ m2) (hm12 : m2 ≤ m1) (hm13 : m1 ≤ m3)
    (ha3 : 0 ≤ a3) (hr : 0 ≤ r)
    (h13 : 1 ≤ r * (a1 + a3)) (hsum : 2 ≤ r * (a1 + a2 + a3)) :
    m1 + m2 ≤ r * (m1 * a1 + m2 * a2 + m3 * a3) := by
  have t1 : 0 ≤ (m1 - m2) * (r * (a1 + a3) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have t2 : 0 ≤ m2 * (r * (a1 + a2 + a3) - 2) := mul_nonneg hm2 (by linarith)
  have t3 : 0 ≤ r * a3 * (m3 - m1) := mul_nonneg (mul_nonneg hr ha3) (by linarith)
  nlinarith [t1, t2, t3]

/-- Strict case-(a) core. Strict endpoint inequalities make the certificate
strict whenever the weighted expensive-fraction sum is positive.-/
theorem weight_core_a_lt {r a1 a2 a3 m1 m2 m3 : ℝ}
    (hm2 : 0 ≤ m2) (hm12 : m2 ≤ m1) (hm13 : m1 ≤ m3)
    (ha3 : 0 ≤ a3) (hr : 0 ≤ r)
    (h13 : 1 < r * (a1 + a3)) (hsum : 2 < r * (a1 + a2 + a3))
    (hW : 0 < m1 * a1 + m2 * a2 + m3 * a3) :
    m1 + m2 < r * (m1 * a1 + m2 * a2 + m3 * a3) := by
  by_cases hm20 : m2 = 0
  · by_cases hm10 : m1 = 0
    · simp only [hm20, hm10, zero_mul, zero_add] at hW ⊢
      have hrpos : 0 < r := by
        rcases hr.eq_or_lt with rfl | hrpos
        · norm_num at h13
        · exact hrpos
      exact mul_pos hrpos hW
    · have hm10le : 0 ≤ m1 := le_trans hm2 hm12
      have hm1pos : 0 < m1 := lt_of_le_of_ne hm10le (Ne.symm hm10)
      have t1 : 0 < (m1 - m2) * (r * (a1 + a3) - 1) :=
        mul_pos (by linarith) (by linarith)
      have t2 : 0 ≤ m2 * (r * (a1 + a2 + a3) - 2) :=
        mul_nonneg hm2 (by linarith)
      have t3 : 0 ≤ r * a3 * (m3 - m1) :=
        mul_nonneg (mul_nonneg hr ha3) (by linarith)
      nlinarith [t1, t2, t3]
  · have hm2pos : 0 < m2 := lt_of_le_of_ne hm2 (Ne.symm hm20)
    have t1 : 0 ≤ (m1 - m2) * (r * (a1 + a3) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have t2 : 0 < m2 * (r * (a1 + a2 + a3) - 2) :=
      mul_pos hm2pos (by linarith)
    have t3 : 0 ≤ r * a3 * (m3 - m1) :=
      mul_nonneg (mul_nonneg hr ha3) (by linarith)
    nlinarith [t1, t2, t3]

/-- **Case (b) core** (exactly the pair `{i,j}` admissible, `k` the third
index, so `{i,k}` and `{j,k}` are blocked): the cheaper of the two available
routings — `{i,j}` (paying `m_k`) or `{k}` (paying `m_i + m_j`) — is within
`r·(Σ m a)`. Only `1 ≤ r` and the two blocked-pair endpoints are used.-/
theorem weight_core_b {r ai aj ak mi mj mk : ℝ}
    (hmi : 0 ≤ mi) (hmj : 0 ≤ mj) (hmk : 0 ≤ mk)
    (hai : 0 ≤ ai) (haj : 0 ≤ aj) (hak : 0 ≤ ak) (hr : 1 ≤ r)
    (hik : 1 ≤ r * (ai + ak)) (hjk : 1 ≤ r * (aj + ak)) :
    min (mi + mj) mk ≤ r * (mi * ai + mj * aj + mk * ak) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  rcases le_total mk mi with h | h
  · -- mk ≤ mi
    refine le_trans (min_le_right _ _) ?_
    have t1 : 0 ≤ r * ai * (mi - mk) := mul_nonneg (mul_nonneg hr0 hai) (by linarith)
    have t2 : 0 ≤ mk * (r * (ai + ak) - 1) := mul_nonneg hmk (by linarith)
    have t3 : 0 ≤ r * (mj * aj) := mul_nonneg hr0 (mul_nonneg hmj haj)
    nlinarith [t1, t2, t3]
  · rcases le_total (mi + mj) mk with h2 | h2
    · -- mi + mj ≤ mk
      refine le_trans (min_le_left _ _) ?_
      have t1 : 0 ≤ r * ak * (mk - mi - mj) :=
        mul_nonneg (mul_nonneg hr0 hak) (by linarith)
      have t2 : 0 ≤ mi * (r * (ai + ak) - 1) := mul_nonneg hmi (by linarith)
      have t3 : 0 ≤ mj * (r * (aj + ak) - 1) := mul_nonneg hmj (by linarith)
      nlinarith [t1, t2, t3]
    · -- max(mi, mj) ≤ mk ≤ mi + mj: the θ-splitting certificate,
      -- scaled by (mi + mj) to avoid division
      refine le_trans (min_le_right _ _) ?_
      rcases eq_or_lt_of_le (by linarith : (0 : ℝ) ≤ mi + mj) with h0 | h0
      · -- mi + mj = 0 forces mi = mj = mk = 0
        have hmi0 : mi = 0 := le_antisymm (by linarith) hmi
        have hmj0 : mj = 0 := le_antisymm (by linarith) hmj
        have hmk0 : mk = 0 := le_antisymm (by linarith) hmk
        simp [hmi0, hmj0, hmk0]
      · have t1 : 0 ≤ r * (mi * ai) * (mi + mj - mk) :=
          mul_nonneg (mul_nonneg hr0 (mul_nonneg hmi hai)) (by linarith)
        have t2 : 0 ≤ r * (mj * aj) * (mi + mj - mk) :=
          mul_nonneg (mul_nonneg hr0 (mul_nonneg hmj haj)) (by linarith)
        have t3 : 0 ≤ (r * (ai + ak) - 1) * (mi * mk) :=
          mul_nonneg (by linarith) (mul_nonneg hmi hmk)
        have t4 : 0 ≤ (r * (aj + ak) - 1) * (mj * mk) :=
          mul_nonneg (by linarith) (mul_nonneg hmj hmk)
        have scaled : (mi + mj) * mk ≤
            (mi + mj) * (r * (mi * ai + mj * aj + mk * ak)) := by
          nlinarith [t1, t2, t3, t4]
        exact le_of_mul_le_mul_left scaled h0

/-- **Case (c) core** (the pair `{i,k}` blocked, the other two pairs
admissible): the cheaper of the routings `{j,k}` (paying `mi`) and `{i,j}`
(paying `mk`) is within `r·(Σ m a)`.-/
theorem weight_core_c {r ai aj ak mi mj mk : ℝ}
    (hmi : 0 ≤ mi) (hmj : 0 ≤ mj) (hmk : 0 ≤ mk)
    (hai : 0 ≤ ai) (haj : 0 ≤ aj) (hak : 0 ≤ ak) (hr : 1 ≤ r)
    (hik : 1 ≤ r * (ai + ak)) :
    min mi mk ≤ r * (mi * ai + mj * aj + mk * ak) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have t3 : 0 ≤ r * (mj * aj) := mul_nonneg hr0 (mul_nonneg hmj haj)
  rcases le_total mi mk with h | h
  · refine le_trans (min_le_left _ _) ?_
    have t1 : 0 ≤ mi * (r * (ai + ak) - 1) := mul_nonneg hmi (by linarith)
    have t2 : 0 ≤ r * ak * (mk - mi) := mul_nonneg (mul_nonneg hr0 hak) (by linarith)
    nlinarith [t1, t2, t3]
  · refine le_trans (min_le_right _ _) ?_
    have t1 : 0 ≤ mk * (r * (ai + ak) - 1) := mul_nonneg hmk (by linarith)
    have t2 : 0 ≤ r * ai * (mi - mk) := mul_nonneg (mul_nonneg hr0 hai) (by linarith)
    nlinarith [t1, t2, t3]

/-- **Case (d) core** (all pairs admissible, triple blocked, which forces
`1 ≤ r(a₁+a₂+a₃)` — indeed `Σ dᵢaᵢ > D`): routing the two largest savings
cheap pays `min m`, which is within `r·(Σ m a)`.-/
theorem weight_core_d {r a1 a2 a3 m1 m2 m3 : ℝ}
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hm3 : 0 ≤ m3)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (hr : 0 ≤ r)
    (hsum : 1 ≤ r * (a1 + a2 + a3)) :
    min m1 (min m2 m3) ≤ r * (m1 * a1 + m2 * a2 + m3 * a3) := by
  set μ := min m1 (min m2 m3) with hμ
  have hμ1 : μ ≤ m1 := min_le_left _ _
  have hμ2 : μ ≤ m2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hμ3 : μ ≤ m3 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hμ0 : 0 ≤ μ := le_min hm1 (le_min hm2 hm3)
  have t1 : 0 ≤ r * a1 * (m1 - μ) := mul_nonneg (mul_nonneg hr ha1) (by linarith)
  have t2 : 0 ≤ r * a2 * (m2 - μ) := mul_nonneg (mul_nonneg hr ha2) (by linarith)
  have t3 : 0 ≤ r * a3 * (m3 - μ) := mul_nonneg (mul_nonneg hr ha3) (by linarith)
  have t4 : 0 ≤ μ * (r * (a1 + a2 + a3) - 1) := mul_nonneg hμ0 (by linarith)
  nlinarith [t1, t2, t3, t4]

end Goemans
