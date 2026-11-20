import Tengoku.Seed.Algebra.Order.Floor.Div
import Tengoku.Seed.Data.Fin.Embedding
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Padding normalized ranks

This file formalizes the arithmetic rank-padding map
`j ↦ ⌈q * j / q₀⌉` used in the thermodynamic ranked-cover argument.
-/

namespace BurningPath

/-- The natural-number value of the padded rank `⌈q * j / q₀⌉`.-/
def rankPaddingValue (q₀ q j : ℕ) : ℕ :=
  q * j ⌈/⌉ q₀

private theorem ceilDiv_add_denominator (n d : ℕ) (hd : 0 < d) :
    (n + d) ⌈/⌉ d = n ⌈/⌉ d + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div]
  have h : n + d + d - 1 = (n + d - 1) + d := by omega
  rw [h, Nat.add_div_right _ hd]

/-- When `1 ≤ q₀ ≤ q`, padded rank values increase strictly.
@isnad1 id=strictmo.2h2v.s4.4d9db169e432 from=translated src=- shape=1f09dc24 vocab=5ca5489f
-/
theorem rankPaddingValue_strictMono {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) :
    StrictMono (rankPaddingValue q₀ q) := by
  intro i j hij
  have hq₀pos : 0 < q₀ := by omega
  have hstep : q * i + q₀ ≤ q * j := by
    calc
      q * i + q₀ ≤ q * i + q := Nat.add_le_add_left hqq₀ (q * i)
      _ = q * (i + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ q * j := Nat.mul_le_mul_left q (Nat.add_one_le_iff.mpr hij)
  have hmono :
      (q * i + q₀) ⌈/⌉ q₀ ≤ (q * j) ⌈/⌉ q₀ :=
    (gc_mul_ceilDiv hq₀pos).monotone_l hstep
  rw [ceilDiv_add_denominator _ _ hq₀pos] at hmono
  exact Nat.lt_iff_add_one_le.mpr hmono

private theorem rankPaddingValue_lt {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q)
    (j : Fin q₀) :
    rankPaddingValue q₀ q j.1 < q := by
  have hq₀pos : 0 < q₀ := by omega
  calc
    rankPaddingValue q₀ q j.1 < rankPaddingValue q₀ q q₀ :=
      rankPaddingValue_strictMono hq₀ hqq₀ j.isLt
    _ = q := by
      simpa [rankPaddingValue, Nat.mul_comm] using smul_ceilDiv hq₀pos q

/-- The rank-padding map `j ↦ ⌈q * j / q₀⌉` as an embedding `Fin q₀ ↪ Fin q`.-/
def rankPaddingEmbedding (q₀ q : ℕ) (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) :
    Fin q₀ ↪ Fin q where
  toFun j := ⟨rankPaddingValue q₀ q j.1, rankPaddingValue_lt hq₀ hqq₀ j⟩
  inj' _i _j hij :=
    Fin.ext <| (rankPaddingValue_strictMono hq₀ hqq₀).injective (congrArg Fin.val hij)

/--
@isnad1 id=eq.2h3v.s5.4d14fc4acd89 from=translated src=- shape=1458ccce vocab=781d78d6
-/
@[simp]
theorem rankPaddingEmbedding_apply_val {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q)
    (j : Fin q₀) :
    (rankPaddingEmbedding q₀ q hq₀ hqq₀ j).1 = rankPaddingValue q₀ q j.1 :=
  rfl

/-- The zero rank remains zero under rank padding.
@isnad1 id=eq.2h2v.s5.23b57a1cab71 from=translated src=- shape=705efb9b vocab=2be45976
-/
@[simp]
theorem rankPaddingEmbedding_zero {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) :
    rankPaddingEmbedding q₀ q hq₀ hqq₀ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  apply Fin.ext
  simp [rankPaddingValue]

/-- The rank-padding embedding is strictly increasing.
@isnad1 id=strictmo.2h2v.s5.62d0d7388d6b from=translated src=- shape=ae6feeae vocab=f9978b0c
-/
theorem rankPaddingEmbedding_strictMono {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) :
    StrictMono (rankPaddingEmbedding q₀ q hq₀ hqq₀) := by
  intro i j hij
  exact rankPaddingValue_strictMono hq₀ hqq₀ hij

/-- Every padded rank is at most `q - 1`.
@isnad1 id=le.2h3v.s6.0328a67c5770 from=translated src=- shape=5eb33779 vocab=aa59bbcd
-/
theorem rankPaddingEmbedding_le_sub_one {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q)
    (j : Fin q₀) :
    (rankPaddingEmbedding q₀ q hq₀ hqq₀ j).1 ≤ q - 1 := by
  omega

/-- Ceiling division gives the cross-multiplied normalized-rank inequality.
@isnad1 id=le.2h3v.s6.2c2f31168466 from=translated src=- shape=e7e8eec1 vocab=f3f12e15
-/
theorem rankPaddingEmbedding_cross_mul {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q)
    (j : Fin q₀) :
    q * j.1 ≤ q₀ * (rankPaddingEmbedding q₀ q hq₀ hqq₀ j).1 := by
  have hq₀pos : 0 < q₀ := by omega
  simpa [rankPaddingValue] using
    (le_smul_ceilDiv (a := q₀) (b := q * j.1) hq₀pos)

/-- Rank padding never decreases the normalized real rank.
@isnad1 id=le.2h3v.s6.dcb0dfc5965f from=translated src=- shape=c32af66e vocab=75f67562
-/
theorem rankPaddingEmbedding_normalized_le {q₀ q : ℕ} (hq₀ : 1 ≤ q₀)
    (hqq₀ : q₀ ≤ q) (j : Fin q₀) :
    (j.1 : ℝ) / q₀ ≤ ((rankPaddingEmbedding q₀ q hq₀ hqq₀ j).1 : ℝ) / q := by
  have hq₀pos : 0 < q₀ := by omega
  have hqpos : 0 < q := hq₀pos.trans_le hqq₀
  rw [div_le_div_iff₀ (by exact_mod_cast hq₀pos) (by exact_mod_cast hqpos)]
  have hcross :
      j.1 * q ≤ (rankPaddingEmbedding q₀ q hq₀ hqq₀ j).1 * q₀ := by
    simpa [Nat.mul_comm] using rankPaddingEmbedding_cross_mul hq₀ hqq₀ j
  exact_mod_cast hcross

/-! ## Generic normalized ranked covers -/

universe u v

variable {X : Type u} {C : Type v}

/--
An abstract normalized ranked cover: center `j` is used at normalized radius `j / q`.
The relation `covers c r x` is supplied by the application.-/
def IsNormalizedRankedCover (covers : C → ℝ → X → Prop) {q : ℕ}
    (centers : Fin q → C) : Prop :=
  ∀ x, ∃ j : Fin q, covers (centers j) ((j.1 : ℝ) / q) x

/--
A normalized ranked cover of length `q₀` pads to every `q ≥ q₀`, provided coverage is
monotone in the radius. Existing centers are preserved at their padded ranks.
@isnad1 id=ex.3h7v.s6.f854b4f340a8 from=translated src=- shape=25ad000e vocab=4666060f
-/
theorem IsNormalizedRankedCover.pad [Nonempty C] {covers : C → ℝ → X → Prop}
    {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) {centers : Fin q₀ → C}
    (hcover : IsNormalizedRankedCover covers centers)
    (hmono : ∀ c x {r s : ℝ}, r ≤ s → covers c r x → covers c s x) :
    ∃ padded : Fin q → C,
      IsNormalizedRankedCover covers padded ∧
        ∀ j, padded (rankPaddingEmbedding q₀ q hq₀ hqq₀ j) = centers j := by
  classical
  let e := rankPaddingEmbedding q₀ q hq₀ hqq₀
  let padded : Fin q → C :=
    Function.extend e centers (fun _ ↦ Classical.choice (inferInstance : Nonempty C))
  have hpadded : ∀ j, padded (e j) = centers j := by
    intro j
    exact e.injective.extend_apply centers
      (fun _ ↦ Classical.choice (inferInstance : Nonempty C)) j
  refine ⟨padded, ?_, hpadded⟩
  intro x
  obtain ⟨j, hj⟩ := hcover x
  refine ⟨e j, ?_⟩
  rw [hpadded j]
  exact hmono _ _ (rankPaddingEmbedding_normalized_le hq₀ hqq₀ j) hj

end BurningPath
