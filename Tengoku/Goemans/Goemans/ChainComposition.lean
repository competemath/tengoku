/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Chain
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Composition and dummy-terminal closure for chain instances

This file formalizes Lemma 6.4 and Remark 6.5 of the paper.

The disjoint parallel union of two chains is not itself a chain.  Accordingly,
`Parallel` models its arcs by a sum of the two complete `Chain.Arc` types and
its routings by pairs of component routings.  Its loads and costs are inherited
literally from the two `Chain.Instance`s.

By contrast, `dummyEmbed` is a genuine larger `Chain.Instance`: it appends one
stage and adds one zero-cost terminal whose fractional cheap amount is zero.
-/

namespace Goemans
namespace Chain

universe u v

noncomputable section

namespace Instance

variable {ι : Type u} {m : ℕ}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite set of admissible cheap-routing selections of a chain
instance.-/
def admissibleRoutings (I : Instance ι m) : Finset (Finset ι) :=
  by
    classical
    exact Finset.univ.filter I.Admissible

/--
@isnad1 id=iff.0h4v.s5.973cf8d7bddb from=translated src=- shape=2058aac5 vocab=5be6e137
-/
theorem mem_admissibleRoutings (I : Instance ι m) (S : Finset ι) :
    S ∈ I.admissibleRoutings ↔ I.Admissible S := by
  simp [admissibleRoutings]

/--
@isnad1 id=nonempty.0h3v.s4.cf79691d8ad6 from=translated src=- shape=ff79e3e1 vocab=635503b5
-/
theorem admissibleRoutings_nonempty (I : Instance ι m) :
    I.admissibleRoutings.Nonempty :=
  ⟨∅, I.mem_admissibleRoutings ∅ |>.2 I.admissible_empty⟩

private def admissibleCosts (I : Instance ι m) : Finset ℝ :=
  I.admissibleRoutings.image I.routingCost

private theorem admissibleCosts_nonempty (I : Instance ι m) :
    I.admissibleCosts.Nonempty :=
  I.admissibleRoutings_nonempty.image I.routingCost

/-- Minimum cost among all admissible unsplittable routings of a chain
instance.-/
def optimalRoutingCost (I : Instance ι m) : ℝ :=
  I.admissibleCosts.min' I.admissibleCosts_nonempty

/-- An optimal admissible routing exists.
@isnad1 id=ex.0h3v.s5.3a459dcf2cbf from=translated src=- shape=4bb1c5f0 vocab=a3f0bc0f
-/
theorem exists_optimalRouting (I : Instance ι m) :
    ∃ S : Finset ι,
      I.Admissible S ∧ I.routingCost S = I.optimalRoutingCost := by
  have hmem : I.optimalRoutingCost ∈ I.admissibleCosts :=
    Finset.min'_mem _ I.admissibleCosts_nonempty
  rcases Finset.mem_image.mp hmem with ⟨S, hS, hcost⟩
  exact ⟨S, (I.mem_admissibleRoutings S).1 hS, hcost⟩

/-- The optimum is no larger than the cost of any admissible routing.
@isnad1 id=le.1h4v.s5.03ec3fe1f3ef from=translated src=- shape=b9cebd24 vocab=3249f3e3
-/
theorem optimalRoutingCost_le (I : Instance ι m) {S : Finset ι}
    (hS : I.Admissible S) :
    I.optimalRoutingCost ≤ I.routingCost S := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨S, (I.mem_admissibleRoutings S).2 hS, rfl⟩

omit [Nonempty ι] in
/-- Every routing cost is nonnegative.
@isnad1 id=le.0h4v.s5.2e8a57423715 from=translated src=- shape=f13bb475 vocab=afddc100
-/
theorem routingCost_nonneg (I : Instance ι m) (S : Finset ι) :
    0 ≤ I.routingCost S := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (I.c_nonneg i) (I.d_pos i).le

/-- The minimum admissible routing cost is nonnegative.
@isnad1 id=le.0h3v.s5.d9b803b2a80c from=translated src=- shape=04f7d038 vocab=f6032248
-/
theorem optimalRoutingCost_nonneg (I : Instance ι m) :
    0 ≤ I.optimalRoutingCost := by
  obtain ⟨S, _, hcost⟩ := I.exists_optimalRouting
  rw [← hcost]
  exact I.routingCost_nonneg S

/-- The optimum-to-fractional-cost ratio.  Results using this definition state
fractional-cost positivity explicitly.-/
def ratio (I : Instance ι m) : ℝ :=
  I.optimalRoutingCost / I.fractionalCost

end Instance

namespace Parallel

variable {ι : Type u} {κ : Type v} {m n : ℕ}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Complete arc type of the disjoint parallel union.-/
abbrev Arc (ι : Type u) (κ : Type v) (m n : ℕ) :=
  Chain.Arc ι m ⊕ Chain.Arc κ n

/-- A routing of the disjoint union is exactly one routing in each component.-/
abbrev Routing (ι : Type u) (κ : Type v) :=
  Finset ι × Finset κ

/-- The maximum demand in the disjoint union.-/
def dmax (I : Instance ι m) (J : Instance κ n) : ℝ :=
  max I.dmax J.dmax

/-- Demand of a terminal in the disjoint union.-/
def demand (I : Instance ι m) (J : Instance κ n) : ι ⊕ κ → ℝ
  | .inl i => I.d i
  | .inr j => J.d j

omit [DecidableEq ι] [DecidableEq κ] in
/-- Every union demand is at most the stated union maximum.
@isnad1 id=le.0h7v.s5.4133144b7822 from=translated src=- shape=9d71b251 vocab=df41e4c8
-/
theorem demand_le_dmax (I : Instance ι m) (J : Instance κ n)
    (q : ι ⊕ κ) :
    demand I J q ≤ dmax I J := by
  rcases q with i | j
  · exact le_trans (I.d_le_dmax i) (le_max_left _ _)
  · exact le_trans (J.d_le_dmax j) (le_max_right _ _)

omit [DecidableEq ι] [DecidableEq κ] in
/-- `dmax` is not merely an allowance chosen for the proof: it is exactly the
maximum demand over the sum-tagged terminal type of the disjoint union.
@isnad1 id=eq.0h6v.s6.eb9801e69a70 from=translated src=- shape=592dd02c vocab=c9fdaa0c
-/
theorem dmax_eq_sup_demand (I : Instance ι m) (J : Instance κ n) :
    dmax I J =
      Finset.univ.sup' Finset.univ_nonempty (demand I J) := by
  apply le_antisymm
  · apply max_le
    · change
        Finset.univ.sup' Finset.univ_nonempty I.d ≤
          Finset.univ.sup' Finset.univ_nonempty (demand I J)
      apply Finset.sup'_le Finset.univ_nonempty
      intro i _
      exact Finset.le_sup' (demand I J) (Finset.mem_univ (Sum.inl i))
    · change
        Finset.univ.sup' Finset.univ_nonempty J.d ≤
          Finset.univ.sup' Finset.univ_nonempty (demand I J)
      apply Finset.sup'_le Finset.univ_nonempty
      intro j _
      exact Finset.le_sup' (demand I J) (Finset.mem_univ (Sum.inr j))
  · apply Finset.sup'_le Finset.univ_nonempty
    intro q _
    exact demand_le_dmax I J q

/-- Fractional load on a union arc.-/
def x (I : Instance ι m) (J : Instance κ n) : Arc ι κ m n → ℝ
  | .inl a => I.x a
  | .inr a => J.x a

/-- Unsplittable load on a union arc.-/
def load (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) : Arc ι κ m n → ℝ
  | .inl a => I.load R.1 a
  | .inr a => J.load R.2 a

/-- Cost on a union arc.-/
def arcCost (I : Instance ι m) (J : Instance κ n) :
    Arc ι κ m n → ℝ
  | .inl a => I.arcCost a
  | .inr a => J.arcCost a

/-- Fractional cost of the disjoint union.-/
def fractionalCost (I : Instance ι m) (J : Instance κ n) : ℝ :=
  I.fractionalCost + J.fractionalCost

/-- Cost of a paired unsplittable routing.-/
def routingCost (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) : ℝ :=
  I.routingCost R.1 + J.routingCost R.2

/-- Full-arc admissibility in the disjoint union, using the maximum demand
across both components.-/
def Admissible (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) : Prop :=
  ∀ a, load I J R a ≤ x I J a + dmax I J

omit [DecidableEq ι] [Nonempty ι] [DecidableEq κ] [Nonempty κ] in
/-- The componentwise definitions are literal ordinary arc-cost sums.
@isnad1 id=eq.0h6v.s6.9829548ed423 from=translated src=- shape=c1633365 vocab=3b3451d3
-/
theorem fractionalCost_eq_sum_arc (I : Instance ι m) (J : Instance κ n) :
    fractionalCost I J =
      ∑ a : Arc ι κ m n, arcCost I J a * x I J a := by
  rw [Fintype.sum_sum_type]
  simp only [fractionalCost, arcCost, x]
  rw [← I.fractionalCost_eq_sum_arc, ← J.fractionalCost_eq_sum_arc]

omit [Nonempty ι] [Nonempty κ] in
/-- The paired routing cost is the literal ordinary cost sum on union arcs.
@isnad1 id=eq.0h7v.s6.0db5dbdca388 from=translated src=- shape=20b55647 vocab=b6b8ee17
-/
theorem routingCost_eq_sum_arc (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) :
    routingCost I J R =
      ∑ a : Arc ι κ m n, arcCost I J a * load I J R a := by
  rw [Fintype.sum_sum_type]
  simp only [routingCost, arcCost, load]
  rw [← I.routingCost_eq_sum_arc, ← J.routingCost_eq_sum_arc]

/-- Union admissibility is exactly the pair of component arc inequalities at
the common union allowance.
@isnad1 id=iff.0h7v.s7.bc9aaf3f89ab from=translated src=- shape=2ed538ee vocab=6485d227
-/
theorem admissible_iff (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) :
    Admissible I J R ↔
      (∀ a, I.load R.1 a ≤ I.x a + dmax I J) ∧
      (∀ a, J.load R.2 a ≤ J.x a + dmax I J) := by
  constructor
  · intro h
    exact ⟨fun a => h (.inl a), fun a => h (.inr a)⟩
  · rintro ⟨hI, hJ⟩ (a | a)
    · exact hI a
    · exact hJ a

/-- Native-admissible component routings combine into a union-admissible
routing because the union allowance dominates both component allowances.
@isnad1 id=admissib.2h8v.s6.4e97c7d38c02 from=translated src=- shape=6245456e vocab=ab871016
-/
theorem admissible_of_components (I : Instance ι m) (J : Instance κ n)
    {S : Finset ι} {T : Finset κ}
    (hS : I.Admissible S) (hT : J.Admissible T) :
    Admissible I J (S, T) := by
  rw [admissible_iff]
  constructor
  · intro a
    have hmax := le_max_left I.dmax J.dmax
    simp only [dmax]
    linarith [hS a]
  · intro a
    have hmax := le_max_right I.dmax J.dmax
    simp only [dmax]
    linarith [hT a]

/-- Admissible routings of the disjoint union.-/
def admissibleRoutings (I : Instance ι m) (J : Instance κ n) :
    Finset (Routing ι κ) :=
  by
    classical
    exact Finset.univ.filter (Admissible I J)

/--
@isnad1 id=iff.0h7v.s6.c7e457dd96f3 from=translated src=- shape=e6dece11 vocab=b9756003
-/
theorem mem_admissibleRoutings (I : Instance ι m) (J : Instance κ n)
    (R : Routing ι κ) :
    R ∈ admissibleRoutings I J ↔ Admissible I J R := by
  simp [admissibleRoutings]

/--
@isnad1 id=nonempty.0h6v.s5.f1eddc021d44 from=translated src=- shape=9d173651 vocab=f7840257
-/
theorem admissibleRoutings_nonempty (I : Instance ι m) (J : Instance κ n) :
    (admissibleRoutings I J).Nonempty :=
  ⟨(∅, ∅), (mem_admissibleRoutings I J _).2
    (admissible_of_components I J I.admissible_empty J.admissible_empty)⟩

private def admissibleCosts (I : Instance ι m) (J : Instance κ n) :
    Finset ℝ :=
  (admissibleRoutings I J).image (routingCost I J)

private theorem admissibleCosts_nonempty
    (I : Instance ι m) (J : Instance κ n) :
    (admissibleCosts I J).Nonempty :=
  (admissibleRoutings_nonempty I J).image (routingCost I J)

/-- Minimum admissible routing cost of the disjoint union.-/
def optimalRoutingCost (I : Instance ι m) (J : Instance κ n) : ℝ :=
  (admissibleCosts I J).min' (admissibleCosts_nonempty I J)

/-- The union optimum is no larger than any exhibited admissible paired
routing.
@isnad1 id=le.1h7v.s6.5f02916232d1 from=translated src=- shape=2423f506 vocab=f4baee7a
-/
theorem optimalRoutingCost_le (I : Instance ι m) (J : Instance κ n)
    {R : Routing ι κ} (hR : Admissible I J R) :
    optimalRoutingCost I J ≤ routingCost I J R := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨R, (mem_admissibleRoutings I J R).2 hR, rfl⟩

/-- Combining native optimal component routings proves the numerator bound in
Lemma 6.4.
@isnad1 id=le.0h6v.s6.e7a48ad50a8c from=translated src=- shape=943bbac3 vocab=6810e691
-/
theorem optimalRoutingCost_le_add (I : Instance ι m) (J : Instance κ n) :
    optimalRoutingCost I J ≤ I.optimalRoutingCost + J.optimalRoutingCost := by
  obtain ⟨S, hS, hScost⟩ := I.exists_optimalRouting
  obtain ⟨T, hT, hTcost⟩ := J.exists_optimalRouting
  calc
    optimalRoutingCost I J ≤ routingCost I J (S, T) :=
      optimalRoutingCost_le I J (admissible_of_components I J hS hT)
    _ = I.optimalRoutingCost + J.optimalRoutingCost := by
      simp only [routingCost, hScost, hTcost]

/-- Positive-denominator mediant inequality.
@isnad1 id=le.2h4v.s6.72e5a20920a6 from=translated src=- shape=67fcc7b6 vocab=1fc97192
-/
theorem add_div_add_le_max_div {U₁ U₂ F₁ F₂ : ℝ}
    (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) :
    (U₁ + U₂) / (F₁ + F₂) ≤ max (U₁ / F₁) (U₂ / F₂) := by
  have h₁ : U₁ ≤ max (U₁ / F₁) (U₂ / F₂) * F₁ :=
    (div_le_iff₀ hF₁).1 (le_max_left _ _)
  have h₂ : U₂ ≤ max (U₁ / F₁) (U₂ / F₂) * F₂ :=
    (div_le_iff₀ hF₂).1 (le_max_right _ _)
  rw [div_le_iff₀ (add_pos hF₁ hF₂)]
  nlinarith

/-- Ratio of the disjoint parallel union.-/
def ratio (I : Instance ι m) (J : Instance κ n) : ℝ :=
  optimalRoutingCost I J / fractionalCost I J

/-- **Lemma 6.4 (parallel composition never helps).** For two positive-cost
chain instances placed in disjoint parallel components, the union ratio is at
most the larger component ratio.
@isnad1 id=le.2h6v.s6.0414c1e2578a from=translated src=- shape=efdbd648 vocab=e034b4e4
-/
theorem ratio_le_max (I : Instance ι m) (J : Instance κ n)
    (hI : 0 < I.fractionalCost) (hJ : 0 < J.fractionalCost) :
    ratio I J ≤ max I.ratio J.ratio := by
  have hsum : 0 < fractionalCost I J := add_pos hI hJ
  calc
    ratio I J ≤
        (I.optimalRoutingCost + J.optimalRoutingCost) /
          fractionalCost I J := by
      rw [ratio]
      exact (div_le_div_iff_of_pos_right hsum).2
        (optimalRoutingCost_le_add I J)
    _ ≤ max I.ratio J.ratio := by
      exact add_div_add_le_max_div hI hJ

end Parallel

namespace Instance

variable {ι : Type u} {m : ℕ}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Embed the old terminals into a terminal type with one fresh dummy.-/
private abbrev oldEmbedding : ι ↪ ι ⊕ PUnit :=
  Function.Embedding.inl

/-- Route the old selection as before and route the fresh dummy expensively.-/
def liftRouting (S : Finset ι) : Finset (ι ⊕ PUnit) :=
  S.map oldEmbedding

/-- Restrict a routing of the enlarged instance to the old terminals.-/
def restrictRouting (T : Finset (ι ⊕ PUnit)) : Finset ι :=
  Finset.univ.filter fun i => Sum.inl i ∈ T

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/--
@isnad1 id=iff.0h3v.s5.3d5223c7e7b3 from=translated src=- shape=bee30d6a vocab=afe14add
-/
@[simp] theorem mem_liftRouting (S : Finset ι) (i : ι) :
    Sum.inl i ∈ liftRouting S ↔ i ∈ S := by
  simp [liftRouting, oldEmbedding]

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=not.0h2v.s5.c556cd00270d from=translated src=- shape=56be723c vocab=637b900e
-/
@[simp] theorem dummy_not_mem_liftRouting (S : Finset ι) :
    Sum.inr PUnit.unit ∉ liftRouting S := by
  simp [liftRouting, oldEmbedding]

omit [Nonempty ι] in
/--
@isnad1 id=iff.0h3v.s5.4285bc879d2d from=translated src=- shape=713729b4 vocab=5f539483
-/
@[simp] theorem mem_restrictRouting (T : Finset (ι ⊕ PUnit)) (i : ι) :
    i ∈ restrictRouting T ↔ Sum.inl i ∈ T := by
  simp [restrictRouting]

omit [Nonempty ι] in
/--
@isnad1 id=eq.0h2v.s4.048903e02110 from=translated src=- shape=e17ccb0b vocab=d7ff3d4f
-/
@[simp] theorem restrictRouting_liftRouting (S : Finset ι) :
    restrictRouting (liftRouting S) = S := by
  ext i
  simp

/-- **Remark 6.5, dummy-terminal construction.** Append one chain stage and
one positive-demand terminal.  Its expensive exit is at the old end, its cheap
peel is one stage later, its cheap fractional amount is zero, and its exit
cost is zero.-/
def dummyEmbed (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (_hδ_le : δ ≤ I.dmax) :
    Instance (ι ⊕ PUnit) (m + 1) where
  d
    | .inl i => I.d i
    | .inr _ => δ
  f
    | .inl i => I.f i
    | .inr _ => 0
  e
    | .inl i => (I.e i).castSucc
    | .inr _ => (Fin.last m).castSucc
  p
    | .inl i => (I.p i).castSucc
    | .inr _ => Fin.last (m + 1)
  c
    | .inl i => I.c i
    | .inr _ => 0
  d_pos
    | .inl i => I.d_pos i
    | .inr _ => hδ_pos
  f_nonneg
    | .inl i => I.f_nonneg i
    | .inr _ => le_rfl
  f_le_d
    | .inl i => I.f_le_d i
    | .inr _ => hδ_pos.le
  e_lt_p
    | .inl i => Fin.castSucc_lt_castSucc_iff.2 (I.e_lt_p i)
    | .inr _ => Fin.castSucc_lt_last (Fin.last m)
  c_nonneg
    | .inl i => I.c_nonneg i
    | .inr _ => le_rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s6.e9579c2db256 from=translated src=- shape=d50a782c vocab=67c49db2
-/
@[simp] theorem dummyEmbed_d_old (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (i : ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).d (.inl i) = I.d i :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h4v.s6.35008506e468 from=translated src=- shape=81c1b2c9 vocab=aaf89a88
-/
@[simp] theorem dummyEmbed_d_dummy (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).d (.inr PUnit.unit) = δ :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s6.ec2d2cabdccc from=translated src=- shape=d50a782c vocab=b5683419
-/
@[simp] theorem dummyEmbed_f_old (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (i : ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).f (.inl i) = I.f i :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h4v.s6.afc969b6fa8d from=translated src=- shape=dedf8411 vocab=f03d378d
-/
@[simp] theorem dummyEmbed_f_dummy (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).f (.inr PUnit.unit) = 0 :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s6.87c9e13e25c5 from=translated src=- shape=4f45244e vocab=70024c09
-/
@[simp] theorem dummyEmbed_e_old (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (i : ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).e (.inl i) = (I.e i).castSucc :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h4v.s6.93b732053c95 from=translated src=- shape=1314270d vocab=aa9398d4
-/
@[simp] theorem dummyEmbed_e_dummy (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).e (.inr PUnit.unit) =
      (Fin.last m).castSucc :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s6.c06b841cfabd from=translated src=- shape=4f45244e vocab=e7baa679
-/
@[simp] theorem dummyEmbed_p_old (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (i : ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).p (.inl i) = (I.p i).castSucc :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h4v.s6.13507d176e0f from=translated src=- shape=980be85f vocab=9957931c
-/
@[simp] theorem dummyEmbed_p_dummy (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).p (.inr PUnit.unit) =
      Fin.last (m + 1) :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h5v.s6.ccfb162c98d2 from=translated src=- shape=d50a782c vocab=94936cfb
-/
@[simp] theorem dummyEmbed_c_old (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (i : ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).c (.inl i) = I.c i :=
  rfl

omit [DecidableEq ι] in
/--
@isnad1 id=eq.2h4v.s6.1a1989785747 from=translated src=- shape=dedf8411 vocab=3e942e87
-/
@[simp] theorem dummyEmbed_c_dummy (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).c (.inr PUnit.unit) = 0 :=
  rfl

omit [DecidableEq ι] in
/-- The dummy demand does not change the maximum demand.
@isnad1 id=eq.2h4v.s6.cbd20c1295a5 from=translated src=- shape=240bf423 vocab=c1ddf4f6
-/
@[simp] theorem dummyEmbed_dmax (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).dmax = I.dmax := by
  let E := I.dummyEmbed δ hδ_pos hδ_le
  apply le_antisymm
  · change
      Finset.univ.sup' Finset.univ_nonempty E.d ≤ I.dmax
    apply Finset.sup'_le Finset.univ_nonempty
    intro q _
    rcases q with i | q
    · exact I.d_le_dmax i
    · exact hδ_le
  · change
      Finset.univ.sup' Finset.univ_nonempty I.d ≤ E.dmax
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    simpa [E] using E.d_le_dmax (Sum.inl i)

omit [DecidableEq ι] in
/-- The fresh zero-cost exit contributes nothing to fractional cost.
@isnad1 id=eq.2h4v.s6.b9e71b53efba from=translated src=- shape=ef2dd8b0 vocab=89e710b4
-/
@[simp] theorem dummyEmbed_fractionalCost (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).fractionalCost =
      I.fractionalCost := by
  rw [fractionalCost, Fintype.sum_sum_type]
  simp [fractionalCost]

/-- Lifting a routing and sending the dummy expensively preserves its cost.
@isnad1 id=eq.2h5v.s6.6f849596ba22 from=translated src=- shape=76076e3d vocab=16d6898e
-/
theorem dummyEmbed_routingCost_lift (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) (S : Finset ι) :
    (I.dummyEmbed δ hδ_pos hδ_le).routingCost (liftRouting S) =
      I.routingCost S := by
  rw [routingCost, Fintype.sum_sum_type]
  simp [routingCost]

/-- More generally, the enlarged routing cost depends only on its restriction
to the old terminals; the dummy costs zero on either path.
@isnad1 id=eq.2h5v.s6.a857d38ab1e4 from=translated src=- shape=aacc046c vocab=e82a3d1d
-/
@[simp] theorem dummyEmbed_routingCost_restrict (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax)
    (T : Finset (ι ⊕ PUnit)) :
    (I.dummyEmbed δ hδ_pos hδ_le).routingCost T =
      I.routingCost (restrictRouting T) := by
  rw [routingCost, Fintype.sum_sum_type]
  simp [routingCost]

omit [DecidableEq ι] in
/-- The appended stage carries no fractional load.
@isnad1 id=eq.2h4v.s6.bc5ab4af2d47 from=translated src=- shape=ad67aeb8 vocab=d22e8dd4
-/
@[simp] theorem dummyEmbed_stageX_last (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax) :
    (I.dummyEmbed δ hδ_pos hδ_le).stageX (Fin.last m) = 0 := by
  have hp (i : ι) : ¬ m < (I.p i).val :=
    not_lt.mpr (Nat.le_of_lt_succ (I.p i).isLt)
  have he (i : ι) : ¬ m < (I.e i).val :=
    not_lt.mpr (Nat.le_of_lt_succ (I.e i).isLt)
  rw [stageX, Fintype.sum_sum_type]
  simp [hp, he]

/-- On the appended stage only a cheaply routed dummy has load, namely its
demand `δ`.
@isnad1 id=eq.2h5v.s7.33aace4fc32b from=translated src=- shape=9886a54b vocab=3cb4121e
-/
@[simp] theorem dummyEmbed_stageLoad_last (I : Instance ι m) (δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ I.dmax)
    (T : Finset (ι ⊕ PUnit)) :
    (I.dummyEmbed δ hδ_pos hδ_le).stageLoad T (Fin.last m) =
      if Sum.inr PUnit.unit ∈ T then δ else 0 := by
  have hp (i : ι) : ¬ m < (I.p i).val :=
    not_lt.mpr (Nat.le_of_lt_succ (I.p i).isLt)
  have he (i : ι) : ¬ m < (I.e i).val :=
    not_lt.mpr (Nat.le_of_lt_succ (I.e i).isLt)
  rw [stageLoad, Fintype.sum_sum_type]
  simp [hp, he]

end Instance

/-- Ratios realized by positive-fractional-cost chain instances with exactly
`k` terminals.  Quantifying over finite terminal types makes the definition
invariant under relabeling.-/
def ratiosWithTerminalCount (k : ℕ) : Set ℝ :=
  {r | ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
      (_ : Nonempty ι) (m : ℕ) (I : Instance ι m),
      Fintype.card ι = k ∧ 0 < I.fractionalCost ∧ I.ratio = r}

end

end Chain
end Goemans
