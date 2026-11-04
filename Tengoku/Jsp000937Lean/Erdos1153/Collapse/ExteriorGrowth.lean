import Tengoku.Jsp000937Lean.Erdos1153.Collapse.ClusterLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Growth on exterior and bridge gaps

For a fixed point away from the cluster anchor and every fixed exterior node,
a clustered cardinal function has a nonzero continuous coefficient divided
by `δ^(d+1)`.  This file first proves that placement-independent fact, then
supplies explicit midpoint witnesses for left fixed gaps, the moving left
bridge, the moving right bridge, and right fixed gaps.

The full-block placement has no exterior gap and is excluded explicitly.
-/

namespace Erdos1153.Collapse

open Polynomial Set
open scoped BigOperators

noncomputable section

namespace Spec

variable {n d : ℕ} (spec : Spec n d)

/-- The nonzero pattern denominator of the `k`th clustered cardinal.-/
def clusterDenominator (k : Fin (d + 2)) : ℝ :=
  ∏ l ∈ Finset.univ.erase k, (spec.offset k - spec.offset l)

/--
@isnad1 id=ne.0h4v.s5.58f9ef5b44b6 from=translated src=- shape=5135f76a vocab=207200b8
-/
lemma clusterDenominator_ne_zero (k : Fin (d + 2)) :
    spec.clusterDenominator k ≠ 0 := by
  rw [clusterDenominator, Finset.prod_ne_zero_iff]
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  exact sub_ne_zero.mpr fun h => hlk (spec.offset_strictMono.injective h).symm

/-- Numerator contributed by the other clustered nodes at a fixed point.-/
def clusterNumerator (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∏ l ∈ Finset.univ.erase k, (x - spec.clusterPoint δ l)

/-- The coefficient left after extracting the pole `δ^-(d+1)`.-/
def blowupCoefficient (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  spec.exteriorRatio δ k x * spec.clusterNumerator δ k x /
    spec.clusterDenominator k

private lemma cluster_denominator_product (δ : ℝ) (k : Fin (d + 2)) :
    (∏ l ∈ Finset.univ.erase k,
      (spec.clusterPoint δ k - spec.clusterPoint δ l)) =
      δ ^ (d + 1) * spec.clusterDenominator k := by
  classical
  have hfactor (l : Fin (d + 2)) :
      spec.clusterPoint δ k - spec.clusterPoint δ l =
        δ * (spec.offset k - spec.offset l) := by
    simp only [clusterPoint]
    ring
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp [clusterDenominator]

private lemma clusterCardinal_eq_numerator_div (δ : ℝ)
    (k : Fin (d + 2)) (x : ℝ) :
    spec.clusterCardinal δ k x =
      spec.clusterNumerator δ k x /
        (δ ^ (d + 1) * spec.clusterDenominator k) := by
  unfold Spec.clusterCardinal Spec.clusterNumerator
  rw [Finset.prod_div_distrib, spec.cluster_denominator_product]

/-- Exact pole extraction for a clustered cardinal function at a fixed
physical point.
@isnad1 id=eq.0h6v.s6.005565cbdbf3 from=translated src=- shape=53e14752 vocab=41b4f973
-/
theorem fullCardinal_eq_blowupCoefficient_div_pow
    (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) :
    spec.fullCardinal δ k x =
      spec.blowupCoefficient δ k x / δ ^ (d + 1) := by
  rw [spec.fullCardinal_factorization]
  rw [spec.clusterCardinal_eq_numerator_div]
  unfold blowupCoefficient
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/--
@isnad1 id=continuo.0h5v.s5.ada49f111fc7 from=translated src=- shape=2562435f vocab=ebdf3464
-/
lemma continuousAt_exteriorRatio_zero (k : Fin (d + 2)) (x : ℝ) :
    ContinuousAt (fun δ => spec.exteriorRatio δ k x) 0 := by
  have hden : ContinuousAt
      (fun δ : ℝ => spec.exteriorPolynomial.eval (spec.clusterPoint δ k)) 0 :=
    spec.exteriorPolynomial.continuous.continuousAt.comp
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)))
  exact continuousAt_const.div hden (by
    simpa [clusterPoint] using spec.exteriorPolynomial_eval_anchor_ne_zero)

/--
@isnad1 id=continuo.0h5v.s5.00cb2aabfa2e from=translated src=- shape=2562435f vocab=b7b4efb8
-/
lemma continuousAt_clusterNumerator_zero (k : Fin (d + 2)) (x : ℝ) :
    ContinuousAt (fun δ => spec.clusterNumerator δ k x) 0 := by
  unfold clusterNumerator
  exact (continuous_finsetProd (Finset.univ.erase k) fun l hl =>
    continuous_const.sub
      (continuous_const.add (continuous_id.mul continuous_const))).continuousAt

/--
@isnad1 id=continuo.0h5v.s5.048a506841e2 from=translated src=- shape=2562435f vocab=85800586
-/
lemma continuousAt_blowupCoefficient_zero (k : Fin (d + 2)) (x : ℝ) :
    ContinuousAt (fun δ => spec.blowupCoefficient δ k x) 0 := by
  unfold blowupCoefficient
  exact ((spec.continuousAt_exteriorRatio_zero k x).mul
    (spec.continuousAt_clusterNumerator_zero k x)).div_const _

/--
@isnad1 id=ne.1h4v.s6.6a61e33a80db from=translated src=- shape=46fabad1 vocab=99719d8f
-/
lemma exteriorPolynomial_eval_ne_zero_of_away {x : ℝ}
    (hx : ∀ j ∈ spec.block.exterior, x ≠ spec.nodes.point j) :
    spec.exteriorPolynomial.eval x ≠ 0 := by
  rw [spec.exteriorPolynomial_eval, Finset.prod_ne_zero_iff]
  intro j hj
  exact sub_ne_zero.mpr (hx j hj)

/--
@isnad1 id=ne.1h5v.s5.86f96ebd1184 from=translated src=- shape=99ec1296 vocab=f59ffb90
-/
lemma clusterNumerator_zero_ne_zero (k : Fin (d + 2)) {x : ℝ}
    (hx : x ≠ spec.anchor) :
    spec.clusterNumerator 0 k x ≠ 0 := by
  rw [clusterNumerator, Finset.prod_ne_zero_iff]
  intro l hl
  simpa only [clusterPoint, zero_mul, add_zero, sub_ne_zero] using hx

/--
@isnad1 id=ne.2h5v.s6.7b779d745a99 from=translated src=- shape=500a61fa vocab=6ae09092
-/
lemma blowupCoefficient_zero_ne_zero (k : Fin (d + 2)) {x : ℝ}
    (hxanchor : x ≠ spec.anchor)
    (hxext : ∀ j ∈ spec.block.exterior, x ≠ spec.nodes.point j) :
    spec.blowupCoefficient 0 k x ≠ 0 := by
  unfold blowupCoefficient exteriorRatio
  apply div_ne_zero
  · apply mul_ne_zero
    · exact div_ne_zero (spec.exteriorPolynomial_eval_ne_zero_of_away hxext)
        (by simpa [clusterPoint] using spec.exteriorPolynomial_eval_anchor_ne_zero)
    · exact spec.clusterNumerator_zero_ne_zero k hxanchor
  · exact spec.clusterDenominator_ne_zero k

/-- A continuous nonzero coefficient divided by a positive power eventually
exceeds every prescribed finite bound in absolute value.-/
private theorem eventually_abs_div_pow_gt
    (f : ℝ → ℝ) (m : ℕ) (hm : 0 < m)
    (hf : ContinuousAt f 0) (hf0 : f 0 ≠ 0) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      A < |f δ / δ ^ m| := by
  let c := |f 0| / 2
  have hc : 0 < c := div_pos (abs_pos.mpr hf0) (by norm_num)
  obtain ⟨η₁, hη₁, hfnear⟩ :=
    (Metric.continuousAt_iff.mp hf) c hc
  let B := max A 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right A 0]
  have hq : 0 < c / B := div_pos hc hB
  have hpowcont : ContinuousAt (fun δ : ℝ => δ ^ m) 0 := continuousAt_id.pow m
  obtain ⟨η₂, hη₂, hpownear⟩ :=
    (Metric.continuousAt_iff.mp hpowcont) (c / B) hq
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  intro δ hδ hδη
  have hδη₁ : dist δ 0 < η₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact hδη.trans_le (min_le_left _ _)
  have hδη₂ : dist δ 0 < η₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact hδη.trans_le (min_le_right _ _)
  have hfclose := hfnear hδη₁
  rw [Real.dist_eq] at hfclose
  have hflower : c < |f δ| := by
    have hrev := abs_sub_abs_le_abs_sub (f 0) (f δ)
    have : |f 0| - |f δ| < c := hrev.trans_lt (by simpa [abs_sub_comm] using hfclose)
    dsimp only [c] at this ⊢
    linarith
  have hpclose := hpownear hδη₂
  rw [Real.dist_eq, zero_pow hm.ne', sub_zero,
    abs_of_pos (pow_pos hδ m)] at hpclose
  have hBpow : B * δ ^ m < c := by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp hpclose
  have hApow : A * δ ^ m < |f δ| :=
    (mul_le_mul_of_nonneg_right
      (show A ≤ B by dsimp [B]; linarith [le_max_left A 0])
      (pow_pos hδ m).le).trans_lt (hBpow.trans hflower)
  rw [abs_div, abs_of_pos (pow_pos hδ m), lt_div_iff₀ (pow_pos hδ m)]
  exact hApow

/-- Placement-independent exterior growth at a fixed point separated from
the limiting cluster and all fixed nodes.
@isnad1 id=ex.2h6v.s7.4b4ff34de47b from=translated src=- shape=58103c03 vocab=0be66125
-/
theorem eventually_abs_fullCardinal_gt
    (k : Fin (d + 2)) {x : ℝ}
    (hxanchor : x ≠ spec.anchor)
    (hxext : ∀ j ∈ spec.block.exterior, x ≠ spec.nodes.point j)
    (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      A < |spec.fullCardinal δ k x| := by
  obtain ⟨η, hη, hbound⟩ := eventually_abs_div_pow_gt
    (fun δ => spec.blowupCoefficient δ k x) (d + 1) (by omega)
    (spec.continuousAt_blowupCoefficient_zero k x)
    (spec.blowupCoefficient_zero_ne_zero k hxanchor hxext) A
  exact ⟨η, hη, fun δ hδ hδη => by
    rw [spec.fullCardinal_eq_blowupCoefficient_div_pow]
    exact hbound δ hδ hδη⟩

/-- The four kinds of noncluster gap.  The bridge kinds are kept separate
because one of their endpoints moves with `δ`.-/
inductive ExteriorGapKind where
  | leftFixed
  | leftBridge
  | rightBridge
  | rightFixed
  deriving DecidableEq

/-- Index conditions defining the four exterior-gap kinds.-/
def ExteriorGapKind.Valid (kind : ExteriorGapKind) (g : Fin (n - 1)) : Prop :=
  match kind with
  | .leftFixed => g.val + 1 < spec.block.start
  | .leftBridge => g.val + 1 = spec.block.start
  | .rightBridge => g.val = spec.block.start + d + 1
  | .rightFixed => spec.block.start + d + 1 < g.val

/-- A gap is external to the `d+1` internal cluster gaps.-/
def IsExteriorGap (g : Fin (n - 1)) : Prop :=
  g.val < spec.block.start ∨ spec.block.start + d + 1 ≤ g.val

/--
@isnad1 id=or.1h4v.s5.afcb7fab1372 from=translated src=- shape=221856ab vocab=ba6f81c3
-/
lemma exteriorGapKind_classification (g : Fin (n - 1))
    (hg : spec.IsExteriorGap g) :
    (ExteriorGapKind.leftFixed.Valid spec g) ∨
      (ExteriorGapKind.leftBridge.Valid spec g) ∨
      (ExteriorGapKind.rightBridge.Valid spec g) ∨
      (ExteriorGapKind.rightFixed.Valid spec g) := by
  change (g.val + 1 < spec.block.start) ∨
    (g.val + 1 = spec.block.start) ∨
    (g.val = spec.block.start + d + 1) ∨
    (spec.block.start + d + 1 < g.val)
  change g.val < spec.block.start ∨ spec.block.start + d + 1 ≤ g.val at hg
  rcases hg with hgleft | hgright
  · by_cases hbridge : g.val + 1 = spec.block.start
    · exact Or.inr (Or.inl hbridge)
    · exact Or.inl (by omega)
  · by_cases hbridge : g.val = spec.block.start + d + 1
    · exact Or.inr (Or.inr (Or.inl hbridge))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- A full block has no exterior or bridge gap.
@isnad1 id=not.1h4v.s5.c356773473b6 from=translated src=- shape=2f90c090 vocab=9472b100
-/
lemma not_isExteriorGap_of_full (hfull : spec.placement = .full)
    (g : Fin (n - 1)) : ¬ spec.IsExteriorGap g := by
  have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 = n := by
    simpa [Placement.Valid, hfull, Nat.add_assoc] using spec.placement_valid
  intro hg
  rcases hg with hg | hg
  · omega
  · have hglt := g.isLt
    omega

/-- Arithmetic midpoint.-/
def midpoint (u v : ℝ) : ℝ := (u + v) / 2

/--
@isnad1 id=mem.1h2v.s4.882a34a70ddc from=translated src=- shape=4c4349f8 vocab=c1c7e4da
-/
lemma midpoint_mem_Ioo {u v : ℝ} (huv : u < v) :
    midpoint u v ∈ Set.Ioo u v := by
  constructor <;> unfold midpoint <;> linarith

/-- Midpoint of an original fixed nodal gap.-/
def fixedGapWitness (g : Fin (n - 1)) : ℝ :=
  midpoint (spec.nodes.point (gapLeftIndex g))
    (spec.nodes.point (gapRightIndex g))

/-- Midpoint of the limiting left bridge.-/
def leftBridgeWitness (g : Fin (n - 1)) : ℝ :=
  midpoint (spec.nodes.point (gapLeftIndex g)) spec.anchor

/-- Midpoint of the limiting right bridge.-/
def rightBridgeWitness (g : Fin (n - 1)) : ℝ :=
  midpoint spec.anchor (spec.nodes.point (gapRightIndex g))

/--
@isnad1 id=mem.0h4v.s5.40f40efbf748 from=translated src=- shape=4bfd5e61 vocab=ff3701f9
-/
lemma fixedGapWitness_mem_original_openGap (g : Fin (n - 1)) :
    spec.fixedGapWitness g ∈ openGap spec.nodes g :=
  midpoint_mem_Ioo (gap_left_lt_right spec.nodes g)

/-- No original node can equal the midpoint of one original nodal gap.
@isnad1 id=ne.0h5v.s5.64586b732f95 from=translated src=- shape=ca49eac0 vocab=c94afe7b
-/
lemma fixedGapWitness_ne_node (g : Fin (n - 1)) (j : Fin n) :
    spec.fixedGapWitness g ≠ spec.nodes.point j := by
  have hw := spec.fixedGapWitness_mem_original_openGap g
  change spec.nodes.point (gapLeftIndex g) < spec.fixedGapWitness g ∧
    spec.fixedGapWitness g < spec.nodes.point (gapRightIndex g) at hw
  intro heq
  by_cases hj : j.val ≤ g.val
  · have hnode : spec.nodes.point j ≤ spec.nodes.point (gapLeftIndex g) :=
      spec.nodes.strictMono.monotone (by
        simpa only [Fin.le_iff_val_le_val, gapLeftIndex_val] using hj)
    rw [heq] at hw
    linarith
  · have hj' : g.val + 1 ≤ j.val := by omega
    have hnode : spec.nodes.point (gapRightIndex g) ≤ spec.nodes.point j :=
      spec.nodes.strictMono.monotone (by
        simpa only [Fin.le_iff_val_le_val, gapRightIndex_val] using hj')
    rw [heq] at hw
    linarith

/--
@isnad1 id=ne.0h4v.s5.44b393d7b655 from=translated src=- shape=a54ca0a1 vocab=e664f094
-/
lemma fixedGapWitness_ne_anchor (g : Fin (n - 1)) :
    spec.fixedGapWitness g ≠ spec.anchor := by
  cases hp : spec.placement
  · simpa [anchor, hp] using spec.fixedGapWitness_ne_node g spec.firstIndex
  · simpa [anchor, hp] using spec.fixedGapWitness_ne_node g spec.firstIndex
  · simpa [anchor, hp] using spec.fixedGapWitness_ne_node g spec.lastIndex
  · simpa [anchor, hp] using spec.fixedGapWitness_ne_node g spec.firstIndex

/--
@isnad1 id=ne.1h5v.s6.0b227da68cc1 from=translated src=- shape=9315d6e1 vocab=dda89f3f
-/
lemma fixedGapWitness_away_exterior (g : Fin (n - 1)) :
    ∀ j ∈ spec.block.exterior,
      spec.fixedGapWitness g ≠ spec.nodes.point j :=
  fun j _ => spec.fixedGapWitness_ne_node g j

/--
@isnad1 id=mem.2h5v.s5.9eb6681d2d9e from=translated src=- shape=37c0b407 vocab=68b7da85
-/
lemma fixedGapWitness_mem_closedGap_of_leftFixed
    {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftFixed.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ) :
    spec.fixedGapWitness g ∈ closedGap (spec.orderedNodes δ hδ) g := by
  have hleft : ¬ spec.block.Mem (gapLeftIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapLeftIndex_val]
    change g.val + 1 < spec.block.start at hg
    omega
  have hright : ¬ spec.block.Mem (gapRightIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapRightIndex_val]
    change g.val + 1 < spec.block.start at hg
    omega
  have hw := spec.fixedGapWitness_mem_original_openGap g
  change spec.nodes.point (gapLeftIndex g) < spec.fixedGapWitness g ∧
    spec.fixedGapWitness g < spec.nodes.point (gapRightIndex g) at hw
  change spec.point δ (gapLeftIndex g) ≤ spec.fixedGapWitness g ∧
    spec.fixedGapWitness g ≤ spec.point δ (gapRightIndex g)
  rw [spec.point_of_not_mem δ hleft, spec.point_of_not_mem δ hright]
  exact ⟨hw.1.le, hw.2.le⟩

/--
@isnad1 id=mem.2h5v.s5.fea39df1be85 from=translated src=- shape=37c0b407 vocab=4d7b72c3
-/
lemma fixedGapWitness_mem_closedGap_of_rightFixed
    {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightFixed.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ) :
    spec.fixedGapWitness g ∈ closedGap (spec.orderedNodes δ hδ) g := by
  have hleft : ¬ spec.block.Mem (gapLeftIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapLeftIndex_val]
    change spec.block.start + d + 1 < g.val at hg
    omega
  have hright : ¬ spec.block.Mem (gapRightIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapRightIndex_val]
    change spec.block.start + d + 1 < g.val at hg
    omega
  have hw := spec.fixedGapWitness_mem_original_openGap g
  change spec.nodes.point (gapLeftIndex g) < spec.fixedGapWitness g ∧
    spec.fixedGapWitness g < spec.nodes.point (gapRightIndex g) at hw
  change spec.point δ (gapLeftIndex g) ≤ spec.fixedGapWitness g ∧
    spec.fixedGapWitness g ≤ spec.point δ (gapRightIndex g)
  rw [spec.point_of_not_mem δ hleft, spec.point_of_not_mem δ hright]
  exact ⟨hw.1.le, hw.2.le⟩

/--
@isnad1 id=lt.1h4v.s5.38c19cfe3020 from=translated src=- shape=569134cd vocab=29fa2437
-/
lemma leftBridge_left_lt_anchor {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g) :
    spec.nodes.point (gapLeftIndex g) < spec.anchor := by
  change g.val + 1 = spec.block.start at hg
  cases hp : spec.placement
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).1
    omega
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .leftEndpoint spec.block by
        simpa [hp] using spec.placement_valid).1
    omega
  · rw [anchor, hp]
    exact spec.nodes.strictMono (by
      simp only [Fin.lt_def, gapLeftIndex_val, spec.lastIndex_val]
      omega)
  · rw [anchor, hp]
    exact spec.nodes.strictMono (by
      simp only [Fin.lt_def, gapLeftIndex_val, spec.firstIndex_val]
      omega)

/--
@isnad1 id=lt.1h4v.s5.9af7c89cfc16 from=translated src=- shape=7d24a683 vocab=d1fb95b9
-/
lemma anchor_lt_rightBridge_right {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g) :
    spec.anchor < spec.nodes.point (gapRightIndex g) := by
  change g.val = spec.block.start + d + 1 at hg
  cases hp : spec.placement
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).2
    have := g.isLt
    omega
  · rw [anchor, hp]
    exact spec.nodes.strictMono (by
      simp only [Fin.lt_def, spec.firstIndex_val, gapRightIndex_val]
      omega)
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .rightEndpoint spec.block by
        simpa [hp] using spec.placement_valid).2
    have := g.isLt
    omega
  · rw [anchor, hp]
    exact spec.nodes.strictMono (by
      simp only [Fin.lt_def, spec.firstIndex_val, gapRightIndex_val]
      omega)

/-- Half the limiting left-bridge length.-/
def leftBridgeRadius (g : Fin (n - 1)) : ℝ :=
  (spec.anchor - spec.nodes.point (gapLeftIndex g)) / 2

/--
@isnad1 id=lt.1h4v.s5.6eca468f936c from=translated src=- shape=04ec395a vocab=c62a7297
-/
lemma leftBridgeRadius_pos {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g) :
    0 < spec.leftBridgeRadius g := by
  unfold leftBridgeRadius
  exact div_pos (sub_pos.mpr (spec.leftBridge_left_lt_anchor hg)) (by norm_num)

/-- Half the limiting right-bridge length.-/
def rightBridgeRadius (g : Fin (n - 1)) : ℝ :=
  (spec.nodes.point (gapRightIndex g) - spec.anchor) / 2

/--
@isnad1 id=lt.1h4v.s5.85ebf660cd38 from=translated src=- shape=04ec395a vocab=6c3fd8c8
-/
lemma rightBridgeRadius_pos {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g) :
    0 < spec.rightBridgeRadius g := by
  unfold rightBridgeRadius
  exact div_pos (sub_pos.mpr (spec.anchor_lt_rightBridge_right hg)) (by norm_num)

/--
@isnad1 id=eq.1h4v.s5.ca1c391c4577 from=translated src=- shape=270ec243 vocab=6e391edb
-/
lemma gapRightIndex_eq_firstIndex_of_leftBridge {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g) :
    gapRightIndex g = spec.firstIndex := by
  apply Fin.ext
  simp only [gapRightIndex_val, spec.firstIndex_val]
  exact hg

/--
@isnad1 id=eq.1h4v.s5.450c9bdc812c from=translated src=- shape=270ec243 vocab=c602be25
-/
lemma gapLeftIndex_eq_lastIndex_of_rightBridge {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g) :
    gapLeftIndex g = spec.lastIndex := by
  apply Fin.ext
  simp only [gapLeftIndex_val, spec.lastIndex_val]
  exact hg

/-- At scales below half the limiting bridge length, the fixed midpoint is
still inside the moving left bridge.
@isnad1 id=mem.3h5v.s6.7d401760a07e from=translated src=- shape=b9233175 vocab=bf753e35
-/
lemma leftBridgeWitness_mem_openGap {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ)
    (hsmall : δ < spec.leftBridgeRadius g) :
    spec.leftBridgeWitness g ∈ openGap (spec.orderedNodes δ hδ) g := by
  have hleft : ¬ spec.block.Mem (gapLeftIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapLeftIndex_val]
    change g.val + 1 = spec.block.start at hg
    omega
  change spec.point δ (gapLeftIndex g) < spec.leftBridgeWitness g ∧
    spec.leftBridgeWitness g < spec.point δ (gapRightIndex g)
  rw [spec.point_of_not_mem δ hleft,
    spec.gapRightIndex_eq_firstIndex_of_leftBridge hg]
  have hmid := midpoint_mem_Ioo (spec.leftBridge_left_lt_anchor hg)
  change spec.nodes.point (gapLeftIndex g) < spec.leftBridgeWitness g ∧
    spec.leftBridgeWitness g < spec.anchor at hmid
  refine ⟨hmid.1, ?_⟩
  cases hp : spec.placement
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).1
    change g.val + 1 = spec.block.start at hg
    omega
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .leftEndpoint spec.block by
        simpa [hp] using spec.placement_valid).1
    change g.val + 1 = spec.block.start at hg
    omega
  · rw [show spec.firstIndex = spec.block.index spec.localLeft by rfl,
      spec.point_index]
    rw [clusterPoint, spec.offset_localLeft, ite_eq_left hp]
    unfold leftBridgeRadius at hsmall
    unfold leftBridgeWitness midpoint
    linarith
  · rw [spec.first_point_fixed_of_not_right δ (by simp [hp])]
    simpa [anchor, hp] using hmid.2

/--
@isnad1 id=mem.3h5v.s6.7f60fbee7428 from=translated src=- shape=b9233175 vocab=b2390be8
-/
lemma leftBridgeWitness_mem_closedGap {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ)
    (hsmall : δ < spec.leftBridgeRadius g) :
    spec.leftBridgeWitness g ∈ closedGap (spec.orderedNodes δ hδ) g :=
  let hw := spec.leftBridgeWitness_mem_openGap hg δ hδ hsmall
  ⟨hw.1.le, hw.2.le⟩

/-- At scales below half the limiting bridge length, the fixed midpoint is
still inside the moving right bridge.
@isnad1 id=mem.3h5v.s6.11c4c56c76b0 from=translated src=- shape=b9233175 vocab=6dd2467a
-/
lemma rightBridgeWitness_mem_openGap {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ)
    (hsmall : δ < spec.rightBridgeRadius g) :
    spec.rightBridgeWitness g ∈ openGap (spec.orderedNodes δ hδ) g := by
  have hright : ¬ spec.block.Mem (gapRightIndex g) := by
    simp only [ConsecutiveBlock.Mem, gapRightIndex_val]
    change g.val = spec.block.start + d + 1 at hg
    omega
  change spec.point δ (gapLeftIndex g) < spec.rightBridgeWitness g ∧
    spec.rightBridgeWitness g < spec.point δ (gapRightIndex g)
  rw [spec.point_of_not_mem δ hright,
    spec.gapLeftIndex_eq_lastIndex_of_rightBridge hg]
  have hmid := midpoint_mem_Ioo (spec.anchor_lt_rightBridge_right hg)
  change spec.anchor < spec.rightBridgeWitness g ∧
    spec.rightBridgeWitness g < spec.nodes.point (gapRightIndex g) at hmid
  refine ⟨?_, hmid.2⟩
  cases hp : spec.placement
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).2
    change g.val = spec.block.start + d + 1 at hg
    have := g.isLt
    omega
  · rw [show spec.lastIndex = spec.block.index spec.localRight by rfl,
      spec.point_index]
    rw [clusterPoint, spec.offset_localRight, ite_eq_right (by simp [hp])]
    unfold rightBridgeRadius at hsmall
    unfold rightBridgeWitness midpoint
    linarith
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .rightEndpoint spec.block by
        simpa [hp] using spec.placement_valid).2
    change g.val = spec.block.start + d + 1 at hg
    have := g.isLt
    omega
  · rw [show spec.lastIndex = spec.block.index spec.localRight by rfl,
      spec.point_index]
    rw [clusterPoint, spec.offset_localRight, ite_eq_right (by simp [hp])]
    unfold rightBridgeRadius at hsmall
    unfold rightBridgeWitness midpoint
    linarith

/--
@isnad1 id=mem.3h5v.s6.b0cec0af810a from=translated src=- shape=b9233175 vocab=a7ea371b
-/
lemma rightBridgeWitness_mem_closedGap {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g)
    (δ : ℝ) (hδ : spec.Admissible δ)
    (hsmall : δ < spec.rightBridgeRadius g) :
    spec.rightBridgeWitness g ∈ closedGap (spec.orderedNodes δ hδ) g :=
  let hw := spec.rightBridgeWitness_mem_openGap hg δ hδ hsmall
  ⟨hw.1.le, hw.2.le⟩

/--
@isnad1 id=ne.1h4v.s5.3fc745694f31 from=translated src=- shape=20980945 vocab=d29a70ed
-/
lemma leftBridgeWitness_ne_anchor {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g) :
    spec.leftBridgeWitness g ≠ spec.anchor := by
  have hw := midpoint_mem_Ioo (spec.leftBridge_left_lt_anchor hg)
  exact ne_of_lt hw.2

/--
@isnad1 id=ne.1h4v.s5.1557028c4631 from=translated src=- shape=20980945 vocab=5acdaece
-/
lemma rightBridgeWitness_ne_anchor {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g) :
    spec.rightBridgeWitness g ≠ spec.anchor := by
  have hw := midpoint_mem_Ioo (spec.anchor_lt_rightBridge_right hg)
  exact ne_of_gt hw.1

/--
@isnad1 id=ne.2h5v.s6.613d88b0dcc9 from=translated src=- shape=2122bbf8 vocab=7f66609b
-/
lemma leftBridgeWitness_away_exterior {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g) :
    ∀ j ∈ spec.block.exterior,
      spec.leftBridgeWitness g ≠ spec.nodes.point j := by
  intro j hj
  have hjnot : ¬ spec.block.Mem j := by simpa using hj
  have hmid := midpoint_mem_Ioo (spec.leftBridge_left_lt_anchor hg)
  change spec.nodes.point (gapLeftIndex g) < spec.leftBridgeWitness g ∧
    spec.leftBridgeWitness g < spec.anchor at hmid
  change g.val + 1 = spec.block.start at hg
  cases hp : spec.placement
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).1
    omega
  · have hv : spec.block.start = 0 :=
      (show Placement.Valid .leftEndpoint spec.block by
        simpa [hp] using spec.placement_valid).1
    omega
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 = n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    have hjleft : j.val < spec.block.start := by
      simp only [ConsecutiveBlock.Mem] at hjnot
      omega
    have hjle : j ≤ gapLeftIndex g := by
      simp only [Fin.le_iff_val_le_val, gapLeftIndex_val]
      omega
    exact ne_of_gt ((spec.nodes.strictMono.monotone hjle).trans_lt hmid.1)
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    by_cases hjleft : j.val < spec.block.start
    · have hjle : j ≤ gapLeftIndex g := by
        simp only [Fin.le_iff_val_le_val, gapLeftIndex_val]
        omega
      exact ne_of_gt ((spec.nodes.strictMono.monotone hjle).trans_lt hmid.1)
    · have hjright : spec.block.start + d + 2 ≤ j.val := by
        simp only [ConsecutiveBlock.Mem] at hjnot
        omega
      have hfirstj : spec.firstIndex < j := by
        simp only [Fin.lt_def, spec.firstIndex_val]
        omega
      have hanchorj : spec.anchor < spec.nodes.point j := by
        simpa [anchor, hp] using spec.nodes.strictMono hfirstj
      exact ne_of_lt (hmid.2.trans hanchorj)

/--
@isnad1 id=ne.2h5v.s6.746fdfb5ce2b from=translated src=- shape=2122bbf8 vocab=4894ac02
-/
lemma rightBridgeWitness_away_exterior {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g) :
    ∀ j ∈ spec.block.exterior,
      spec.rightBridgeWitness g ≠ spec.nodes.point j := by
  intro j hj
  have hjnot : ¬ spec.block.Mem j := by simpa using hj
  have hmid := midpoint_mem_Ioo (spec.anchor_lt_rightBridge_right hg)
  change spec.anchor < spec.rightBridgeWitness g ∧
    spec.rightBridgeWitness g < spec.nodes.point (gapRightIndex g) at hmid
  change g.val = spec.block.start + d + 1 at hg
  cases hp : spec.placement
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .full spec.block by simpa [hp] using spec.placement_valid).2
    have := g.isLt
    omega
  · have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    have hjright : spec.block.start + d + 2 ≤ j.val := by
      simp only [ConsecutiveBlock.Mem] at hjnot
      omega
    have hrightle : gapRightIndex g ≤ j := by
      simp only [Fin.le_iff_val_le_val, gapRightIndex_val]
      omega
    exact ne_of_lt (hmid.2.trans_le (spec.nodes.strictMono.monotone hrightle))
  · have hv : spec.block.start + d + 2 = n :=
      (show Placement.Valid .rightEndpoint spec.block by
        simpa [hp] using spec.placement_valid).2
    have := g.isLt
    omega
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    by_cases hjleft : j.val < spec.block.start
    · have hjfirst : j < spec.firstIndex := by
        simp only [Fin.lt_def, spec.firstIndex_val]
        exact hjleft
      have hjanchor : spec.nodes.point j < spec.anchor := by
        simpa [anchor, hp] using spec.nodes.strictMono hjfirst
      exact ne_of_gt (hjanchor.trans hmid.1)
    · have hjright : spec.block.start + d + 2 ≤ j.val := by
        simp only [ConsecutiveBlock.Mem] at hjnot
        omega
      have hrightle : gapRightIndex g ≤ j := by
        simp only [Fin.le_iff_val_le_val, gapRightIndex_val]
        omega
      exact ne_of_lt (hmid.2.trans_le (spec.nodes.strictMono.monotone hrightle))

/-- A single clustered cardinal evaluated inside a collapsed gap is bounded
by that gap's Lebesgue height.
@isnad1 id=le.2h7v.s6.0af5cff9437d from=translated src=- shape=ccbe394a vocab=9409414e
-/
lemma abs_fullCardinal_le_gapHeight (δ : ℝ) (hδ : spec.Admissible δ)
    (g : Fin (n - 1)) (k : Fin (d + 2)) {x : ℝ}
    (hx : x ∈ closedGap (spec.orderedNodes δ hδ) g) :
    |spec.fullCardinal δ k x| ≤ gapHeight (spec.orderedNodes δ hδ) g := by
  rw [spec.fullCardinal_eq_lagrangeFundamental δ hδ]
  have hterm :
      |lagrangeFundamental (spec.orderedNodes δ hδ).toNodeFamily
          (spec.block.index k) x| ≤
        lebesgueFunction (spec.orderedNodes δ hδ).toNodeFamily x := by
    unfold lebesgueFunction
    exact Finset.single_le_sum
      (fun i _ => abs_nonneg (lagrangeFundamental
        (spec.orderedNodes δ hδ).toNodeFamily i x))
      (Finset.mem_univ (spec.block.index k))
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge
    (spec.orderedNodes δ hδ).toNodeFamily
    (gap_left_lt_right (spec.orderedNodes δ hδ) g).le
  rw [gapHeight, heq]
  exact hterm.trans (hmax x hx)

/-- Every clustered cardinal forces blowup on a fixed gap to the left of the
block.  Both endpoints of this gap remain fixed.
@isnad1 id=ex.1h6v.s6.0674b3722e78 from=translated src=- shape=b783faa4 vocab=e0697e24
-/
theorem eventually_leftFixed_gapHeight_gt {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftFixed.Valid spec g)
    (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  obtain ⟨η, hη, hgrowth⟩ := spec.eventually_abs_fullCardinal_gt k
    (spec.fixedGapWitness_ne_anchor g)
    (spec.fixedGapWitness_away_exterior g) A
  refine ⟨η, hη, ?_⟩
  intro δ hδpos hδη hδ
  exact (hgrowth δ hδpos hδη).trans_le
    (spec.abs_fullCardinal_le_gapHeight δ hδ g k
      (spec.fixedGapWitness_mem_closedGap_of_leftFixed hg δ hδ))

/-- Every clustered cardinal forces blowup on the moving bridge immediately
to the left of the block.
@isnad1 id=ex.1h6v.s6.d79e99bf31a7 from=translated src=- shape=b783faa4 vocab=6037efc5
-/
theorem eventually_leftBridge_gapHeight_gt {g : Fin (n - 1)}
    (hg : ExteriorGapKind.leftBridge.Valid spec g)
    (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  obtain ⟨η₀, hη₀, hgrowth⟩ := spec.eventually_abs_fullCardinal_gt k
    (spec.leftBridgeWitness_ne_anchor hg)
    (spec.leftBridgeWitness_away_exterior hg) A
  refine ⟨min η₀ (spec.leftBridgeRadius g),
    lt_min hη₀ (spec.leftBridgeRadius_pos hg), ?_⟩
  intro δ hδpos hδη hδ
  have hgrowth' := hgrowth δ hδpos (hδη.trans_le (min_le_left _ _))
  have hmem := spec.leftBridgeWitness_mem_closedGap hg δ hδ
    (hδη.trans_le (min_le_right _ _))
  exact hgrowth'.trans_le
    (spec.abs_fullCardinal_le_gapHeight δ hδ g k hmem)

/-- Every clustered cardinal forces blowup on the moving bridge immediately
to the right of the block.
@isnad1 id=ex.1h6v.s6.7999495b9ba7 from=translated src=- shape=b783faa4 vocab=8557b68b
-/
theorem eventually_rightBridge_gapHeight_gt {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightBridge.Valid spec g)
    (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  obtain ⟨η₀, hη₀, hgrowth⟩ := spec.eventually_abs_fullCardinal_gt k
    (spec.rightBridgeWitness_ne_anchor hg)
    (spec.rightBridgeWitness_away_exterior hg) A
  refine ⟨min η₀ (spec.rightBridgeRadius g),
    lt_min hη₀ (spec.rightBridgeRadius_pos hg), ?_⟩
  intro δ hδpos hδη hδ
  have hgrowth' := hgrowth δ hδpos (hδη.trans_le (min_le_left _ _))
  have hmem := spec.rightBridgeWitness_mem_closedGap hg δ hδ
    (hδη.trans_le (min_le_right _ _))
  exact hgrowth'.trans_le
    (spec.abs_fullCardinal_le_gapHeight δ hδ g k hmem)

/-- Every clustered cardinal forces blowup on a fixed gap to the right of
the block.  Both endpoints of this gap remain fixed.
@isnad1 id=ex.1h6v.s6.53c7ec85f9b3 from=translated src=- shape=b783faa4 vocab=1bcdc7fc
-/
theorem eventually_rightFixed_gapHeight_gt {g : Fin (n - 1)}
    (hg : ExteriorGapKind.rightFixed.Valid spec g)
    (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  obtain ⟨η, hη, hgrowth⟩ := spec.eventually_abs_fullCardinal_gt k
    (spec.fixedGapWitness_ne_anchor g)
    (spec.fixedGapWitness_away_exterior g) A
  refine ⟨η, hη, ?_⟩
  intro δ hδpos hδη hδ
  exact (hgrowth δ hδpos hδη).trans_le
    (spec.abs_fullCardinal_le_gapHeight δ hδ g k
      (spec.fixedGapWitness_mem_closedGap_of_rightFixed hg δ hδ))

/-- Uniform case split for every non-full placement and every gap outside
the cluster's internal `d+1` gaps.  In fact the conclusion holds for every
choice of clustered cardinal `k`; the theorem records one explicitly.

The `hnotfull` argument is intentional: the small-scale collapse family is
only a comparison family in the three non-full placements.
@isnad1 id=ex.2h6v.s6.8a0bca15482d from=translated src=- shape=bd8bd8a0 vocab=66ac15db
-/
theorem eventually_exteriorGap_gapHeight_gt
    (hnotfull : spec.placement ≠ .full) {g : Fin (n - 1)}
    (hg : spec.IsExteriorGap g) (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  have _ := hnotfull
  rcases spec.exteriorGapKind_classification g hg with
    hleft | hleftBridge | hrightBridge | hright
  · exact spec.eventually_leftFixed_gapHeight_gt hleft k A
  · exact spec.eventually_leftBridge_gapHeight_gt hleftBridge k A
  · exact spec.eventually_rightBridge_gapHeight_gt hrightBridge k A
  · exact spec.eventually_rightFixed_gapHeight_gt hright k A

/-- Nonvacuous eventual formulation.  For every sufficiently small positive
scale in any of the three genuine collapse placements, an admissibility
proof exists and the selected exterior gap height exceeds `A`.

This theorem makes the left-endpoint, right-endpoint, and interior
admissibility constructions explicit; the full placement is discharged by
the stated exception rather than treated as a small-scale family.
@isnad1 id=ex.2h6v.s6.b4df6cf6fb3d from=translated src=- shape=b3bfa1db vocab=66ac15db
-/
theorem eventually_exists_admissible_exteriorGap_gapHeight_gt
    (hnotfull : spec.placement ≠ .full) {g : Fin (n - 1)}
    (hg : spec.IsExteriorGap g) (k : Fin (d + 2)) (A : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∃ hδ : spec.Admissible δ,
        A < gapHeight (spec.orderedNodes δ hδ) g := by
  obtain ⟨η₀, hη₀, hgrowth⟩ :=
    spec.eventually_exteriorGap_gapHeight_gt hnotfull hg k A
  cases hp : spec.placement
  · exact (hnotfull hp).elim
  · have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    obtain ⟨η₁, hη₁, hadm⟩ := spec.exists_small_admissible_of_not_right
      (by simp [hp]) hv.2
    refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
    intro δ hδpos hδη
    have hδ := hadm δ hδpos (hδη.trans_le (min_le_right _ _))
    exact ⟨hδ, hgrowth δ hδpos
      (hδη.trans_le (min_le_left _ _)) hδ⟩
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 = n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    obtain ⟨η₁, hη₁, hadm⟩ := spec.exists_small_admissible_of_right hp hv.1 hv.2
    refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
    intro δ hδpos hδη
    have hδ := hadm δ hδpos (hδη.trans_le (min_le_right _ _))
    exact ⟨hδ, hgrowth δ hδpos
      (hδη.trans_le (min_le_left _ _)) hδ⟩
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp, Nat.add_assoc] using spec.placement_valid
    obtain ⟨η₁, hη₁, hadm⟩ := spec.exists_small_admissible_of_not_right
      (by simp [hp]) hv.2
    refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
    intro δ hδpos hδη
    have hδ := hadm δ hδpos (hδη.trans_le (min_le_right _ _))
    exact ⟨hδ, hgrowth δ hδpos
      (hδη.trans_le (min_le_left _ _)) hδ⟩

end Spec

end

end Erdos1153.Collapse
