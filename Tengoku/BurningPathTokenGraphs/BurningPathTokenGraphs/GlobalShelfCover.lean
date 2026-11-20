import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.Shelf
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ShelfRecurrence
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ShelfTrajectory
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global covers assembled from shelf trajectories

This file packages the finite shelf recursion. A shelf uses the largest
remaining radii, while the recursive cover of the residual cap uses the
smaller radii. The final cover is indexed by `Fin w` and uses every radius
`0, ..., w - 1` exactly once.
-/

open Filter Topology

namespace BurningPath

/-- A legal-center ranked square cover of a parity cap using all radii below `w`.-/
def IsParityCapRankedCover (h z w : ℕ) (σ : ℤ)
    (centers : Fin w → ℤ × ℤ) : Prop :=
  (∀ r, centers r ∈ parityCap h z σ) ∧
    ∀ p ∈ parityCap h z σ,
      ∃ r, p ∈ integerSquare (centers r) r.val

/-- The decreasing embedding that assigns the `i`-th shelf center radius `w - (i + 1)`.-/
def shelfRadiusEmbedding (w q : ℕ) (hqw : q ≤ w) : Fin q ↪ Fin w where
  toFun i := ⟨w - (i.val + 1), by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi : i.val + 1 ≤ w := by omega
    have hj : j.val + 1 ≤ w := by omega
    have hval := congrArg Fin.val hij
    change w - (i.val + 1) = w - (j.val + 1) at hval
    omega

/--
@isnad1 id=eq.1h3v.s5.e0461f0fd32f from=translated src=- shape=e69f1dbb vocab=15673bc1
-/
@[simp]
theorem shelfRadiusEmbedding_val (w q : ℕ) (hqw : q ≤ w) (i : Fin q) :
    (shelfRadiusEmbedding w q hqw i).val = w - (i.val + 1) :=
  rfl

/-- A residual cap is contained in the cap from which its bottom band was removed.
@isnad1 id=le.1h4v.s6.4623528e4407 from=translated src=- shape=ccfe808b vocab=d167c97e
-/
theorem residual_parityCap_subset {h z a : ℕ} {σ : ℤ} (ha : 2 * a ≤ z) :
    parityCap (h + 2 * a) (z - 2 * a) σ ⊆ parityCap h z σ := by
  intro p hp
  rcases hp with ⟨hpBottom, hpTop, hpSide, hpParity⟩
  have hapex : h + 2 * a + (z - 2 * a) = h + z := by omega
  have hapexInt :
      ((h + 2 * a : ℕ) : ℤ) + ((z - 2 * a : ℕ) : ℤ) =
        (h : ℤ) + (z : ℤ) := by
    exact_mod_cast hapex
  simp only [parityCap, Set.mem_ofPred_eq]
  constructor
  · exact hpBottom.trans' (by exact_mod_cast Nat.le_add_right h (2 * a))
  constructor
  · rw [← hapexInt]
    exact hpTop
  constructor
  · rw [← hapex]
    exact hpSide
  · exact hpParity

/--
Extend a shelf that covers the whole cap to a full ranked cover.  Unused lower radii receive the
legal apex center.
@isnad1 id=ex.4h6v.s7.759532945fa9 from=translated src=- shape=159c4bc7 vocab=e58e61a0
-/
theorem exists_full_rankedCover_of_shelf {h z w q : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2]) (hqw : q ≤ w)
    (shelfCenters : Fin q → ℤ × ℤ)
    (hlegal : ∀ i, shelfCenters i ∈ parityCap h z σ)
    (hcover :
      ∀ p ∈ parityCap h z σ,
        ∃ i, p ∈ integerSquare (shelfCenters i) (w - (i.val + 1))) :
    ∃ centers : Fin w → ℤ × ℤ,
      IsParityCapRankedCover h z w σ centers := by
  classical
  let e := shelfRadiusEmbedding w q hqw
  let apex := parityCapApex h z
  let centers : Fin w → ℤ × ℤ :=
    Function.extend e shelfCenters (fun _ ↦ apex)
  have hcenters (i : Fin q) : centers (e i) = shelfCenters i :=
    e.injective.extend_apply shelfCenters (fun _ ↦ apex) i
  refine ⟨centers, ?_, ?_⟩
  · intro r
    by_cases hr : r ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hr
      rw [hcenters]
      exact hlegal i
    · change Function.extend e shelfCenters (fun _ ↦ apex) r ∈ parityCap h z σ
      rw [Function.extend_apply' shelfCenters (fun _ ↦ apex) r]
      · exact parityCapApex_mem hσ
      · simpa only [Set.mem_range] using hr
  · intro p hp
    obtain ⟨i, hi⟩ := hcover p hp
    refine ⟨e i, ?_⟩
    rw [hcenters]
    simpa only [e, shelfRadiusEmbedding_val] using hi

/--
Combine one nonterminal shelf with a ranked cover of its residual cap.  The two pieces occupy
disjoint high and low radius intervals.
@isnad1 id=ex.6h7v.s8.2d4f06bfa477 from=translated src=- shape=96eb7efc vocab=b25dc222
-/
theorem exists_full_rankedCover_of_shelf_and_residual {h z w q : ℕ} {σ : ℤ}
    (hσ : (h + z : ℕ) ≡ σ [ZMOD 2]) (hqw : q ≤ w)
    (hnonterminal : 2 * (w - q) < z)
    (shelfCenters : Fin q → ℤ × ℤ)
    (hlegal : ∀ i, shelfCenters i ∈ parityCap h z σ)
    (hresidual :
      ∀ p ∈ parityCap h z σ,
        (∀ i, p ∉ integerSquare (shelfCenters i) (w - (i.val + 1))) →
          p ∈ parityCap (h + 2 * (w - q)) (z - 2 * (w - q)) σ)
    (lowerCenters : Fin (w - q) → ℤ × ℤ)
    (hlower :
      IsParityCapRankedCover (h + 2 * (w - q)) (z - 2 * (w - q))
        (w - q) σ lowerCenters) :
    ∃ centers : Fin w → ℤ × ℤ,
      IsParityCapRankedCover h z w σ centers := by
  classical
  let high := shelfRadiusEmbedding w q hqw
  let low : Fin (w - q) ↪ Fin w := Fin.castLEEmb (Nat.sub_le w q)
  let apex := parityCapApex h z
  let withLow : Fin w → ℤ × ℤ :=
    Function.extend low lowerCenters (fun _ ↦ apex)
  let centers : Fin w → ℤ × ℤ :=
    Function.extend high shelfCenters withLow
  have hhigh (i : Fin q) : centers (high i) = shelfCenters i :=
    high.injective.extend_apply shelfCenters withLow i
  have hdisjoint (i : Fin q) (j : Fin (w - q)) : high i ≠ low j := by
    intro hij
    have hval := congrArg Fin.val hij
    simp only [high, low, shelfRadiusEmbedding_val, Fin.castLEEmb_apply,
      Fin.val_castLE] at hval
    have hi : i.val + 1 ≤ q := i.isLt
    have hj := j.isLt
    omega
  have hwithLow (j : Fin (w - q)) : withLow (low j) = lowerCenters j :=
    low.injective.extend_apply lowerCenters (fun _ ↦ apex) j
  have hlow (j : Fin (w - q)) : centers (low j) = lowerCenters j := by
    change Function.extend high shelfCenters withLow (low j) = lowerCenters j
    rw [Function.extend_apply']
    · exact hwithLow j
    · rintro ⟨i, hi⟩
      exact hdisjoint i j hi
  have hresSubset :
      parityCap (h + 2 * (w - q)) (z - 2 * (w - q)) σ ⊆
        parityCap h z σ :=
    residual_parityCap_subset (by omega)
  refine ⟨centers, ?_, ?_⟩
  · intro r
    by_cases hrHigh : r ∈ Set.range high
    · obtain ⟨i, rfl⟩ := hrHigh
      rw [hhigh]
      exact hlegal i
    · change Function.extend high shelfCenters withLow r ∈ parityCap h z σ
      rw [Function.extend_apply']
      · by_cases hrLow : r ∈ Set.range low
        · obtain ⟨j, rfl⟩ := hrLow
          rw [hwithLow]
          exact hresSubset (hlower.1 j)
        · change Function.extend low lowerCenters (fun _ ↦ apex) r ∈ parityCap h z σ
          rw [Function.extend_apply']
          · exact parityCapApex_mem hσ
          · simpa only [Set.mem_range] using hrLow
      · simpa only [Set.mem_range] using hrHigh
  · intro p hp
    by_cases hshelf :
        ∃ i, p ∈ integerSquare (shelfCenters i) (w - (i.val + 1))
    · obtain ⟨i, hi⟩ := hshelf
      refine ⟨high i, ?_⟩
      rw [hhigh]
      simpa only [high, shelfRadiusEmbedding_val] using hi
    · have huncovered :
          ∀ i, p ∉ integerSquare (shelfCenters i) (w - (i.val + 1)) := by
        simpa only [not_exists] using hshelf
      obtain ⟨j, hj⟩ := hlower.2 p (hresidual p hp huncovered)
      refine ⟨low j, ?_⟩
      rw [hlow]
      simpa only [low, Fin.castLEEmb_apply, Fin.val_castLE] using hj

/--
A finite least-width shelf run.  The first `m` stages are nonterminal updates and stage `m` is
terminal, either by an apex square or by one final shelf.-/
structure ShelfRun (m : ℕ) (h z w q : ℕ → ℕ) : Prop where
  width : ∀ i ≤ m, 144 ≤ w i
  cube : ∀ i ≤ m, 3 * (z i) ^ 2 ≤ 4 * (w i) ^ 3
  tall : ∀ i < m, w i - 1 < z i
  least :
    ∀ i ≤ m, w i - 1 < z i → IsLeastShelfWidth (w i) (z i) (q i)
  nonterminal : ∀ i < m, 2 * (w i - q i) < z i
  h_next : ∀ i < m, h (i + 1) = h i + 2 * (w i - q i)
  z_next : ∀ i < m, z (i + 1) = z i - 2 * (w i - q i)
  w_next : ∀ i < m, w (i + 1) = w i - q i
  terminal :
    z m ≤ w m - 1 ∨ z m ≤ 2 * (w m - q m)

/-- Every finite shelf run assembles into a legal cover using all radii below the initial width.
@isnad1 id=ex.2h6v.s6.5054bfbf5496 from=translated src=- shape=52233b82 vocab=e1b1f571
-/
theorem ShelfRun.exists_rankedCover {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {σ : ℤ}
    (hσ : (h 0 + z 0 : ℕ) ≡ σ [ZMOD 2]) :
    ∃ centers : Fin (w 0) → ℤ × ℤ,
      IsParityCapRankedCover (h 0) (z 0) (w 0) σ centers := by
  induction m generalizing h z w q with
  | zero =>
      have hw : 3 ≤ w 0 := (run.width 0 (by omega)).trans' (by omega)
      by_cases hterminal : z 0 ≤ w 0 - 1
      · let apex := parityCapApex (h 0) (z 0)
        let centers : Fin (w 0) → ℤ × ℤ := fun _ ↦ apex
        refine ⟨centers, ?_, ?_⟩
        · intro r
          exact parityCapApex_mem hσ
        · intro p hp
          refine ⟨⟨w 0 - 1, by omega⟩, ?_⟩
          exact parityCap_subset_terminal_square σ hterminal hp
      · have htall : w 0 - 1 < z 0 := by omega
        have hleast := run.least 0 (by omega) htall
        have hq2 : 2 ≤ q 0 := hleast.1.1
        have hqhalf : 2 * q 0 ≤ w 0 := hleast.1.2.1
        have hqw : q 0 < w 0 := by omega
        have hcapacity : z 0 ≤ q 0 * (w 0 - q 0) := hleast.1.2.2
        have hfinal : z 0 ≤ 2 * (w 0 - q 0) :=
          run.terminal.resolve_left (by simpa using hterminal)
        obtain ⟨shelfCenters, hlegal, hcover⟩ :=
          exists_shelf_centers_cover_cap hσ hw htall hq2 hqw hcapacity hfinal
        exact exists_full_rankedCover_of_shelf hσ hqw.le shelfCenters hlegal hcover
  | succ m ih =>
      have hw : 3 ≤ w 0 := (run.width 0 (by omega)).trans' (by omega)
      have htall : w 0 - 1 < z 0 := run.tall 0 (by omega)
      have hleast := run.least 0 (by omega) htall
      have hq2 : 2 ≤ q 0 := hleast.1.1
      have hqhalf : 2 * q 0 ≤ w 0 := hleast.1.2.1
      have hqw : q 0 < w 0 := by omega
      have hcapacity : z 0 ≤ q 0 * (w 0 - q 0) := hleast.1.2.2
      have hnonterminal : 2 * (w 0 - q 0) < z 0 :=
        run.nonterminal 0 (by omega)
      obtain ⟨shelfCenters, hlegal, _, hresidual⟩ :=
        exists_shelf_centers_with_residual hσ hw htall hq2 hqw hcapacity
          hnonterminal
      let h' : ℕ → ℕ := fun i ↦ h (i + 1)
      let z' : ℕ → ℕ := fun i ↦ z (i + 1)
      let w' : ℕ → ℕ := fun i ↦ w (i + 1)
      let q' : ℕ → ℕ := fun i ↦ q (i + 1)
      have tailRun : ShelfRun m h' z' w' q' := {
        width := by
          intro i hi
          exact run.width (i + 1) (by omega)
        cube := by
          intro i hi
          exact run.cube (i + 1) (by omega)
        tall := by
          intro i hi
          exact run.tall (i + 1) (by omega)
        least := by
          intro i hi hitall
          exact run.least (i + 1) (by omega) hitall
        nonterminal := by
          intro i hi
          exact run.nonterminal (i + 1) (by omega)
        h_next := by
          intro i hi
          exact run.h_next (i + 1) (by omega)
        z_next := by
          intro i hi
          exact run.z_next (i + 1) (by omega)
        w_next := by
          intro i hi
          exact run.w_next (i + 1) (by omega)
        terminal := run.terminal
      }
      have hhNext : h 1 = h 0 + 2 * (w 0 - q 0) := by
        simpa using run.h_next 0 (by omega)
      have hzNext : z 1 = z 0 - 2 * (w 0 - q 0) := by
        simpa using run.z_next 0 (by omega)
      have hwNext : w 1 = w 0 - q 0 := by
        simpa using run.w_next 0 (by omega)
      have hapex : h 1 + z 1 = h 0 + z 0 := by omega
      have hσ' : (h' 0 + z' 0 : ℕ) ≡ σ [ZMOD 2] := by
        change (h 1 + z 1 : ℕ) ≡ σ [ZMOD 2]
        rw [hapex]
        exact hσ
      obtain ⟨lowerCenters, hlower⟩ := ih tailRun hσ'
      change IsParityCapRankedCover (h 1) (z 1) (w 1) σ lowerCenters at hlower
      rw [hhNext, hzNext] at hlower
      let adjustedLower : Fin (w 0 - q 0) → ℤ × ℤ :=
        fun r ↦ lowerCenters (Fin.cast hwNext.symm r)
      have hadjusted :
          IsParityCapRankedCover (h 0 + 2 * (w 0 - q 0))
            (z 0 - 2 * (w 0 - q 0)) (w 0 - q 0) σ adjustedLower := by
        constructor
        · intro r
          exact hlower.1 (Fin.cast hwNext.symm r)
        · intro p hp
          obtain ⟨r, hr⟩ := hlower.2 p hp
          refine ⟨Fin.cast hwNext r, ?_⟩
          simpa [adjustedLower] using hr
      exact
        exists_full_rankedCover_of_shelf_and_residual hσ hqw.le hnonterminal
          shelfCenters hlegal hresidual adjustedLower hadjusted

/-- Widths along a shelf run never exceed the initial width.
@isnad1 id=le.2h6v.s5.300afbdeb32d from=translated src=- shape=07d92051 vocab=4b1e9f56
-/
theorem ShelfRun.w_le_initial {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {i : ℕ} (hi : i ≤ m) :
    w i ≤ w 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      calc
        w (i + 1) = w i - q i := run.w_next i (by omega)
        _ ≤ w i := Nat.sub_le _ _
        _ ≤ w 0 := ih (by omega)

/-- Each nonterminal update retains at least three quarters of the preceding width.
@isnad1 id=le.2h6v.s6.55229c347fd0 from=translated src=- shape=3a0c052a vocab=e0aa37d8
-/
theorem ShelfRun.three_mul_w_le_four_mul_w_next {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {i : ℕ} (hi : i < m) :
    3 * w i ≤ 4 * w (i + 1) := by
  have htall := run.tall i hi
  have hleast := run.least i (by omega) htall
  have hbounds := hleast.bounds (run.width i (by omega)) (run.cube i (by omega))
  rw [run.w_next i hi]
  exact hbounds.2.2

/-- The cap height decrement is exactly twice the next width.
@isnad1 id=eq.2h6v.s6.4f65ce0033d7 from=translated src=- shape=82617412 vocab=b76dfb08
-/
theorem ShelfRun.z_sub_z_next {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {i : ℕ} (hi : i < m) :
    (z i : ℝ) - z (i + 1) = 2 * (w (i + 1) : ℝ) := by
  rw [run.z_next i hi, run.w_next i hi]
  have hsub : 2 * (w i - q i) ≤ z i := by
    exact (run.nonterminal i hi).le
  rw [Nat.cast_sub hsub]
  norm_num

/-- Every update in a shelf run satisfies the one-step potential estimate.
@isnad1 id=le.2h6v.s7.8b8545383353 from=translated src=- shape=b75ae3be vocab=60ce09ac
-/
theorem ShelfRun.potential_step {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {i : ℕ} (hi : i < m) :
    shelfPotential (w (i + 1) : ℝ) (z (i + 1) : ℝ) ≥
      shelfPotential (w i : ℝ) (z i : ℝ) - 45 * (w i : ℝ) ^ 2 := by
  have htall := run.tall i hi
  have hleast := run.least i (by omega) htall
  have hstep :=
    hleast.potential_update (run.width i (by omega)) htall
      (run.cube i (by omega)) (run.nonterminal i hi)
  rw [run.w_next i hi, run.z_next i hi]
  exact hstep

/-- Equation (23)'s square-sum estimate holds for every prefix of a shelf run.
@isnad1 id=le.2h6v.s6.4ededc270904 from=translated src=- shape=ab3b8763 vocab=e344ab4b
-/
theorem ShelfRun.sum_sq_le {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {j : ℕ} (hj : j ≤ m) :
    ∑ i ∈ Finset.range j, (w i : ℝ) ^ 2 ≤
      (2 / 3 : ℝ) * (w 0 : ℝ) * (z 0 : ℝ) := by
  apply shelfTrajectory_sum_sq_le (fun i ↦ (w i : ℝ)) (fun i ↦ (z i : ℝ))
  · intro i hi
    positivity
  · positivity
  · intro i hi
    exact_mod_cast run.w_le_initial (hi.le.trans hj)
  · intro i hi
    exact_mod_cast run.three_mul_w_le_four_mul_w_next (hi.trans_le hj)
  · intro i hi
    exact run.z_sub_z_next (hi.trans_le hj)

/-- Equation (23)'s accumulated potential estimate holds at every stage of a shelf run.
@isnad1 id=le.2h6v.s6.f1548b7f6a4b from=translated src=- shape=fe791412 vocab=b3a94b5d
-/
theorem ShelfRun.potential_lower {m : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {j : ℕ} (hj : j ≤ m) :
    shelfPotential (w j : ℝ) (z j : ℝ) ≥
      shelfPotential (w 0 : ℝ) (z 0 : ℝ) -
        30 * (w 0 : ℝ) * (z 0 : ℝ) := by
  apply shelfPotential_trajectory_lower (fun i ↦ (w i : ℝ)) (fun i ↦ (z i : ℝ))
  · exact run.sum_sq_le hj
  · intro i hi
    exact run.potential_step (hi.trans_le hj)

/-- A sufficient initial potential margin persists throughout the run.
@isnad1 id=le.3h7v.s6.f004865d82f6 from=translated src=- shape=a5728ad9 vocab=1911d0d4
-/
theorem ShelfRun.potential_ge_of_initial_margin {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {E : ℝ}
    (hmargin :
      E + 30 * (w 0 : ℝ) * (z 0 : ℝ) ≤
        shelfPotential (w 0 : ℝ) (z 0 : ℝ))
    {j : ℕ} (hj : j ≤ m) :
    E ≤ shelfPotential (w j : ℝ) (z j : ℝ) := by
  have htrajectory := run.potential_lower hj
  linarith

/-- The persistent potential margin gives the cubic part of the width bound in (31).
@isnad1 id=le.3h7v.s7.a63d38fbd931 from=translated src=- shape=39a4f470 vocab=8680cb9a
-/
theorem ShelfRun.width_cube_ge_of_initial_margin {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {E : ℝ}
    (hmargin :
      E + 30 * (w 0 : ℝ) * (z 0 : ℝ) ≤
        shelfPotential (w 0 : ℝ) (z 0 : ℝ))
    {j : ℕ} (hj : j ≤ m) :
    (3 / 4 : ℝ) * E ≤ (w j : ℝ) ^ 3 :=
  cube_lower_of_shelfPotential_lower (run.potential_ge_of_initial_margin hmargin hj)

private theorem sum_range_forward_difference (z : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (z i - z (i + 1)) = z 0 - z m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/--
If every preterminal width is at least `B`, each nonterminal shelf removes at least `3B/2`
height in total.
@isnad1 id=le.2h6v.s6.892403208b12 from=translated src=- shape=ba77a4c7 vocab=83395a67
-/
theorem ShelfRun.nonterminal_count_mul_le {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {B : ℝ}
    (hB : ∀ i < m, B ≤ (w i : ℝ)) :
    (m : ℝ) * ((3 / 2 : ℝ) * B) ≤ (z 0 : ℝ) := by
  have hpoint :
      ∀ i ∈ Finset.range m,
        (3 / 2 : ℝ) * B ≤ (z i : ℝ) - z (i + 1) := by
    intro i hi
    have him := Finset.mem_range.mp hi
    have hwidth := hB i him
    have hnext : 3 * (w i : ℝ) ≤ 4 * (w (i + 1) : ℝ) := by
      exact_mod_cast run.three_mul_w_le_four_mul_w_next him
    rw [run.z_sub_z_next him]
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  rw [sum_range_forward_difference] at hsum
  have hzFinal : 0 ≤ (z m : ℝ) := by positivity
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    hsum.trans (by nlinarith : (z 0 : ℝ) - z m ≤ z 0)

/-- Ceiling form of the explicit nonterminal-shelf count.
@isnad1 id=le.3h6v.s6.b789112415d4 from=translated src=- shape=77b65a31 vocab=b05d6abc
-/
theorem ShelfRun.nonterminal_count_le_ceil {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {B : ℝ}
    (hBpos : 0 < B) (hB : ∀ i < m, B ≤ (w i : ℝ)) :
    m ≤ ⌈(2 * (z 0 : ℝ)) / (3 * B)⌉₊ := by
  have hcount := run.nonterminal_count_mul_le hB
  have hreal : (m : ℝ) ≤ (2 * (z 0 : ℝ)) / (3 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * B)).2
    nlinarith
  have hceil :
      (2 * (z 0 : ℝ)) / (3 * B) ≤
        (⌈(2 * (z 0 : ℝ)) / (3 * B)⌉₊ : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

/-- Including the final shelf gives the stated `ceiling + 1` shelf bound.
@isnad1 id=le.3h6v.s7.4695f26c4bc4 from=translated src=- shape=9f9c3e61 vocab=77b994fd
-/
theorem ShelfRun.shelf_count_le_ceil_add_one {m : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q) {B : ℝ}
    (hBpos : 0 < B) (hB : ∀ i < m, B ≤ (w i : ℝ)) :
    m + 1 ≤ ⌈(2 * (z 0 : ℝ)) / (3 * B)⌉₊ + 1 := by
  exact Nat.add_le_add_right (run.nonterminal_count_le_ceil hBpos hB) 1

/-- The potential surplus `δ_ε` for the global shelf cover.-/
noncomputable def shelfDelta (ε : ℝ) : ℝ :=
  (1 + ε) ^ 3 - 1

/-- The width coefficient `β_ε` for the global shelf cover.-/
noncomputable def shelfBeta (ε : ℝ) : ℝ :=
  ((3 * shelfDelta ε) / 8) ^ (3 : ℝ)⁻¹

/-- The `N^(2/3)` width scale appearing in (31).-/
noncomputable def shelfWidthScale (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 / 3 : ℝ)

/--
@isnad1 id=lt.1h1v.s4.079bee69daed from=translated src=- shape=35bd48ee vocab=c0070500
-/
theorem shelfDelta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < shelfDelta ε := by
  have hone : (1 : ℝ) < 1 + ε := by linarith
  have hpow : (1 : ℝ) ^ 3 < (1 + ε) ^ 3 :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).2 hone
  rw [shelfDelta]
  norm_num at hpow ⊢
  exact hpow

/--
@isnad1 id=lt.1h1v.s4.53462f3a4f7a from=translated src=- shape=35bd48ee vocab=d7e2f3d3
-/
theorem shelfBeta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < shelfBeta ε := by
  rw [shelfBeta]
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos (by norm_num) (shelfDelta_pos hε)) (by norm_num)

/--
@isnad1 id=eq.1h1v.s6.307c229bde90 from=translated src=- shape=1a7dfaee vocab=5ba948d0
-/
@[simp]
theorem shelfBeta_pow_three {ε : ℝ} (hε : 0 < ε) :
    shelfBeta ε ^ 3 = (3 * shelfDelta ε) / 8 := by
  simpa [shelfBeta] using
    (Real.rpow_inv_natCast_pow (x := (3 * shelfDelta ε) / 8) (n := 3)
      (div_nonneg (mul_nonneg (by norm_num) (shelfDelta_pos hε).le) (by norm_num))
      (by norm_num))

/--
@isnad1 id=eq.0h1v.s5.3bd40401a20c from=translated src=- shape=83850f4f vocab=83d6a5d1
-/
@[simp]
theorem shelfWidthScale_pow_three (N : ℕ) :
    shelfWidthScale N ^ 3 = (N : ℝ) ^ 2 := by
  have h :=
    (Real.rpow_mul_natCast (show 0 ≤ (N : ℝ) by positivity)
      (2 / 3 : ℝ) 3).symm
  norm_num [shelfWidthScale, Real.rpow_natCast] at h ⊢
  exact h

/--
@isnad1 id=lt.1h1v.s4.dc934b927e3a from=translated src=- shape=7f2e781e vocab=95dfa640
-/
theorem shelfWidthScale_pos {N : ℕ} (hN : 0 < N) :
    0 < shelfWidthScale N := by
  rw [shelfWidthScale]
  apply Real.rpow_pos_of_pos
  positivity

/--
@isnad1 id=le.0h1v.s3.9ba2bc2c1a46 from=translated src=- shape=b9369acb vocab=2dfaf37d
-/
theorem shelfWidthScale_nonneg (N : ℕ) :
    0 ≤ shelfWidthScale N := by
  rw [shelfWidthScale]
  exact Real.rpow_nonneg (by positivity) _

/-- The cubic potential consequence in (31), converted to its advertised width lower bound.
@isnad1 id=le.4h8v.s7.76dddada394f from=translated src=- shape=bdf01a72 vocab=35e9a08b
-/
theorem ShelfRun.shelfBeta_mul_widthScale_le {m N : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q)
    {ε : ℝ} (hε : 0 < ε)
    (hmargin :
      shelfDelta ε / 2 * (N : ℝ) ^ 2 +
          30 * (w 0 : ℝ) * (z 0 : ℝ) ≤
        shelfPotential (w 0 : ℝ) (z 0 : ℝ))
    {j : ℕ} (hj : j ≤ m) :
    shelfBeta ε * shelfWidthScale N ≤ (w j : ℝ) := by
  have hcube :=
    run.width_cube_ge_of_initial_margin hmargin hj
  have hleft :
      (shelfBeta ε * shelfWidthScale N) ^ 3 =
        (3 / 4 : ℝ) * (shelfDelta ε / 2 * (N : ℝ) ^ 2) := by
    rw [mul_pow, shelfBeta_pow_three hε, shelfWidthScale_pow_three]
    ring
  apply
    (pow_le_pow_iff_left₀
      (mul_nonneg (shelfBeta_pos hε).le (shelfWidthScale_nonneg N))
      (Nat.cast_nonneg _) (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hleft]
  exact hcube

/--
Equation (31) for every stage of a run under the initial accumulated-loss
margin for the global shelf cover.
@isnad1 id=and.4h8v.s8.934e568c7c7d from=translated src=- shape=069b8069 vocab=35e9a08b
-/
theorem ShelfRun.equation31 {m N : ℕ} {h z w q : ℕ → ℕ}
    (run : ShelfRun m h z w q) {ε : ℝ} (hε : 0 < ε)
    (hmargin :
      shelfDelta ε / 2 * (N : ℝ) ^ 2 +
          30 * (w 0 : ℝ) * (z 0 : ℝ) ≤
        shelfPotential (w 0 : ℝ) (z 0 : ℝ))
    {j : ℕ} (hj : j ≤ m) :
    shelfDelta ε / 2 * (N : ℝ) ^ 2 ≤
        shelfPotential (w j : ℝ) (z j : ℝ) ∧
      shelfBeta ε * shelfWidthScale N ≤ (w j : ℝ) ∧
        144 ≤ w j := by
  exact
    ⟨run.potential_ge_of_initial_margin hmargin hj,
      run.shelfBeta_mul_widthScale_le hε hmargin hj,
      run.width j hj⟩

private theorem width_scale_quotient {N : ℕ} (hN : 0 < N) :
    (N : ℝ) / shelfWidthScale N = (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hNReal : 0 < (N : ℝ) := by positivity
  have h := (Real.rpow_sub hNReal (1 : ℝ) (2 / 3 : ℝ)).symm
  norm_num [shelfWidthScale, Real.rpow_one] at h ⊢
  exact h

/-- Explicit shelf-count bound in terms of the initial cap size.
@isnad1 id=le.5h7v.s8.56e334f5e323 from=translated src=- shape=e014de6e vocab=ba10aeb3
-/
theorem ShelfRun.shelf_count_explicit_bound {m N : ℕ}
    {h z w q : ℕ → ℕ} (run : ShelfRun m h z w q)
    {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) (hz0 : z 0 = N)
    (hmargin :
      shelfDelta ε / 2 * (N : ℝ) ^ 2 +
          30 * (w 0 : ℝ) * (z 0 : ℝ) ≤
        shelfPotential (w 0 : ℝ) (z 0 : ℝ)) :
    m + 1 ≤
      ⌈(2 / (3 * shelfBeta ε)) * (N : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1 := by
  have hB :
      ∀ i < m, shelfBeta ε * shelfWidthScale N ≤ (w i : ℝ) := by
    intro i hi
    exact run.shelfBeta_mul_widthScale_le hε hmargin hi.le
  have hcount :=
    run.shelf_count_le_ceil_add_one
      (mul_pos (shelfBeta_pos hε) (shelfWidthScale_pos hN)) hB
  rw [hz0] at hcount
  have harg :
      (2 * (N : ℝ)) / (3 * (shelfBeta ε * shelfWidthScale N)) =
        (2 / (3 * shelfBeta ε)) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← width_scale_quotient hN]
    field_simp [(shelfBeta_pos hε).ne', (shelfWidthScale_pos hN).ne']
  rwa [harg] at hcount

/-- Prepend one value to a sequence indexed by natural numbers.-/
def prependNat (x : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => x
  | i + 1 => f i

/--
@isnad1 id=eq.0h2v.s4.669e522f94c0 from=translated src=- shape=a9fb1440 vocab=be0ba193
-/
@[simp]
theorem prependNat_zero (x : ℕ) (f : ℕ → ℕ) :
    prependNat x f 0 = x :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.148de5c675c9 from=translated src=- shape=1d992269 vocab=16497f44
-/
@[simp]
theorem prependNat_succ (x : ℕ) (f : ℕ → ℕ) (i : ℕ) :
    prependNat x f (i + 1) = f i :=
  rfl

/-- Prepend one nonterminal least-width update to an existing shelf run.
@isnad1 id=shelfrun.9h9v.s8.10917b35128b from=translated src=- shape=a89606c8 vocab=f9faf405
-/
theorem ShelfRun.prepend {m : ℕ} {H Z W Q : ℕ → ℕ}
    (tail : ShelfRun m H Z W Q) {h z w q : ℕ}
    (hw : 144 ≤ w) (hcube : 3 * z ^ 2 ≤ 4 * w ^ 3)
    (htall : w - 1 < z) (hleast : IsLeastShelfWidth w z q)
    (hnonterminal : 2 * (w - q) < z)
    (hH : H 0 = h + 2 * (w - q))
    (hZ : Z 0 = z - 2 * (w - q))
    (hW : W 0 = w - q) :
    ShelfRun (m + 1) (prependNat h H) (prependNat z Z)
      (prependNat w W) (prependNat q Q) := by
  refine {
    width := ?_
    cube := ?_
    tall := ?_
    least := ?_
    nonterminal := ?_
    h_next := ?_
    z_next := ?_
    w_next := ?_
    terminal := ?_
  }
  · intro i hi
    cases i with
    | zero => exact hw
    | succ i => exact tail.width i (by omega)
  · intro i hi
    cases i with
    | zero => exact hcube
    | succ i => exact tail.cube i (by omega)
  · intro i hi
    cases i with
    | zero => exact htall
    | succ i => exact tail.tall i (by omega)
  · intro i hi hiTall
    cases i with
    | zero => exact hleast
    | succ i => exact tail.least i (by omega) hiTall
  · intro i hi
    cases i with
    | zero => exact hnonterminal
    | succ i => exact tail.nonterminal i (by omega)
  · intro i hi
    cases i with
    | zero => simpa using hH
    | succ i => simpa using tail.h_next i (by omega)
  · intro i hi
    cases i with
    | zero => simpa using hZ
    | succ i => simpa using tail.z_next i (by omega)
  · intro i hi
    cases i with
    | zero => simpa using hW
    | succ i => simpa using tail.w_next i (by omega)
  · simpa using tail.terminal

/-- Existence of a finite shelf run beginning at the specified cap and width.-/
def HasShelfRun (h z w : ℕ) : Prop :=
  ∃ m : ℕ, ∃ H Z W Q : ℕ → ℕ,
    H 0 = h ∧ Z 0 = z ∧ W 0 = w ∧ ShelfRun m H Z W Q

/-- A finite run immediately yields the global ranked cover at its initial state.
@isnad1 id=ex.2h4v.s5.d563a7446ac8 from=translated src=- shape=2f525a92 vocab=1866907c
-/
theorem HasShelfRun.exists_rankedCover {h z w : ℕ} (hrun : HasShelfRun h z w)
    {σ : ℤ} (hσ : (h + z : ℕ) ≡ σ [ZMOD 2]) :
    ∃ centers : Fin w → ℤ × ℤ,
      IsParityCapRankedCover h z w σ centers := by
  obtain ⟨m, H, Z, W, Q, hH, hZ, hW, run⟩ := hrun
  have hσ' : (H 0 + Z 0 : ℕ) ≡ σ [ZMOD 2] := by
    rw [hH, hZ]
    exact hσ
  obtain ⟨centers, hcenters⟩ := run.exists_rankedCover hσ'
  subst h
  subst z
  subst w
  exact ⟨centers, hcenters⟩

/-- The reserve invariant supplies the width and cube hypotheses at the current state.
@isnad1 id=and.4h5v.s8.e7cb043086e1 from=translated src=- shape=7055599d vocab=77d66391
-/
theorem shelf_state_bounds_of_reserve {w₀ z₀ z w : ℕ} {E : ℝ}
    (hzle : z ≤ z₀)
    (hmargin :
      E + 30 * (w₀ : ℝ) * (z₀ : ℝ) ≤
        shelfPotential (w₀ : ℝ) (z₀ : ℝ))
    (hreserve :
      shelfPotential (w₀ : ℝ) (z₀ : ℝ) -
          30 * (w₀ : ℝ) * ((z₀ - z : ℕ) : ℝ) ≤
        shelfPotential (w : ℝ) (z : ℝ))
    (h144 :
      (144 : ℝ) ^ 3 ≤ (3 / 4 : ℝ) * E) :
    144 ≤ w ∧ 3 * z ^ 2 ≤ 4 * w ^ 3 := by
  have hgap : (((z₀ - z : ℕ) : ℝ)) ≤ (z₀ : ℝ) := by
    rw [Nat.cast_sub hzle]
    exact sub_le_self _ (Nat.cast_nonneg z)
  have hcurrent : E ≤ shelfPotential (w : ℝ) (z : ℝ) := by
    nlinarith [show 0 ≤ (w₀ : ℝ) by positivity]
  have hcubeReal : 3 * (z : ℝ) ^ 2 ≤ 4 * (w : ℝ) ^ 3 := by
    rw [shelfPotential] at hcurrent
    nlinarith
  have hwidthCube : (144 : ℝ) ^ 3 ≤ (w : ℝ) ^ 3 :=
    h144.trans (cube_lower_of_shelfPotential_lower hcurrent)
  have hwidthReal : (144 : ℝ) ≤ (w : ℝ) :=
    (pow_le_pow_iff_left₀ (by norm_num) (Nat.cast_nonneg _)
      (by norm_num : (3 : ℕ) ≠ 0)).mp hwidthCube
  constructor
  · exact_mod_cast hwidthReal
  · exact_mod_cast hcubeReal

/--
Strong-induction construction of the finite shelf trajectory.  The reserve term records exactly
the portion of the accumulated `30 w₀ z₀` loss already spent.
@isnad1 id=hasshelf.5h6v.s7.9cc34984f95d from=translated src=- shape=3191f157 vocab=1bc22281
-/
theorem exists_hasShelfRun_of_reserve {w₀ z₀ h z w : ℕ} {E : ℝ}
    (hzle : z ≤ z₀) (hwle : w ≤ w₀)
    (hmargin :
      E + 30 * (w₀ : ℝ) * (z₀ : ℝ) ≤
        shelfPotential (w₀ : ℝ) (z₀ : ℝ))
    (hreserve :
      shelfPotential (w₀ : ℝ) (z₀ : ℝ) -
          30 * (w₀ : ℝ) * ((z₀ - z : ℕ) : ℝ) ≤
        shelfPotential (w : ℝ) (z : ℝ))
    (h144 :
      (144 : ℝ) ^ 3 ≤ (3 / 4 : ℝ) * E) :
    HasShelfRun h z w := by
  induction z using Nat.strong_induction_on generalizing h w with
  | h z ih =>
      have hstate :=
        shelf_state_bounds_of_reserve hzle hmargin hreserve h144
      have hw144 : 144 ≤ w := hstate.1
      have hcube : 3 * z ^ 2 ≤ 4 * w ^ 3 := hstate.2
      by_cases hapex : z ≤ w - 1
      · let H : ℕ → ℕ := fun _ ↦ h
        let Z : ℕ → ℕ := fun _ ↦ z
        let W : ℕ → ℕ := fun _ ↦ w
        let Q : ℕ → ℕ := fun _ ↦ 0
        refine ⟨0, H, Z, W, Q, rfl, rfl, rfl, ?_⟩
        refine {
          width := ?_
          cube := ?_
          tall := ?_
          least := ?_
          nonterminal := ?_
          h_next := ?_
          z_next := ?_
          w_next := ?_
          terminal := ?_
        }
        · intro i hi
          simpa [H] using hw144
        · intro i hi
          simpa [Z, W] using hcube
        · intro i hi
          omega
        · intro i hi hiTall
          simp only [Z, W] at hiTall
          omega
        · intro i hi
          omega
        · intro i hi
          omega
        · intro i hi
          omega
        · intro i hi
          omega
        · exact Or.inl (by simpa [Z, W] using hapex)
      · have htall : w - 1 < z := by omega
        obtain ⟨q, hleast⟩ := exists_isLeastShelfWidth hw144 hcube
        by_cases hfinal : z ≤ 2 * (w - q)
        · let H : ℕ → ℕ := fun _ ↦ h
          let Z : ℕ → ℕ := fun _ ↦ z
          let W : ℕ → ℕ := fun _ ↦ w
          let Q : ℕ → ℕ := fun _ ↦ q
          refine ⟨0, H, Z, W, Q, rfl, rfl, rfl, ?_⟩
          refine {
            width := ?_
            cube := ?_
            tall := ?_
            least := ?_
            nonterminal := ?_
            h_next := ?_
            z_next := ?_
            w_next := ?_
            terminal := ?_
          }
          · intro i hi
            simpa [W] using hw144
          · intro i hi
            simpa [Z, W] using hcube
          · intro i hi
            omega
          · intro i hi hiTall
            simpa [W, Z, Q] using hleast
          · intro i hi
            omega
          · intro i hi
            omega
          · intro i hi
            omega
          · intro i hi
            omega
          · exact Or.inr (by simpa [Z, W, Q] using hfinal)
        · have hnonterminal : 2 * (w - q) < z := by omega
          have hbounds := hleast.bounds hw144 hcube
          have hq2 : 2 ≤ q := hleast.1.1
          have hqhalf : 2 * q ≤ w := hleast.1.2.1
          have hqw : q < w := by omega
          let a := w - q
          let z' := z - 2 * a
          have haPos : 0 < a := by
            dsimp [a]
            omega
          have hz'lt : z' < z := by
            dsimp [z', a]
            omega
          have hz'le : z' ≤ z₀ := by
            dsimp [z']
            omega
          have haLe : a ≤ w₀ := by
            dsimp [a]
            exact (Nat.sub_le w q).trans hwle
          have hstep :=
            hleast.potential_update hw144 htall hcube hnonterminal
          have hquarter : 3 * w ≤ 4 * a := by
            dsimp [a]
            exact hbounds.2.2
          have herror :
              45 * (w : ℝ) ^ 2 ≤ 60 * (w₀ : ℝ) * (a : ℝ) := by
            have hwleReal : (w : ℝ) ≤ (w₀ : ℝ) := by exact_mod_cast hwle
            have hquarterReal : 3 * (w : ℝ) ≤ 4 * (a : ℝ) := by
              exact_mod_cast hquarter
            have hmul :
                (w : ℝ) * (w : ℝ) ≤ (w₀ : ℝ) * (w : ℝ) :=
              mul_le_mul_of_nonneg_right hwleReal (by positivity)
            have hscale :
                3 * ((w₀ : ℝ) * (w : ℝ)) ≤
                  4 * ((w₀ : ℝ) * (a : ℝ)) := by
              nlinarith [mul_nonneg (show 0 ≤ (w₀ : ℝ) by positivity)
                (sub_nonneg.mpr hquarterReal)]
            nlinarith
          have hgapNat :
              z₀ - z' = (z₀ - z) + 2 * a := by
            dsimp [z', a]
            omega
          have hgapReal :
              ((z₀ - z' : ℕ) : ℝ) =
                ((z₀ - z : ℕ) : ℝ) + 2 * (a : ℝ) := by
            exact_mod_cast hgapNat
          have hreserve' :
              shelfPotential (w₀ : ℝ) (z₀ : ℝ) -
                  30 * (w₀ : ℝ) * ((z₀ - z' : ℕ) : ℝ) ≤
                shelfPotential (a : ℝ) (z' : ℝ) := by
            dsimp [a, z'] at hstep ⊢
            rw [hgapReal]
            nlinarith
          obtain ⟨m, H, Z, W, Q, hH, hZ, hW, tail⟩ :=
            ih z' hz'lt (h := h + 2 * a) (w := a) hz'le haLe hreserve'
          refine
            ⟨m + 1, prependNat h H, prependNat z Z, prependNat w W,
              prependNat q Q, rfl, rfl, rfl, ?_⟩
          exact
            tail.prepend hw144 hcube htall hleast hnonterminal hH hZ hW

/-- Initial-state form of the trajectory existence theorem.
@isnad1 id=hasshelf.2h4v.s6.d646da2317e4 from=translated src=- shape=ed0ad1df vocab=2f42c50f
-/
theorem exists_hasShelfRun_of_initial_margin {h z w : ℕ} {E : ℝ}
    (hmargin :
      E + 30 * (w : ℝ) * (z : ℝ) ≤
        shelfPotential (w : ℝ) (z : ℝ))
    (h144 :
      (144 : ℝ) ^ 3 ≤ (3 / 4 : ℝ) * E) :
    HasShelfRun h z w := by
  apply exists_hasShelfRun_of_reserve (w₀ := w) (z₀ := z)
    (z := z) (w := w) le_rfl le_rfl hmargin
  · simp
  · exact h144

/-- The sharp two-token constant `(3/4)^(1/3)`.-/
noncomputable def shelfSharpConstant : ℝ :=
  (3 / 4 : ℝ) ^ (3 : ℝ)⁻¹

/-- The ideal initial width `(1+ε)cN^(2/3)`.-/
noncomputable def shelfIdealWidth (ε : ℝ) (N : ℕ) : ℝ :=
  (1 + ε) * shelfSharpConstant * shelfWidthScale N

/-- The ceiling of the ideal initial shelf width.-/
noncomputable def shelfInitialWidth (ε : ℝ) (N : ℕ) : ℕ :=
  ⌈shelfIdealWidth ε N⌉₊

/--
@isnad1 id=lt.0h0v.s3.5bd99c7e1875 from=translated src=- shape=ff3a10fc vocab=2ee3754e
-/
theorem shelfSharpConstant_pos :
    0 < shelfSharpConstant := by
  rw [shelfSharpConstant]
  apply Real.rpow_pos_of_pos
  norm_num

/--
@isnad1 id=eq.0h0v.s5.979bd1fc1708 from=translated src=- shape=bce64568 vocab=f83f9d35
-/
@[simp]
theorem shelfSharpConstant_pow_three :
    shelfSharpConstant ^ 3 = (3 / 4 : ℝ) := by
  simpa [shelfSharpConstant] using
    (Real.rpow_inv_natCast_pow (x := (3 / 4 : ℝ)) (n := 3)
      (by norm_num) (by norm_num))

/-- Equation (32): ceiling the ideal width can only increase the initial potential.
@isnad1 id=le.1h2v.s5.1ffb13681ff6 from=translated src=- shape=ac9c7f83 vocab=e66317a2
-/
theorem shelfPotential_initial_lower {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    shelfDelta ε * (N : ℝ) ^ 2 ≤
      shelfPotential (shelfInitialWidth ε N : ℝ) (N : ℝ) := by
  let target := shelfIdealWidth ε N
  have htarget : 0 ≤ target := by
    dsimp [target]
    rw [shelfIdealWidth]
    exact mul_nonneg (mul_nonneg (by linarith) shelfSharpConstant_pos.le)
      (shelfWidthScale_nonneg N)
  have hceil : target ≤ (shelfInitialWidth ε N : ℝ) := by
    exact Nat.le_ceil target
  have hpow :
      target ^ 3 ≤ (shelfInitialWidth ε N : ℝ) ^ 3 :=
    (pow_le_pow_iff_left₀ htarget (Nat.cast_nonneg _)
      (by norm_num : (3 : ℕ) ≠ 0)).2 hceil
  have htargetCube :
      target ^ 3 =
        (1 + ε) ^ 3 * (3 / 4 : ℝ) * (N : ℝ) ^ 2 := by
    dsimp [target]
    rw [shelfIdealWidth]
    rw [mul_pow, mul_pow, shelfSharpConstant_pow_three,
      shelfWidthScale_pow_three]
  rw [shelfPotential]
  rw [htargetCube] at hpow
  rw [shelfDelta]
  nlinarith

/--
@isnad1 id=tendsto.0h0v.s3.094d20c97296 from=translated src=- shape=d5274890 vocab=6ea9e57c
-/
theorem tendsto_shelfWidthScale_atTop :
    Tendsto (fun N : ℕ ↦ shelfWidthScale N) atTop atTop := by
  exact
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      tendsto_natCast_atTop_atTop

private theorem shelfWidthScale_div_natCast {N : ℕ} (hN : 0 < N) :
    shelfWidthScale N / (N : ℝ) = (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hNReal : 0 < (N : ℝ) := by positivity
  have h := Real.rpow_sub hNReal (2 / 3 : ℝ) (1 : ℝ)
  norm_num [shelfWidthScale, Real.rpow_one] at h ⊢
  exact h.symm

/--
@isnad1 id=tendsto.0h0v.s5.1b66323c6977 from=translated src=- shape=15fb6055 vocab=aa5cec42
-/
theorem tendsto_shelfWidthScale_div_natCast :
    Tendsto (fun N : ℕ ↦ shelfWidthScale N / (N : ℝ)) atTop (𝓝 0) := by
  have h :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (shelfWidthScale_div_natCast hN).symm

/--
@isnad1 id=tendsto.1h1v.s4.ca166757c892 from=translated src=- shape=264d12bc vocab=105b8fe1
-/
theorem tendsto_shelfIdealWidth_atTop {ε : ℝ} (hε : 0 < ε) :
    Tendsto (shelfIdealWidth ε) atTop atTop := by
  have hcoefficient :
      0 < (1 + ε) * shelfSharpConstant :=
    mul_pos (by linarith) shelfSharpConstant_pos
  convert tendsto_shelfWidthScale_atTop.const_mul_atTop hcoefficient using 1
  funext N
  simp only [shelfIdealWidth]

/--
@isnad1 id=tendsto.0h1v.s5.8caafbe44e01 from=translated src=- shape=fa7fe8fc vocab=e7a18162
-/
theorem tendsto_shelfIdealWidth_div_natCast {ε : ℝ} :
    Tendsto (fun N : ℕ ↦ shelfIdealWidth ε N / (N : ℝ)) atTop (𝓝 0) := by
  have hconst :
      Tendsto (fun _ : ℕ ↦ (1 + ε) * shelfSharpConstant) atTop
        (𝓝 ((1 + ε) * shelfSharpConstant)) :=
    tendsto_const_nhds
  have h := hconst.mul tendsto_shelfWidthScale_div_natCast
  simpa only [shelfIdealWidth, mul_div_assoc, mul_zero] using h

/--
@isnad1 id=tendsto.1h1v.s5.5b900e6a1059 from=translated src=- shape=bf590e69 vocab=26750ca7
-/
theorem tendsto_shelfInitialWidth_div_natCast {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun N : ℕ ↦ (shelfInitialWidth ε N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  have hideal := tendsto_shelfIdealWidth_atTop hε
  have hceil :
      Tendsto
        (fun N : ℕ ↦
          (shelfInitialWidth ε N : ℝ) / shelfIdealWidth ε N)
        atTop (𝓝 1) := by
    simpa only [shelfInitialWidth, Function.comp_def] using
      (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hideal
  have hproduct :=
    hceil.mul (tendsto_shelfIdealWidth_div_natCast (ε := ε))
  have heq :
      (fun N : ℕ ↦
        ((shelfInitialWidth ε N : ℝ) / shelfIdealWidth ε N) *
          (shelfIdealWidth ε N / (N : ℝ))) =ᶠ[atTop]
        (fun N : ℕ ↦ (shelfInitialWidth ε N : ℝ) / (N : ℝ)) := by
    filter_upwards [hideal.eventually_gt_atTop 0, eventually_gt_atTop 0]
      with N hidealN hN
    field_simp [hidealN.ne', show (N : ℝ) ≠ 0 by positivity]
  simpa only [one_mul] using hproduct.congr' heq

/--
@isnad1 id=eventual.1h1v.s6.175ca47495f6 from=translated src=- shape=417ac41c vocab=ec80d35b
-/
theorem eventually_shelf_large_conditions {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      30 * (shelfInitialWidth ε N : ℝ) * (N : ℝ) ≤
          shelfDelta ε / 2 * (N : ℝ) ^ 2 ∧
        (144 : ℝ) ≤ shelfBeta ε * shelfWidthScale N := by
  have hratio := tendsto_shelfInitialWidth_div_natCast hε
  have hratioSmall :
      ∀ᶠ N : ℕ in atTop,
        (shelfInitialWidth ε N : ℝ) / (N : ℝ) <
          shelfDelta ε / 60 :=
    hratio.eventually
      (Iio_mem_nhds (div_pos (shelfDelta_pos hε) (by norm_num)))
  have hwidth :
      Tendsto (fun N : ℕ ↦ shelfBeta ε * shelfWidthScale N) atTop atTop :=
    tendsto_shelfWidthScale_atTop.const_mul_atTop (shelfBeta_pos hε)
  filter_upwards [hratioSmall, hwidth.eventually_ge_atTop 144,
      eventually_gt_atTop 0] with N hsmall hlarge hN
  constructor
  · have hNReal : 0 < (N : ℝ) := by positivity
    have hlinear :
        (shelfInitialWidth ε N : ℝ) <
          shelfDelta ε / 60 * (N : ℝ) :=
      (div_lt_iff₀ hNReal).mp hsmall
    nlinarith [shelfDelta_pos hε]
  · exact hlarge

private theorem shelfBeta_widthScale_cube {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (shelfBeta ε * shelfWidthScale N) ^ 3 =
      (3 / 4 : ℝ) * (shelfDelta ε / 2 * (N : ℝ) ^ 2) := by
  rw [mul_pow, shelfBeta_pow_three hε, shelfWidthScale_pow_three]
  ring

/-- The large-`N` inequalities from (33) produce the finite least-width shelf run.
@isnad1 id=hasshelf.3h2v.s7.1668588818f9 from=translated src=- shape=c362f993 vocab=e19e3d89
-/
theorem exists_hasShelfRun_of_large_conditions {ε : ℝ}
    (hε : 0 < ε) {N : ℕ}
    (hloss :
      30 * (shelfInitialWidth ε N : ℝ) * (N : ℝ) ≤
        shelfDelta ε / 2 * (N : ℝ) ^ 2)
    (hwidth :
      (144 : ℝ) ≤ shelfBeta ε * shelfWidthScale N) :
    HasShelfRun 0 N (shelfInitialWidth ε N) := by
  have hinitial := shelfPotential_initial_lower hε N
  have hmargin :
      shelfDelta ε / 2 * (N : ℝ) ^ 2 +
          30 * (shelfInitialWidth ε N : ℝ) * (N : ℝ) ≤
        shelfPotential (shelfInitialWidth ε N : ℝ) (N : ℝ) := by
    nlinarith
  have h144 :
      (144 : ℝ) ^ 3 ≤
        (3 / 4 : ℝ) * (shelfDelta ε / 2 * (N : ℝ) ^ 2) := by
    have hcube :=
      (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 144)
        (mul_nonneg (shelfBeta_pos hε).le (shelfWidthScale_nonneg N))
        (by norm_num : (3 : ℕ) ≠ 0)).2 hwidth
    rwa [shelfBeta_widthScale_cube hε] at hcube
  exact exists_hasShelfRun_of_initial_margin hmargin h144

/--
The trajectory furnished by the large-`N` conditions satisfies (31) at every
stage and the explicit shelf-count bound.
@isnad1 id=ex.3h2v.s8.e47ffc034d92 from=translated src=- shape=faafa08a vocab=f5659a38
-/
theorem exists_shelfRun_certificate_of_large_conditions {ε : ℝ}
    (hε : 0 < ε) {N : ℕ}
    (hloss :
      30 * (shelfInitialWidth ε N : ℝ) * (N : ℝ) ≤
        shelfDelta ε / 2 * (N : ℝ) ^ 2)
    (hwidth :
      (144 : ℝ) ≤ shelfBeta ε * shelfWidthScale N) :
    ∃ m : ℕ, ∃ H Z W Q : ℕ → ℕ,
      H 0 = 0 ∧ Z 0 = N ∧ W 0 = shelfInitialWidth ε N ∧
        ShelfRun m H Z W Q ∧
        (∀ j ≤ m,
          shelfDelta ε / 2 * (N : ℝ) ^ 2 ≤
              shelfPotential (W j : ℝ) (Z j : ℝ) ∧
            shelfBeta ε * shelfWidthScale N ≤ (W j : ℝ) ∧
              144 ≤ W j) ∧
        m + 1 ≤
          ⌈(2 / (3 * shelfBeta ε)) * (N : ℝ) ^ (1 / 3 : ℝ)⌉₊ + 1 := by
  obtain ⟨m, H, Z, W, Q, hH, hZ, hW, run⟩ :=
    exists_hasShelfRun_of_large_conditions hε hloss hwidth
  have hinitial := shelfPotential_initial_lower hε N
  have hmargin :
      shelfDelta ε / 2 * (N : ℝ) ^ 2 +
          30 * (W 0 : ℝ) * (Z 0 : ℝ) ≤
        shelfPotential (W 0 : ℝ) (Z 0 : ℝ) := by
    rw [hW, hZ]
    nlinarith
  have hN : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    rw [hN0] at hwidth
    norm_num [shelfWidthScale] at hwidth
  refine ⟨m, H, Z, W, Q, hH, hZ, hW, run, ?_, ?_⟩
  · intro j hj
    exact run.equation31 hε hmargin hj
  · exact run.shelf_count_explicit_bound hε hN hZ hmargin

/--
The two explicit large-`N` inequalities from (33) imply existence of the full
parity-triangle cover.
@isnad1 id=ex.4h3v.s7.11aaf7073369 from=translated src=- shape=dfa65a33 vocab=81bcdc95
-/
theorem exists_parityTriangleCover_of_large_conditions {ε : ℝ}
    (hε : 0 < ε) {N : ℕ} {σ : ℤ}
    (hσ : (N : ℕ) ≡ σ [ZMOD 2])
    (hloss :
      30 * (shelfInitialWidth ε N : ℝ) * (N : ℝ) ≤
        shelfDelta ε / 2 * (N : ℝ) ^ 2)
    (hwidth :
      (144 : ℝ) ≤ shelfBeta ε * shelfWidthScale N) :
    ∃ centers : Fin (shelfInitialWidth ε N) → ℤ × ℤ,
      IsParityCapRankedCover 0 N (shelfInitialWidth ε N) σ centers := by
  have hrun :
      HasShelfRun 0 N (shelfInitialWidth ε N) :=
    exists_hasShelfRun_of_large_conditions hε hloss hwidth
  exact hrun.exists_rankedCover (by simpa using hσ)

/--
For fixed `ε ∈ (0,1)`, all sufficiently large parity triangles have a
legal-center ranked cover of length `ceil((1+ε)cN^(2/3))`.
@isnad1 id=eventual.1h1v.s6.e8afdacecabe from=translated src=- shape=2e0f3796 vocab=acc787e6
-/
theorem eventually_exists_parityTriangleCover {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ N : ℕ in atTop,
      ∀ σ : ℤ, (N : ℕ) ≡ σ [ZMOD 2] →
        ∃ centers : Fin (shelfInitialWidth ε N) → ℤ × ℤ,
          IsParityCapRankedCover 0 N (shelfInitialWidth ε N) σ centers := by
  filter_upwards [eventually_shelf_large_conditions hε.1] with N hlarge
  intro σ hσ
  exact
    exists_parityTriangleCover_of_large_conditions hε.1 hσ
      hlarge.1 hlarge.2

/--
Threshold form of the global parity-triangle cover with an explicit
existential `N_ε`.
@isnad1 id=ex.1h1v.s6.312a107d9a8c from=translated src=- shape=de5fc925 vocab=3592b25c
-/
theorem exists_parityTriangleCover_threshold {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ Nε : ℕ, ∀ N ≥ Nε, ∀ σ : ℤ, (N : ℕ) ≡ σ [ZMOD 2] →
      ∃ centers : Fin (shelfInitialWidth ε N) → ℤ × ℤ,
        IsParityCapRankedCover 0 N (shelfInitialWidth ε N) σ centers := by
  exact eventually_atTop.1 (eventually_exists_parityTriangleCover hε)

end BurningPath
