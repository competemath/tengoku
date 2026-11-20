import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.FiniteObstruction
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.AngularBins
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Grouping
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Budget

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set Filter
namespace Erdos1133

/-- The complete finite reduction. The analytic obstruction is displayed as
an assumption of this intermediate theorem; it is not an axiom.-/
theorem robust_labels_of_finite_obstruction {C : ℝ} {k n : ℕ}
    (hk : 2 ≤ k) (hn : 4*k^2 ≤ n) (hcore : FiniteBernsteinObstruction C k)
    (x : Fin n → Icc (-1 : ℝ) 1) :
    ∃ y : Fin n → Icc (-1 : ℝ) 1,
      ∀ P : Polynomial ℝ, (P.natDegree : ℝ) < (1 + obstructionEpsilon k) * (n : ℝ) →
      ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
        (1 - obstructionEpsilon k) * (n : ℝ) →
      ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C := by
  classical
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hn0 : 0 < n := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let D : ℝ := (1 + obstructionEpsilon k) * n
  have hD : 0 < D := mul_pos (by linarith [obstructionEpsilon_pos hk]) hnR
  let N := binCount D ((k : ℝ) + 1)
  have hL : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  let t : Fin n → Icc 0 D := fun i => ⟨angularNode D (x i), angularNode_mem hD.le (x i)⟩
  let b : Fin n → Fin N := fun i => angularBin hL (t i)
  obtain ⟨G,hG,hdis,hcount⟩ := exists_grouping_by_bins Finset.univ b k hk0
  have hcount' : n ≤ k * G.card + k * N := by
    have hh : n ≤ k * G.card + (k-1) * N := by simpa using hcount
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul_right N (Nat.sub_le k 1)) _)
  have hq : obstructionEpsilon k * (n : ℝ) < G.card := by
    apply robust_group_budget hk hn
    have hbN : (N : ℝ) ≤ D / ((k : ℝ) + 1) + 1 := binCount_le hD.le hL
    have hc : (n : ℝ) ≤ (k : ℝ) * G.card + (k : ℝ) * N := by exact_mod_cast hcount'
    have hd : (n : ℝ) / k ≤ (G.card : ℝ) + N := by
      apply (div_le_iff₀ hkR).mpr
      nlinarith
    dsimp only [D] at hbN
    linarith
  have hlab (g : G) : ∃ a : Fin n → ℝ, (∀ i, |a i| ≤ 1) ∧
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi C f →
        ∃ i ∈ g.val, f (t i) ≠ (a i : ℂ) := by
    obtain ⟨hgs,hgcard,j,hj⟩ := hG g.val g.property
    apply finiteObstruction_group hcore g.val hgcard (fun i => (t i : ℝ)) (j.val * ((k : ℝ)+1))
    intro i hi
    have hb := angularBin_bounds hL (t i)
    have hij : angularBin hL (t i) = j := hj i hi
    rw [hij] at hb
    convert hb using 1 <;> ring
  choose a ha hbad using hlab
  let a' : Finset (Fin n) → Fin n → ℝ := fun g i =>
    if hg : g ∈ G then a ⟨g,hg⟩ i else 0
  obtain ⟨y,hy,hyg⟩ := glue_group_labels G hdis a' (by
    intro g hg i hi
    simpa [a',hg] using ha ⟨g,hg⟩ i)
  refine ⟨fun i => ⟨y i, abs_le.mp (hy i)⟩, ?_⟩
  intro P hdeg hfit
  by_contra hno
  have hbounded : BoundedOnSegment C P := by
    intro z hz
    exact le_of_not_gt (fun h => hno ⟨z,hz,h⟩)
  have hPB := polynomialPullback_isBernstein hD P hdeg.le hbounded
  have herr : G.card ≤ (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card := by
    apply groups_force_errors Finset.univ G (fun _ _ => Finset.subset_univ _) hdis
    intro g hg
    obtain ⟨i,hi,hne⟩ := hbad ⟨g,hg⟩ (polynomialPullback D P) hPB
    refine ⟨i,hi,?_⟩
    have hval : y i = a ⟨g,hg⟩ i := by simpa [a',hg] using hyg g hg i hi
    have heval := polynomialPullback_at_node hD P (x i)
    change polynomialPullback D P (angularNode D (x i)) ≠ _ at hne
    rw [heval] at hne
    intro he
    apply hne
    exact congrArg (fun r : ℝ => (r : ℂ)) (he.trans hval)
  have hpartition :
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card +
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card = n := by
    simpa using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => P.eval (x i : ℝ) = y i)
  have hpartitionR :
      ((Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card : ℝ) +
      ((Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card : ℝ) = n := by
    exact_mod_cast hpartition
  have herrR : (G.card : ℝ) ≤
      (Finset.univ.filter (fun i => P.eval (x i : ℝ) ≠ y i)).card := by exact_mod_cast herr
  change ((Finset.univ.filter (fun i => P.eval (x i : ℝ) = y i)).card : ℝ) ≥ _ at hfit
  nlinarith

end Erdos1133
