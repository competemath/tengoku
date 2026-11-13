import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellRolleCount
import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellDescartes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/WuProver/lean-commutator@2f197491d436, `CommutatorTheorem/Epsilon/BTFellTaylorCount.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Taylor translation and half-line root counts

Translation by a threshold turns roots to its right into positive roots.
This file provides the exact multiset identity needed to connect the
half-line count used by the Fell reduction with coefficient-side tools such
as Descartes' rule of signs.
-/

open scoped Polynomial

namespace CommutatorTheorem.BTFellTaylorCount

open Polynomial
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellCrossGap
open CommutatorTheorem.BTFellRolleCount

/-- Taylor translation subtracts the center from every root of a monic
real-rooted polynomial, preserving multiplicities.-/
theorem roots_taylor_eq_map_sub
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) (x : ℝ) :
    (p.taylor x).roots = p.roots.map (fun r ↦ r - x) := by
  have htranslate : ∀ roots : Multiset ℝ,
      ((roots.map (fun r ↦ X - C r)).prod).taylor x =
        (roots.map (fun r ↦ X - C (r - x))).prod := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons r roots ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons]
        rw [taylor_mul, ih]
        congr 1
        simp only [map_sub, taylor_X, taylor_C]
        ring
  have hprod : p = (p.roots.map (fun r ↦ X - C r)).prod :=
    hreal.eq_prod_roots_of_monic hmonic
  have htaylor : p.taylor x =
      (p.roots.map (fun r ↦ X - C (r - x))).prod := by
    calc
      p.taylor x =
          ((p.roots.map (fun r ↦ X - C r)).prod).taylor x :=
        congrArg (fun f : ℝ[X] ↦ f.taylor x) hprod
      _ = _ := htranslate p.roots
  rw [htaylor]
  let translated : Multiset ℝ := p.roots.map (fun r ↦ r - x)
  simpa only [translated, Multiset.map_map, Function.comp_apply] using
    (roots_multiset_prod_X_sub_C translated)

/-- The number of roots strictly to the right of `x` is exactly the number
of positive roots of the Taylor translate at `x`.-/
theorem rootsGTCount_eq_taylor_roots_countP_pos
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) (x : ℝ) :
    rootsGTCount p x = (p.taylor x).roots.countP (0 < ·) := by
  rw [rootsGTCount, roots_taylor_eq_map_sub hmonic hreal]
  rw [Multiset.countP_map]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro r hr
  simp only [sub_pos]

/-- Descartes' rule now gives a coefficient-side upper bound for the exact
half-line root count.-/
theorem rootsGTCount_le_signVariations_taylor
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) (x : ℝ) :
    rootsGTCount p x ≤ (p.taylor x).signVariations := by
  rw [rootsGTCount_eq_taylor_roots_countP_pos hmonic hreal]
  exact roots_countP_pos_le_signVariations (p.taylor x)

/-- Descartes' bound is exact when every root is positive.  This extreme
threshold case combines real-rootedness (all degree-many roots are present)
with the general degree upper bound for sign variations.-/
theorem signVariations_eq_natDegree_of_all_roots_pos
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p)
    (hpos : ∀ r ∈ p.roots, 0 < r) :
    p.signVariations = p.natDegree := by
  have hcount : p.roots.countP (0 < ·) = p.roots.card := by
    rw [Multiset.countP_eq_card]
    intro r hr
    exact hpos r hr
  apply le_antisymm
  · exact CommutatorTheorem.BTFellDescartes.signVariations_le_natDegree p
  · rw [hreal.natDegree_eq_card_roots, ← hcount]
    exact roots_countP_pos_le_signVariations p

/-- Consequently the Taylor/Descartes count is exact for a threshold lying
strictly below every root.-/
theorem rootsGTCount_eq_signVariations_taylor_of_lt_all_roots
    {p : ℝ[X]} (hmonic : p.Monic) (hreal : RealRooted p) {x : ℝ}
    (hx : ∀ r ∈ p.roots, x < r) :
    rootsGTCount p x = (p.taylor x).signVariations := by
  have htmonic : (p.taylor x).Monic := by
    rw [Monic, leadingCoeff_taylor]
    exact hmonic
  have htreal : RealRooted (p.taylor x) := by
    change (p.taylor x).Splits
    apply splits_iff_card_roots.mpr
    rw [roots_taylor_eq_map_sub hmonic hreal]
    simp [natDegree_taylor, hreal.natDegree_eq_card_roots]
  have htpos : ∀ r ∈ (p.taylor x).roots, 0 < r := by
    rw [roots_taylor_eq_map_sub hmonic hreal]
    intro r hr
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hr
    exact sub_pos.mpr (hx y hy)
  rw [rootsGTCount_eq_taylor_roots_countP_pos hmonic hreal]
  rw [signVariations_eq_natDegree_of_all_roots_pos htmonic htreal htpos]
  calc
    (p.taylor x).roots.countP (0 < ·) = (p.taylor x).roots.card := by
      rw [Multiset.countP_eq_card]
      exact fun r hr ↦ htpos r hr
    _ = (p.taylor x).natDegree := htreal.natDegree_eq_card_roots.symm

end CommutatorTheorem.BTFellTaylorCount
