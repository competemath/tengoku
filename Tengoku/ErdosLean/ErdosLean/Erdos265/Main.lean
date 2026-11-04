import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.SquareRec
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.QuadLimit
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.LogBound
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.ResidualLower
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.ResidualUpper
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.ExpGrowth
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.TailRegular
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.MajorantVanish
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.BlockApprox
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.NestedBoxes
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.SeqAssembly
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.DoubleExp
import Tengoku.ErdosLean.ErdosLean.Erdos265.Parts.Conversions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős Problem 265 (JSP-000229): main theorem

Assembly of the parts:
* `growth_half` — Kovač–Tao construction (arXiv:2406.17593 v4, Theorem 2.8 / Corollary 2.9,
  §7, `d = 2`), with modified parameters `N_k = 4^{m_k}` and `β = 51/50`;
* `barrier_half` — every admissible sequence has `log aₙ / 2ⁿ → 0`: an independent Lean
  formalisation of Kitamura's argument (tail envelope and second residual); the mathematics
  of this half is due to K. Kitamura;
* `erdos_265 : Erdos265Statement`, i.e. `51/50 ≤ β* ≤ 2` for the optimal exponent `β*`,
  which remains open.
-/

open Filter Topology

namespace Erdos265

/-- **Growth half** (Kovač–Tao).  An admissible sequence with `aₙ^{1/(51/50)ⁿ} → ∞`.
@isnad1 id=ex.0h0v.s6.2122b003913b from=translated src=- shape=cae4b470 vocab=fe8a5f1d
-/
theorem growth_half : ∃ a : ℕ → ℕ, IsRationalPair a ∧
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1 : ℝ) / (51 / 50 : ℝ) ^ n)) atTop atTop := by
  obtain ⟨hs1, hs2⟩ := center_summable
  have hr1 := rad1_pos 0
  have hr2 := rad2_pos 0
  obtain ⟨q1, hq1l, hq1r⟩ := exists_rat_btwn
    (show ∑' k, (center k).1 - rad1 0 < ∑' k, (center k).1 + rad1 0 by linarith)
  obtain ⟨q2, hq2l, hq2r⟩ := exists_rat_btwn
    (show ∑' k, (center k).2 - rad2 0 < ∑' k, (center k).2 + rad2 0 by linarith)
  have hx1 : |((q1 : ℝ), (q2 : ℝ)).1 - ∑' k, (center k).1| ≤ rad1 0 :=
    abs_le.2 ⟨by simp only; linarith, by simp only; linarith⟩
  have hx2 : |((q1 : ℝ), (q2 : ℝ)).2 - ∑' k, (center k).2| ≤ rad2 0 :=
    abs_le.2 ⟨by simp only; linarith, by simp only; linarith⟩
  obtain ⟨c, hadm, h1, h2⟩ := nested_boxes blockVal Adm center rad1 rad2 hs1 hs2
    rad1_tendsto rad2_tendsto (fun _ _ hi ↦ blockVal_nonneg hi)
    (fun k δ h1 h2 ↦ by
      obtain ⟨c, hc, e1, e2⟩ := block_approx k δ h1 h2
      exact ⟨c, hc, e1.trans (step_rad1 k), e2.trans (step_rad2 k)⟩)
    ((q1 : ℝ), (q2 : ℝ)) hx1 hx2
  exact ⟨seqOf c, isRationalPair_of_blocks hadm h1 h2, seqOf_double_exp hadm⟩

end Erdos265
