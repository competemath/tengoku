import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.DualCoordinates

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
open scoped Classical

lemma rootPath_root (n : ℕ) : rootPath (root n)=lp.single 2 (root n) (1:ℝ) := by
  have he : pathNodes (root n)={root n} := by
    ext s
    simp [mem_pathNodes_iff,root,Subtype.ext_iff]
  simp only [rootPath,he,Finset.sum_singleton]

/-- The sharp root normalization for the quadratic cost, distinct from L_n. -/
theorem quadraticBlockCost_root (n : ℕ) :
    quadraticBlockCost n (lp.single 2 (root n) (1:ℝ))=1/Real.sqrt 2 := by
  apply le_antisymm _ (quadraticBlockCost_single_bounds (root n)).1
  let e : TreeHilbert n := lp.single 2 (root n) (1:ℝ)
  let μ : L1Mass (Tree n) := lp.single 1 (root n) (1/2:ℝ)
  have hn : ‖e‖=1 := by simp [e,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
  have hm : ‖μ‖=(1/2:ℝ) := by simp [μ,lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
  have hout : (1/2:ℝ) • e+pathSynthesis n μ=e := by
    rw [pathSynthesis_single,rootPath_root]
    change (1/2:ℝ) • e+(1/2:ℝ) • e=e
    module
  have hh := quadraticCost_representation_le (pathSynthesis n) ((1/2:ℝ) • e) μ
  rw [hout] at hh
  change quadraticBlockCost n e ≤ pairCost ((1/2:ℝ) • e) μ at hh
  apply hh.trans
  rw [pairCost,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),hn,hm]
  norm_num only [mul_one]
  have h2 : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have h22 : 0< Real.sqrt (2:ℝ) := by positivity
  have hs : Real.sqrt (((1/2:ℝ))^2+(1/2)^2)^2=(1/2:ℝ)^2+(1/2)^2 := Real.sq_sqrt (by positivity)
  apply (le_div_iff₀ h22).mpr
  nlinarith [Real.sqrt_nonneg (((1/2:ℝ))^2+(1/2)^2),
    sq_nonneg (Real.sqrt (((1/2:ℝ))^2+(1/2)^2)*Real.sqrt 2-1)]

namespace TreeCalculus
end TreeCalculus
end BoundedTreePotentials

namespace BoundedTreePotentials.CostHeads

end BoundedTreePotentials.CostHeads

namespace BoundedTreePotentials.Segments

end BoundedTreePotentials.Segments

end

end OAI
