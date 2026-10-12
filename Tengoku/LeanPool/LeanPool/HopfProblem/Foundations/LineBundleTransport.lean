/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import Tengoku.LeanPool.LeanPool.HopfProblem.Prelude
public import Tengoku.LeanPool.LeanPool.HopfProblem.Foundations.Core1
import all Tengoku.LeanPool.LeanPool.HopfProblem.Uniformization.HolomorphicCousin
import all Tengoku.LeanPool.LeanPool.HopfProblem.Foundations.Core1

/-!
# Hopf problem: foundations · line bundle transport

Supporting definitions and proofs for this stage of the six-sphere construction.
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem
    LineBundleTransport.exists_smooth_cutoff_near_closed {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
        tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ Set.EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : Set.univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
    · exact Set.mem_iUnion.mpr ⟨Bool.true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed (modelWithCornersSelf ℝ E)
      O hOo hOc Bool.false hK hKU
  exact ⟨ρ Bool.false, (ρ Bool.false).contMDiff.contDiff, hρ Bool.false, W, hWo, hKW, hWU, hρone⟩

public

end Mathoverflow1973

end
