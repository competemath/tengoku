import Tengoku.FltAnthropic.Definitions.Def_LatticeTreeBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem LT.LatticeTree.nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (m : ℕ) (hm : 1 ≤ m)
    (h : (∃ x : LT.LatticeTree.Vertex R K, (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x = x) ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₀ = x₁ ∧ (LT.LatticeTree.Vertex.twistedAct δ σ)^[m] x₁ = x₀) :
    (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty ∨
      ∃ x₀ x₁ : LT.LatticeTree.Vertex R K,
        LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁ ∧ x₀ ≠ x₁ ∧
          LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁ ∧ LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀ := by exact @_root_.P2MW.S_LT_LatticeTree_nonempty_twistedFixedVertexSet_or_exists_swap_of_iterate_twistedAct.solution R K _ _ _ _ _ _ ϖ hϖ σ δ m hm h
