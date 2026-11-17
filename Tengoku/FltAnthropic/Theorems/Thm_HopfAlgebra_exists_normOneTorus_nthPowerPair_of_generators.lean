import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
/--
@isnad1 id=ex.9h7v.s13.3792be9604a7 from=translated src=- shape=9220c679 vocab=e68371b7
-/
theorem HopfAlgebra.exists_normOneTorus_nthPowerPair_of_generators
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) :
    ∃ (P Q : B₀),
      (P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1) ∧
      (Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q)) ∧
      (Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P) ∧
      (Coalgebra.counit (R := K) P = 1) ∧
      (Coalgebra.counit (R := K) Q = 0) ∧
      (∀ f : B₀ →ₐ[K] AlgebraicClosure K,
        f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
        f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n) := by exact @_root_.P2MW.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators.solution K _ _ c hc hnsq n _ δ hδ B₀ _ _ hcc₀ u₀ v₀ hgen₀ hrel₀ hcu₀ hcv₀ hlift₀
