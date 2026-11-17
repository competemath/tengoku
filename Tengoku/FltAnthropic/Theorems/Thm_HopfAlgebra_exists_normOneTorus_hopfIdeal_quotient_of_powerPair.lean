import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
/--
@isnad1 id=ex.10h7v.s14.0dd2c7d291d8 from=translated src=- shape=64623a1f vocab=2bc1bed1
-/
theorem HopfAlgebra.exists_normOneTorus_hopfIdeal_quotient_of_powerPair
    (K : Type) [Field K] (c : K)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (P Q : B₀)
    (hrelPQ : P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1)
    (hcP : Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q))
    (hcQ : Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P)
    (hεP : Coalgebra.counit (R := K) P = 1)
    (hεQ : Coalgebra.counit (R := K) Q = 0) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A) (π : B₀ →ₐ[K] A),
        π u₀ = u' ∧ π v₀ = v' ∧ π P = 1 ∧ π Q = 0 ∧
        (∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
          ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g) ∧
        (Algebra.adjoin K {u', v'} = ⊤) ∧
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') := by exact @_root_.P2MW.S_HopfAlgebra_exists_normOneTorus_hopfIdeal_quotient_of_powerPair.solution K _ c B₀ _ _ hcc₀ u₀ v₀ hgen₀ hrel₀ hcu₀ hcv₀ P Q hrelPQ hcP hcQ hεP hεQ
