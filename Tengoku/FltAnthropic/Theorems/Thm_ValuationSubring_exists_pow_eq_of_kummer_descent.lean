import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_pow_eq_of_kummer_descent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_pow_eq_of_kummer_descent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.9h6v.s11.3c83ed167306 from=translated src=- shape=8c5a8a76 vocab=bbe508cc
-/
theorem ValuationSubring.exists_pow_eq_of_kummer_descent
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [IsGalois K L] [CharZero L]
    (P : ValuationSubring L) (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P)
    (p q : ℕ) (hp : p.Prime) (hqp : q.Prime) (hpq : p ≠ q)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P)
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = (q : K))
    (hres : ∀ u : P.comap (algebraMap K L), IsUnit u →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)))
    (a : K) (ha : a ≠ 0) : ∃ b : K, b ^ p = a := by exact @_root_.P2MW.S_ValuationSubring_exists_pow_eq_of_kummer_descent.solution K L _ _ _ _ _ _ P hstab p q hp hqp hpq hq halg hroot hres a ha
