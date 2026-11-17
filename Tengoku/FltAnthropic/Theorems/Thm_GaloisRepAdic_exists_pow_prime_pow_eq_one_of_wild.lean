import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.P2M.Sol.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false
open Polynomial

/--
@isnad1 id=ex.6h6v.s11.c4e734504643 from=translated src=- shape=9f55e6cb vocab=9174599e
-/
theorem Tengoku.FltAnthropic.GaloisRepAdic.exists_pow_prime_pow_eq_one_of_wild
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits) :
    ∃ k : ℕ, ρ.ρ σ ^ q ^ k = 1 := by exact @_root_.P2MW.S_GaloisRepAdic_exists_pow_prime_pow_eq_one_of_wild.solution A _ _ _ ρ p hp hpA q hq hqp P hP σ hwild
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
