import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ExtEndgame_ProductionDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ExtCitation_liesOverPrime_primeLocalPlace.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ExtCitation_liesOverPrime_primeLocalPlace

set_option autoImplicit false

open ExtCitation

namespace P2mS17LOP

/--
@isnad1 id=iff.0h5v.s7.a3fb00a7f70d from=translated src=- shape=4c39380b vocab=dc9359c5
-/
theorem mem_nonunits_comap {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

open scoped NNReal in
/--
@isnad1 id=liesover.0h1v.s4.3f5074e157b0 from=translated src=- shape=025085eb vocab=9ff962aa
-/
theorem padicPlace_liesOverPrime (q : ℕ) [Fact q.Prime] : (padicPlace q).LiesOverPrime q := by
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / (q : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ q := (Fact.out : q.Prime).two_le
  rw [ValuationSubring.LiesOverPrime, padicPlace, mem_nonunits_comap, ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((padicEmbedding q) (q : AlgebraicClosure ℚ)) < 1
  rw [map_natCast, hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

end P2mS17LOP

/--
@isnad1 id=liesover.0h1v.s4.47951e5446ba from=translated src=- shape=069d1425 vocab=a1a869e7
-/
theorem solution (q : Nat.Primes) : (primeLocalPlace q).LiesOverPrime q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact P2mS17LOP.padicPlace_liesOverPrime q
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
