import Tengoku.Seed.RingTheory.HopkinsLevitzki
import Tengoku.Seed.RingTheory.Ideal.Quotient.Index
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsArtinianRing_finite_of_finite_residueField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsArtinianRing_finite_of_finite_residueField

/--
@isnad1 id=finite.0h1v.s4.a32214f2b2f9 from=translated src=- shape=8bfb1a0d vocab=725246ad
-/
theorem solution (R : Type*) [CommRing R] [IsArtinianRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  have h1 : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›
  have h2 : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv
