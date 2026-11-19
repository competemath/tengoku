import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockOrbit
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Core
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Feeding a quotient relation into the symmetric orbit product

The relation

    sum_i a_i g^i = 0 mod X^q

says that the image of `A(Y)` vanishes at the image of `g`.  Therefore the
mapped orbit product vanishes there as well.  This is the quotient-ring
analogue of the first half of the passage to equation (6.19) in LN97.
-/

/-- The quotient `F[X]/(X^q)` used in Lemma 6.46.  This is an abbreviation,
not an opaque type alias, so the `AdjoinRoot` commutative-ring instance is
visible to typeclass synthesis.-/
abbrev XCardQuotient (F : Type*) [Field F] [Fintype F] :=
  AdjoinRoot (X ^ Fintype.card F : Polynomial F)

/-- The canonical quotient map `F[X] -> F[X]/(X^q)`.-/
noncomputable def XCardMk (F : Type*) [Field F] [Fintype F] :
    Polynomial F →+* XCardQuotient F :=
  AdjoinRoot.mk (X ^ Fintype.card F : Polynomial F)

variable {F : Type*} [Field F] [Fintype F]

/--
@isnad1 id=eq.1h4v.s10.e0f29396b71c from=translated src=- shape=c8430279 vocab=7275b7c9
-/
theorem mapped_firstBlockPolynomial_eval_eq_zero
    {m : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F)
    (hrel :
      ∑ i : Fin m,
        (XCardMk F) (a i) *
          ((XCardMk F) g) ^ (i : ℕ) = 0) :
    Polynomial.eval ((XCardMk F) g)
      (Polynomial.map (XCardMk F)
        (firstBlockPolynomial a)) = 0 := by
  rw [map_firstBlockPolynomial]
  simpa [eval_firstBlockPolynomial] using hrel

/-- Abstract map/evaluation form of the orbit-product implication.

If the mapped first-block polynomial vanishes at `y`, then the mapped orbit
product vanishes there, because the `j = 0` factor is exactly the original
first-block polynomial.
@isnad1 id=eq.2h7v.s7.76ccc71ec763 from=translated src=- shape=e35043c5 vocab=cdc80afb
-/
theorem map_orbit_eval_zero_of_map_A_eval_zero
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    {m : ℕ}
    (phi : R →+* S)
    (zeta : R)
    (A : Polynomial R)
    (y : S)
    (hm : 0 < m)
    (hA : Polynomial.eval y (Polynomial.map phi A) = 0) :
    Polynomial.eval y
      (Polynomial.map phi (domainOrbitProduct m zeta A)) = 0 := by
  unfold domainOrbitProduct
  rw [Polynomial.eval_map]
  rw [Polynomial.eval₂_finsetProd]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hm)
  simpa [domainOrbitFactor, Polynomial.eval_map] using hA

end LN97
end MagicSquares
