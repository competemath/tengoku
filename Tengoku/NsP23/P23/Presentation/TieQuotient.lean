import Tengoku.NsP23.P23.Presentation.TieNormalForm
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The three-variable single-tie quotient

This file identifies the independently defined principal tie ideal with the
kernel of normalized evaluation, then packages the resulting algebra
equivalence.  It deliberately does not mention the Run 13 border ideal.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The independently defined principal tie ideal is killed by normalized
evaluation.-/
theorem tieIdeal_le_polyToNormalAlg_ker :
    tieIdeal k a b c ≤
      RingHom.ker (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom := by
  apply Ideal.span_le.2
  intro f hf
  rw [Set.mem_singleton_iff.mp hf]
  exact RingHom.mem_ker.2 polyToNormalAlg_tiePolynomial

/-- A polynomial in the normalized-evaluation kernel lies in the principal
tie ideal.  The proof reduces by monic division and invokes injectivity only
on the symbolic x-reduced remainder.-/
theorem polyToNormalAlg_ker_le_tieIdeal :
    RingHom.ker (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom ≤
      tieIdeal k a b c := by
  intro f hf
  have hf0 : polyToNormalAlg (k := k) (a := a) (b := b) (c := c) f = 0 :=
    RingHom.mem_ker.1 hf
  have hdiff := sub_reducedRepresentative_mem_tieIdeal
    (k := k) (a := a) (b := b) (c := c) f
  have hdiff0 :
      polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
          (f - reducedRepresentative a b c f) = 0 :=
    RingHom.mem_ker.1 (tieIdeal_le_polyToNormalAlg_ker
      (k := k) (a := a) (b := b) (c := c) hdiff)
  have hrem0 :
      polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
          (reducedRepresentative a b c f) = 0 := by
    simpa only [map_sub, hf0, zero_sub, neg_eq_zero] using hdiff0
  have hrem : reducedRepresentative a b c f = 0 :=
    polyToNormalAlg_injective_on_reduced
      (reducedRepresentative_isReduced (k := k) (a := a) (b := b) (c := c) f) hrem0
  simpa [hrem] using hdiff

/-- Exact kernel theorem for the public polynomial map.-/
theorem polyToNormalAlg_ker :
    RingHom.ker (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)).toRingHom =
      tieIdeal k a b c := by
  apply le_antisymm
  · exact polyToNormalAlg_ker_le_tieIdeal
  · exact tieIdeal_le_polyToNormalAlg_ker

/-- Exact monomial reduction modulo the principal tie ideal.-/
theorem monomial_sub_normalMonomial_mem_tieIdeal (d : Fin 3 →₀ ℕ) (r : k) :
    MvPolynomial.monomial d r -
        MvPolynomial.monomial (normalExponent (normalizeExponent a b c d)) r ∈
      tieIdeal k a b c := by
  rw [← polyToNormalAlg_ker (k := k) (a := a) (b := b) (c := c)]
  apply RingHom.mem_ker.2
  simp

/-- The public quotient by the single tie polynomial.-/
abbrev TieQuotient (k : Type*) [Field k] (a b c : ℕ) [NeZero a] :=
  ThreePoly k ⧸ tieIdeal k a b c

/-- The single-tie polynomial quotient is exactly the normalized one-tie
monoid algebra.-/
def tieQuotientEquivNormalMonoidAlgebra :
    TieQuotient k a b c ≃ₐ[k] NormalMonoidAlgebra k a b c :=
  (Ideal.quotientEquivAlgOfEq k
      (polyToNormalAlg_ker (k := k) (a := a) (b := b) (c := c)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (polyToNormalAlg_surjective (k := k) (a := a) (b := b) (c := c)))

@[simp] theorem tieQuotientEquiv_mk (f : ThreePoly k) :
    tieQuotientEquivNormalMonoidAlgebra (k := k) (a := a) (b := b) (c := c)
        (Ideal.Quotient.mk _ f) =
      polyToNormalAlg (k := k) (a := a) (b := b) (c := c) f := by
  rfl

@[simp] theorem tieQuotientEquiv_polyX :
    tieQuotientEquivNormalMonoidAlgebra (k := k) (a := a) (b := b) (c := c)
        (Ideal.Quotient.mk _ polyX) =
      monomial (k := k) (Normal.xGenerator : Normal a b c) := by
  simp

@[simp] theorem tieQuotientEquiv_polyY :
    tieQuotientEquivNormalMonoidAlgebra (k := k) (a := a) (b := b) (c := c)
        (Ideal.Quotient.mk _ polyY) =
      monomial (k := k) (Normal.yGenerator : Normal a b c) := by
  simp

@[simp] theorem tieQuotientEquiv_polyZ :
    tieQuotientEquivNormalMonoidAlgebra (k := k) (a := a) (b := b) (c := c)
        (Ideal.Quotient.mk _ polyZ) =
      monomial (k := k) (Normal.zGenerator : Normal a b c) := by
  simp

@[simp] theorem tieQuotientEquiv_monomial (d : Fin 3 →₀ ℕ) (r : k) :
    tieQuotientEquivNormalMonoidAlgebra (k := k) (a := a) (b := b) (c := c)
        (Ideal.Quotient.mk _ (MvPolynomial.monomial d r)) =
      r • monomial (k := k) (normalizeExponent a b c d) := by
  simp

/-- Scope-explicit Run 14 presentation proposition.-/
def NormalMonoidAlgebraAsTieQuotient (k : Type*) [Field k]
    (a b c : ℕ) [NeZero a] : Prop :=
  Nonempty (TieQuotient k a b c ≃ₐ[k] NormalMonoidAlgebra k a b c)

/-- The normalized one-tie monoid algebra has the asserted single-binomial
three-variable presentation.-/
theorem normalMonoidAlgebra_as_tieQuotient :
    NormalMonoidAlgebraAsTieQuotient k a b c :=
  ⟨tieQuotientEquivNormalMonoidAlgebra⟩

end

end P23.Presentation
