import Tengoku.PaperCLean.PaperC.Arithmetic.DefectParitySupport
import Tengoku.PaperCLean.PaperC.Arithmetic.PrimesUpTo
import Tengoku.PaperCLean.PaperC.Combinatorics.LargePrimeComponents
import Tengoku.PaperCLean.PaperC.Combinatorics.LargePrimeGraphResolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Prime-parity support of one large-prime component

Section 8 attaches to every residual component the parity vector of the
product of all integer labels carried by that component.  The large-prime
graph already makes every coordinate above the cutoff vanish.  Consequently
all nonzero coordinates of this product occur in the canonical list of
primes at most `L + 1`.

This file packages that fact in the exact form consumed by the binary
component code.  It does not use the alignment channel.
-/

namespace PaperC
namespace ComponentProductParity

open scoped BigOperators
open LargePrimeComponents
open LargePrimeGraph
open LargePrimeOccurrences

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-- Product of the positive complete-boundary labels in one component.-/
noncomputable def componentVertexProduct
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) : ℕ :=
  ∏ v ∈ componentVertices x y L C,
    Affine.twoStartCompleteVertexLabel x y L v

/--
The finset presentation of a component's vertices is canonically equivalent
to the support subtype carried by the graph quotient.-/
noncomputable def componentVerticesEquivSupp
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    {v : Occurrence L // v ∈ componentVertices x y L C} ≃ C.supp where
  toFun v :=
    ⟨v.1,
      (SimpleGraph.ConnectedComponent.mem_supp_iff C v.1).2
        (mem_componentVertices.mp v.2)⟩
  invFun v :=
    ⟨v.1,
      mem_componentVertices.mpr
        ((SimpleGraph.ConnectedComponent.mem_supp_iff C v.1).1 v.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Cardinality of the finset and support presentations agree.
@isnad1 id=eq.0h4v.s7.fad5abdcaea5 from=translated src=- shape=7ea635f0 vocab=adc84652
-/
theorem card_componentVertices
    (x y L : ℕ)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    (componentVertices x y L C).card = Fintype.card C.supp := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (componentVerticesEquivSupp x y L C)

/--
The graph-resolution notion of an unpinned component implies the literal
absence of a pinned occurrence used by the component-product lemmas.
@isnad1 id=not.1h4v.s7.b36870ae1366 from=translated src=- shape=c8813fdd vocab=c5ae1364
-/
theorem not_isPinnedComponent_of_isNontrivialUnpinned
    {x y L : ℕ}
    {C : (largePrimeGraph x y L).ConnectedComponent}
    (hC :
      PinnedGraphResolution.IsNontrivialUnpinnedComponent
        (largePrimeGraph x y L)
        (LargePrimeGraphResolution.pinnedVertices x y L) C) :
    ¬IsPinnedComponent x y L C := by
  intro hpinned
  obtain ⟨v, hvC, hvPinned⟩ := hpinned
  apply hC.1
  exact
    ⟨v,
      LargePrimeGraphResolution.mem_pinnedVertices.mpr hvPinned,
      mem_componentVertices.mp hvC⟩

/-- Every factor occurring in `componentVertexProduct` is positive.
@isnad1 id=lt.3h5v.s6.4be3b1832221 from=translated src=- shape=cdb38f00 vocab=030f01ac
-/
theorem componentVertexLabel_pos
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    {v : Occurrence L}
    (hv : v ∈ componentVertices x y L C) :
    0 < Affine.twoStartCompleteVertexLabel x y L v := by
  apply componentLabels_pos hx hy C
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- The component product is nonzero (indeed positive).
@isnad1 id=lt.2h4v.s5.d8ef74f477e9 from=translated src=- shape=1b7c7ea2 vocab=3fc17d09
-/
theorem componentVertexProduct_pos
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent) :
    0 < componentVertexProduct x y L C := by
  unfold componentVertexProduct
  exact Finset.prod_pos fun v hv ↦
    componentVertexLabel_pos hx hy C hv

/--
Every prime above the complete-boundary cutoff has even valuation in the
product of an unpinned component.
@isnad1 id=eq.5h5v.s7.390cf7de268a from=translated src=- shape=fdfaf85a vocab=584bb633
-/
theorem componentVertexProduct_large_parity_eq_zero
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬IsPinnedComponent x y L C)
    (p : ℕ) (hp : p.Prime) (hpL : L + 1 < p) :
    parityVec (componentVertexProduct x y L C) p = 0 := by
  have hnonzero :
      ∀ v ∈ componentVertices x y L C,
        Affine.twoStartCompleteVertexLabel x y L v ≠ 0 := by
    intro v hv
    exact (componentVertexLabel_pos hx hy C hv).ne'
  have hprod :=
    DFunLike.congr_fun
      (parityVec_prod
        (componentVertices x y L C)
        (Affine.twoStartCompleteVertexLabel x y L)
        hnonzero)
      p
  calc
    parityVec (componentVertexProduct x y L C) p =
        (∑ v ∈ componentVertices x y L C,
          parityVec
            (Affine.twoStartCompleteVertexLabel x y L v)) p := by
      simpa only [componentVertexProduct] using hprod
    _ =
        ∑ v ∈ componentVertices x y L C,
          parityVec
            (Affine.twoStartCompleteVertexLabel x y L v) p := by
      rw [Finsupp.finsetSum_apply]
    _ = 0 :=
      component_large_parity_eq_zero
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        C hfree p ⟨hp, hpL⟩

/--
Every nonzero coordinate of a component-product parity vector is represented
by the canonical enumeration of primes at most `L + 1`.
@isnad1 id=ex.4h5v.s7.c8dc260772eb from=translated src=- shape=e7c2a927 vocab=17789008
-/
theorem componentVertexProduct_smallPrime_coverage
    {x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (C : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬IsPinnedComponent x y L C)
    (p : ℕ)
    (hp : parityVec (componentVertexProduct x y L C) p ≠ 0) :
    ∃ j : Fin (PrimesUpTo.count (L + 1)),
      PrimesUpTo.smallPrime (L + 1) j = p := by
  have hpPrime : p.Prime :=
    DefectParitySupport.prime_of_parityVec_ne_zero hp
  have hpLe : p ≤ L + 1 := by
    by_contra hnot
    have hpLarge : L + 1 < p := by omega
    exact hp
      (componentVertexProduct_large_parity_eq_zero
        hx hy C hfree p hpPrime hpLarge)
  exact PrimesUpTo.exists_smallPrime_eq_of_prime_le hpPrime hpLe

end

end ComponentProductParity
end PaperC
