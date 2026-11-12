import Tengoku.AbelFormalization.AbelFormalization.FiniteWeightNoetherianDescent
import Tengoku.AbelFormalization.AbelFormalization.PolynomialWindowDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Noetherian stabilization in a bounded polynomial window

The bounded ordinary-degree window is the finite product of its grouped
lexicographic weight pieces.  Their coordinatewise finiteness lets us apply
the Noetherian finite-weight stabilization theorem over any coefficient ring
with a finite upper bound on Krull dimension.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n r h : ℕ}
variable (G : PolynomialGradedLexData n r h)

/-- Direct specialization of Noetherian finite-weight stabilization to the
ordered grouped pieces of one bounded polynomial window.
@isnad1 id=ex.3h9v.s15.f9642be0e628 from=translated src=- shape=57edeb39 vocab=166612c2
-/
theorem PolynomialGradedLexData.exists_windowOrderedWeightDescent_stabilizes_of_krullDimLE
    (d : ℕ) [IsNoetherianRing B] [Ring.KrullDimLE d B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J :
      ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
        ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i))
    (htri : ∀ i (v : G.orderedWeightPiece B hpositive D i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive D)
          (fun i : Fin (G.weightCount hpositive D) =>
            G.orderedWeightPiece B hpositive D i) i.val
          (J (Pi.single i v)))
    (N₀ : Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
          finiteWeightDescentIterate J N₀ j₀ ∧
        ∀ j, j₀ ≤ j →
          finiteWeightDescentIterate J N₀ j =
            finiteWeightDescentIterate J N₀ j₀ := by
  let _ : ∀ i : Fin (G.weightCount hpositive D),
      Module.Finite B (G.orderedWeightPiece B hpositive D i) :=
    fun i => G.orderedWeightPiece_moduleFinite
      (B := B) hpositive D i
  exact exists_finiteWeightDescent_stabilizes_of_krullDimLE
    (R := B)
    (n := G.weightCount hpositive D)
    (M := fun i : Fin (G.weightCount hpositive D) =>
      G.orderedWeightPiece B hpositive D i)
    d J htri N₀ hN₀

end AbelFormalization
