import Tengoku.Erdos64.Erdos64.RootedDoubleDegreeOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The explicit data needed for the strict rooted-double branch.

This is a certificate interface, not an existence theorem: in particular it
does not package `IsStrictlySmallerCounterexample` or any minimality argument.-/
structure StrictRootedSideCertificate (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] where
  S : Finset V
  root : {v : V // v ∈ S}
  nonroot_closed : ∀ v, v ∈ S → v ≠ root.val →
    ∀ w, G.Adj v w → w ∈ S
  root_internal_degree : 2 ≤ internalDegree G S root.val
  side_degree : ∀ v, v ∈ S → 3 ≤ G.degree v
  strict_order : 2 * S.card - 1 < Fintype.card V

/-- The final proof boundary: either a dyadic cycle is already supplied, or
the strict-side certificate is supplied for the separate descent branch.

No theorem in this file claims that either branch can be constructed from
the ambient minimum-degree hypotheses.-/
inductive FinalDichotomyCertificate (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : Prop where
  | dyadicCycle (hcycle : HasPowerOfTwoCycle G) :
      FinalDichotomyCertificate G
  | strictSide (side : StrictRootedSideCertificate G) :
      FinalDichotomyCertificate G

/-- Certified degree and order consequences for the strict-side branch.-/
theorem StrictRootedSideCertificate.rootedDouble_degree_order
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (side : StrictRootedSideCertificate G) :
    (∀ (b : Bool) (v : {v : (↑side.S : Set V) // v ≠ side.root}),
      3 ≤ (rootedDoubleGraph (G.induce (↑side.S : Set V)) side.root).degree
        (some (b, v))) ∧
    4 ≤ (rootedDoubleGraph (G.induce (↑side.S : Set V)) side.root).degree none ∧
    Fintype.card (RootedDoubleVertex (↑side.S : Set V) side.root) =
      2 * side.S.card - 1 ∧
    Fintype.card (RootedDoubleVertex (↑side.S : Set V) side.root) <
      Fintype.card V := by
  exact rootedDouble_degree_order_interface side.S side.root
    side.nonroot_closed side.root_internal_degree side.side_degree
    side.strict_order

end Erdos64
