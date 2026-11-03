import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.FrameIdeal
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.ResidualMatrices
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.ResidualTwoOrbit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms residualPairOfChart_actChart` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAutRelated_has_sourceAut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAutRelated_iff_related` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ChartResidualBaseSourceAutClassification` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The residual chart action as source Albert automorphisms

This module connects the chart-local residual matrices to the actual
determinant-one automorphisms of the structured source Albert algebra.  The
chart action changes the four vector columns and four covector rows and keeps
the diagonal and hyperbolic-plane data fixed.  Its residual projection is
exactly `X ↦ gX`, `A ↦ A gInv`, while both source encoders are transported by
the unital product automorphism `ResidualAction.sourceAut G`.

The capstone restates the accepted two-family residual classification in
terms of these source automorphisms.  It remains local to
`ExplicitFrameChart`; it does not assert that every frame has such a chart or
identify the displayed families with all orbits of a global Albert group.
-/

noncomputable section

namespace AlbertLean.Generic.ChartBridge

open Matrix
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Residual.FrameIdeal
open AlbertLean.Residual.ResidualMatrices
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.ResidualTwoOrbit
open AlbertLean.Generic

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Every residual source automorphism fixes every literal diagonal source
coordinate.  In particular it fixes each diagonal base idempotent, without
choosing an order or normalization for a third frame encoder.
@isnad1 id=eq.0h5v.s8.df9d232b6531 from=translated src=- shape=a10658a0 vocab=d11d8b6f
-/
@[simp] theorem sourceAut_diagonal
    (G : DetOneMatrix K) (d1 d2 d3 : K) :
    (ResidualAction.sourceAut G).linear
        (AlbertLean.Triality.StructuredCubic.diagonal d1 d2 d3) =
      AlbertLean.Triality.StructuredCubic.diagonal d1 d2 d3 := by
  apply JCoord.ext <;>
    simp [AlbertLean.Triality.StructuredCubic.diagonal,
      ResidualAction.sourceAut,
      ResidualAction.linearEquiv_apply, ResidualAction.act,
      ResidualAction.actV, ResidualAction.actS, ResidualAction.actC,
      ExteriorAction.vecAct, ExteriorAction.covAct] <;>
    rfl

/-- The seven-line residual projection of an explicit frame chart: four
covector rows and four vector columns in the specified order.-/
def residualPairOfChart (x : ExplicitFrameChart K) : ResidualPair K where
  A := AMatrix x.s1 x.s2 x.c1 x.c2
  X := XMatrix x.s1 x.s2 x.c1 x.c2

/-- Apply a determinant-one residual matrix to the source-coordinate fields
of an explicit chart.  The vector-plane and diagonal chart data are fixed.-/
def actChart (G : DetOneMatrix K) (x : ExplicitFrameChart K) :
    ExplicitFrameChart K where
  diagA := x.diagA
  diagB := x.diagB
  r1 := x.r1
  z1 := x.z1
  r2 := x.r2
  z2 := x.z2
  kappa := x.kappa
  s1 := ResidualAction.actS G x.s1
  s2 := ResidualAction.actS G x.s2
  c1 := ResidualAction.actC G x.c1
  c2 := ResidualAction.actC G x.c2

/-- Reinsert an arbitrary residual pair into the four row/column fields of a
chart while retaining all its other fields.-/
def chartWithResidualPair (x : ExplicitFrameChart K) (P : ResidualPair K) :
    ExplicitFrameChart K where
  diagA := x.diagA
  diagB := x.diagB
  r1 := x.r1
  z1 := x.z1
  r2 := x.r2
  z2 := x.z2
  kappa := x.kappa
  s1 := { p := fun i => P.X i 0, phi := fun j => P.A 0 j }
  s2 := { p := fun i => P.X i 1, phi := fun j => P.A 1 j }
  c1 := { q := fun i => P.X i 2, psi := fun j => P.A 2 j }
  c2 := { q := fun i => P.X i 3, psi := fun j => P.A 3 j }

/-- Reading the row/column fields just inserted into a chart recovers the
given residual pair exactly.
@isnad1 id=eq.0h3v.s5.cad7cbe3660f from=translated src=- shape=71ffb63e vocab=ab38ab0f
-/
@[simp] theorem residualPairOfChart_chartWithResidualPair
    (x : ExplicitFrameChart K) (P : ResidualPair K) :
    residualPairOfChart (chartWithResidualPair x P) = P := by
  apply ResidualPair.ext
  · funext i j
    fin_cases i <;> rfl
  · funext i j
    fin_cases j <;> rfl

/-- The residual projection intertwines the chart action with the accepted
explicit matrix-pair action.
@isnad1 id=eq.0h3v.s5.cf4499901f32 from=translated src=- shape=9837654e vocab=259b38e1
-/
theorem residualPairOfChart_actChart
    (G : DetOneMatrix K) (x : ExplicitFrameChart K) :
    residualPairOfChart (actChart G x) =
      AlbertLean.Residual.SL4PairAction.act G (residualPairOfChart x) := by
  apply ResidualPair.ext
  · funext i j
    fin_cases i <;>
      simp [residualPairOfChart, actChart, AMatrix, ResidualAction.actS,
        ResidualAction.actC, ExteriorAction.covAct,
        AlbertLean.Residual.SL4PairAction.act,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · funext i j
    fin_cases j <;>
      simp [residualPairOfChart, actChart, XMatrix, ResidualAction.actS,
        ResidualAction.actC, ExteriorAction.vecAct,
        AlbertLean.Residual.SL4PairAction.act,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The first chart encoder is transported by the same source action.
@isnad1 id=eq.0h3v.s5.0630ac95d840 from=translated src=- shape=9837654e vocab=4cced8d7
-/
theorem encoderA_actChart (G : DetOneMatrix K) (x : ExplicitFrameChart K) :
    encoderA (actChart G x) = ResidualAction.act G (encoderA x) := by
  apply JCoord.ext <;>
    simp [actChart, encoderA, vectorA, ResidualAction.act,
      ResidualAction.actV, ResidualAction.actS, ResidualAction.actC,
      ExteriorAction.wedgeAct_zero]

/-- The second chart encoder is transported by the same source action.
@isnad1 id=eq.0h3v.s5.e64b53635c70 from=translated src=- shape=9837654e vocab=6b608f01
-/
theorem encoderB_actChart (G : DetOneMatrix K) (x : ExplicitFrameChart K) :
    encoderB (actChart G x) = ResidualAction.act G (encoderB x) := by
  apply JCoord.ext <;>
    simp [actChart, encoderB, vectorB, ResidualAction.act,
      ResidualAction.actV, ResidualAction.actS, ResidualAction.actC,
      ExteriorAction.wedgeAct_zero]

/-- A residual target belongs to the displayed source-automorphism family of
a chart when one constructed unital source Albert automorphism fixes every
literal diagonal coordinate, transports both varying encoders, and has the
stated residual projection.  The local `α` is a proof-bearing `SourceAut`,
including unit and product preservation fields.-/
def SourceAutRelated (x : ExplicitFrameChart K) (Q : ResidualPair K) : Prop :=
  ∃ G : DetOneMatrix K,
    let α : ResidualAction.SourceAut (K := K) :=
      ResidualAction.sourceAut G
    residualPairOfChart (actChart G x) = Q ∧
      (∀ d1 d2 d3 : K,
        α.linear (diagonal d1 d2 d3) = diagonal d1 d2 d3) ∧
      α.linear (encoderA x) = encoderA (actChart G x) ∧
      α.linear (encoderB x) = encoderB (actChart G x)

/-- Every chart-family witness supplies an actual unital source Albert
automorphism transporting both source encoders and preserving the recovered
Springer product by its bundled `map_product` field.
@isnad1 id=ex.1h3v.s10.3d891657f6c9 from=translated src=- shape=47383939 vocab=7c83d4a1
-/
theorem sourceAutRelated_has_sourceAut
    {x : ExplicitFrameChart K} {Q : ResidualPair K}
    (h : SourceAutRelated x Q) :
    ∃ G : DetOneMatrix K,
      residualPairOfChart (actChart G x) = Q ∧
      (∀ d1 d2 d3 : K,
        (ResidualAction.sourceAut G).linear (diagonal d1 d2 d3) =
          diagonal d1 d2 d3) ∧
      (ResidualAction.sourceAut G).linear (encoderA x) =
        encoderA (actChart G x) ∧
      (ResidualAction.sourceAut G).linear (encoderB x) =
        encoderB (actChart G x) := by
  exact h

/-- The chart source-automorphism relation is exactly the accepted residual
`Related` relation after projection.
@isnad1 id=iff.0h3v.s5.0b662297f1e4 from=translated src=- shape=399db823 vocab=126cf893
-/
theorem sourceAutRelated_iff_related
    (x : ExplicitFrameChart K) (Q : ResidualPair K) :
    SourceAutRelated x Q ↔ Related (residualPairOfChart x) Q := by
  constructor
  · rintro ⟨G, hG, _, _, _⟩
    exact ⟨G, (residualPairOfChart_actChart G x).symm.trans hG⟩
  · rintro ⟨G, hG⟩
    refine ⟨G, (residualPairOfChart_actChart G x).trans hG,
      sourceAut_diagonal G, ?_, ?_⟩
    · exact (encoderA_actChart G x).symm
    · exact (encoderB_actChart G x).symm

/-- Capstone: on the accepted residual open with distinct determinant roots,
the entire residual base fibre is the disjoint union of two displayed
families induced by actual unital automorphisms of the structured source
Albert algebra.  The second representative is reinserted into the same
explicit chart coordinates.
@isnad1 id=other.2h2v.s7.76fd0deac48f from=translated src=- shape=9ec3ddf5 vocab=f00135fc
-/
theorem ChartResidualBaseSourceAutClassification
    (x : ExplicitFrameChart K)
    (hP : ResidualOpen (residualPairOfChart x))
    (hbranch : delta (residualPairOfChart x) ≠
      deltaStar (residualPairOfChart x)) :
    let P := residualPairOfChart x
    let Pswap := rootSwappedRepresentative P hP
    let xswap := chartWithResidualPair x Pswap
    residualPairOfChart xswap = Pswap ∧
      ∀ Q : ResidualPair K, ResidualOpen Q →
        (sameResidualBase P Q ↔
          SourceAutRelated x Q ∨ SourceAutRelated xswap Q) ∧
        ¬ (SourceAutRelated x Q ∧ SourceAutRelated xswap Q) := by
  dsimp only
  let P := residualPairOfChart x
  let Pswap := rootSwappedRepresentative P hP
  let xswap := chartWithResidualPair x Pswap
  have hxswap : residualPairOfChart xswap = Pswap := by
    simp [xswap]
  refine ⟨hxswap, ?_⟩
  intro Q hQ
  constructor
  · rw [sourceAutRelated_iff_related,
      sourceAutRelated_iff_related, hxswap]
    exact sameResidualBase_iff_related_or_swapped P hP Q hQ
  · rintro ⟨hx, hxs⟩
    apply related_families_disjoint P hP hbranch Q
    constructor
    · exact (sourceAutRelated_iff_related x Q).mp hx
    · change Related Pswap Q
      rw [← hxswap]
      exact (sourceAutRelated_iff_related xswap Q).mp hxs

end AlbertLean.Generic.ChartBridge
