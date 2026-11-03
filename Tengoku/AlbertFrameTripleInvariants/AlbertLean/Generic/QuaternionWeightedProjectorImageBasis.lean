import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualFrameCoverage
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticThreePairCoverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_spanning_carrier_frame_eigenbasis` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms first_projector_image_spanned` (it only prints; the queue checks the axioms of every declaration). -/

/-! The image-basis input consumed by the Q1 weighted-projector gauge. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.SymplecticProjectorFrame
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A genuine carrier frame has a labelled hyperbolic eigenbasis which spans
the ambient six-space.  This exposes the witnesses hidden inside the accepted
twelve-step normalization theorem and avoids a matrix-rank detour.
@isnad1 id=ex.3h2v.s11.c7899437d9c2 from=translated src=- shape=e6bc8dcc vocab=63c89208
-/
theorem exists_spanning_carrier_frame_eigenbasis
    (P : Fin 3 → Carrier K)
    (hidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (htrace : ∀ i, jordanTrace (K := K) (P i : Mat6 K) = 1)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ∃ u v : Fin 3 → Vec6 K,
      HyperbolicTriple (omega (K := K)) u v ∧
      (∀ i j, matrixAction (P i : Mat6 K) (u j) =
        if i = j then u j else 0) ∧
      (∀ i j, matrixAction (P i : Mat6 K) (v j) =
        if i = j then v j else 0) ∧
      ∀ x : Vec6 K, ∃ a b : Fin 3 → K,
        x = (∑ j, a j • u j) + ∑ j, b j • v j := by
  let Q : Fin 3 → Vec6 K →ₗ[K] Vec6 K :=
    fun i => matrixAction (K := K) (P i : Mat6 K)
  have hQi : ∀ i, IsIdempotent (Q i) :=
    fun i => carrier_projector_action_idempotent (P i) (hidem i)
  have hQs : ∀ i, IsSelfAdjoint (omega (K := K)) (Q i) :=
    fun i => carrier_action_selfAdjoint (P i)
  have hQn : ∀ i, Q i ≠ 0 :=
    fun i => carrier_action_ne_zero_of_trace_one (P i) (htrace i)
  have hQsum : Q 0 + Q 1 + Q 2 = LinearMap.id :=
    carrier_frame_action_sum P hsum
  obtain ⟨u, v, huv, hPu, hPv⟩ :=
    exists_hyperbolicTriple_of_complete_frame (omega (K := K))
      omega_right_nondegenerate Q hQi hQs hQn hQsum
  obtain ⟨word, -, hwu, hwv⟩ :=
    exists_fixed_twelve_triple_alignment (omega (K := K)) omega_alternating
      omega_left_nondegenerate omega_right_nondegenerate
      u v standardE standardF huv standard_hyperbolicTriple
  refine ⟨u, v, huv, hPu, hPv, ?_⟩
  intro x
  obtain ⟨a, b, hx⟩ := standard_spans (wordMap omega word x)
  refine ⟨a, b, ?_⟩
  apply wordMap_injective (omega (K := K)) omega_alternating word
  simpa only [map_add, map_sum, map_smul, hwu, hwv] using hx

/-- Consequently the actual image of the first projector is exactly the span
of its displayed hyperbolic pair.  This is the rank-two input used by Q1.
@isnad1 id=ex.3h2v.s11.d1d5c2fbb61f from=translated src=- shape=2b805529 vocab=cd69d133
-/
theorem first_projector_image_spanned
    (P : Fin 3 → Carrier K)
    (hidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (htrace : ∀ i, jordanTrace (K := K) (P i : Mat6 K) = 1)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ∃ u v : Fin 3 → Vec6 K,
      HyperbolicTriple (omega (K := K)) u v ∧
      (∀ i j, matrixAction (P i : Mat6 K) (u j) =
        if i = j then u j else 0) ∧
      (∀ i j, matrixAction (P i : Mat6 K) (v j) =
        if i = j then v j else 0) ∧
      ∀ x, matrixAction (P 0 : Mat6 K) x = x →
        ∃ a b : K, x = a • u 0 + b • v 0 := by
  obtain ⟨u, v, huv, hPu, hPv, hspan⟩ :=
    exists_spanning_carrier_frame_eigenbasis P hidem htrace hsum
  refine ⟨u, v, huv, hPu, hPv, ?_⟩
  intro x hx
  obtain ⟨a, b, hab⟩ := hspan x
  refine ⟨a 0, b 0, ?_⟩
  rw [← hx, hab]
  simp only [map_add, map_sum, map_smul, hPu, hPv]
  simp [Fin.sum_univ_succ]

end AlbertLean.Generic.QuaternionRow.WeightedProjectorGauge
