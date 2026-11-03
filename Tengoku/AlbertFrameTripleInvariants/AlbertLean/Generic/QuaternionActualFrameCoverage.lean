import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSymplecticMatrixBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticActualFrameCoverage
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticLiteralFixedTwelve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms standard_hyperbolicTriple` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms standard_spans` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_twelve_actual_carrier_frame_alignment` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_literal_twelve_actual_carrier_frame_alignment` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ActualFrameCoverage

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.SymplecticTransvection
open AlbertLean.Generic.SymplecticProjectorFrame

universe u
variable {K : Type u} [Field K] [CharZero K]

def standardE (i : Fin 3) : Vec6 K := basisVector (Sum.inl i)
def standardF (i : Fin 3) : Vec6 K := basisVector (Sum.inr i)

def coordinateLabel : Ix6 → Fin 3
  | Sum.inl i => i
  | Sum.inr i => i

/-- The standard labelled rank-two projector, defined directly on grouped
coordinates without a rank or basis library.-/
def standardProjector (i : Fin 3) : Vec6 K →ₗ[K] Vec6 K where
  toFun x p := if coordinateLabel p = i then x p else 0
  map_add' := by
    intro x y
    funext p
    by_cases h : coordinateLabel p = i <;> simp [h]
  map_smul' := by
    intro t x
    funext p
    by_cases h : coordinateLabel p = i <;> simp [h]

theorem standardProjector_E (i j : Fin 3) :
    standardProjector (K := K) i (standardE j) =
      if i = j then standardE j else 0 := by
  classical
  by_cases hij : i = j
  · subst i
    ext p
    rcases p with p | p <;> by_cases hp : p = j <;>
      simp [standardProjector, standardE, coordinateLabel, basisVector,
        Pi.single_apply, hp]
  · ext p
    rcases p with p | p <;> by_cases hpj : p = j <;>
      by_cases hpi : p = i <;>
      simp_all [standardProjector, standardE, coordinateLabel, basisVector,
        Pi.single_apply]

theorem standardProjector_F (i j : Fin 3) :
    standardProjector (K := K) i (standardF j) =
      if i = j then standardF j else 0 := by
  classical
  by_cases hij : i = j
  · subst i
    ext p
    rcases p with p | p <;> by_cases hp : p = j <;>
      simp [standardProjector, standardF, coordinateLabel, basisVector,
        Pi.single_apply, hp]
  · ext p
    rcases p with p | p <;> by_cases hpj : p = j <;>
      by_cases hpi : p = i <;>
      simp_all [standardProjector, standardF, coordinateLabel, basisVector,
        Pi.single_apply]

theorem standard_hyperbolicTriple :
    HyperbolicTriple (omega (K := K)) standardE standardF := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact omega_basis_pair i
  all_goals
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [omega, omegaFun, standardE, standardF, basisVector,
        Pi.single_apply, Fin.sum_univ_succ]

/-- The six displayed target vectors span by their literal coordinates.-/
theorem standard_spans (x : Vec6 K) :
    ∃ a b : Fin 3 → K,
      x = (∑ j, a j • standardE j) + ∑ j, b j • standardF j := by
  classical
  refine ⟨fun j => x (Sum.inl j), fun j => x (Sum.inr j), ?_⟩
  funext p
  rcases p with p | p <;> fin_cases p <;>
    simp [standardE, standardF, basisVector, Fin.sum_univ_succ]

/-- Every actual complete trace-one self-adjoint projector frame on the
grouped carrier is intertwined with the literal standard frame by a word of
exactly twelve transvections over the original field.-/
theorem exists_twelve_actual_carrier_frame_alignment
    (P : Fin 3 → Carrier K)
    (hidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (htrace : ∀ i, jordanTrace (K := K) ((P i : Carrier K) : Mat6 K) = 1)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ∃ word : List (Step (K := K) (V := Vec6 K)), word.length = 12 ∧
      ∀ i, (wordMap omega word).comp (matrixAction (P i)) =
        (standardProjector i).comp (wordMap omega word) := by
  apply exists_twelve_actual_frame_alignment (K := K) (V := Vec6 K)
    (Q := fun i => standardProjector (K := K) i)
    (e := standardE (K := K)) (f := standardF (K := K))
    (omega (K := K)) omega_alternating omega_left_nondegenerate
    omega_right_nondegenerate
    (fun i => matrixAction (K := K) (P i : Mat6 K))
  · exact fun i => carrier_projector_action_idempotent (P i) (hidem i)
  · exact fun i => carrier_action_selfAdjoint (P i)
  · exact fun i => carrier_action_ne_zero_of_trace_one (P i) (htrace i)
  · exact carrier_frame_action_sum P hsum
  · exact standard_hyperbolicTriple (K := K)
  · exact standardProjector_E (K := K)
  · exact standardProjector_F (K := K)
  · exact standard_spans (K := K)

/-- Literal `Fin 12` version of the same actual-carrier normalization.-/
theorem exists_literal_twelve_actual_carrier_frame_alignment
    (P : Fin 3 → Carrier K)
    (hidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (htrace : ∀ i, jordanTrace (K := K) ((P i : Carrier K) : Mat6 K) = 1)
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ∃ schedule : FixedTwelveSchedule (K := K) (V := Vec6 K),
      ∀ i, (fixedTwelveMap omega schedule).comp (matrixAction (P i)) =
        (standardProjector i).comp (fixedTwelveMap omega schedule) := by
  obtain ⟨word, hlen, hintertwine⟩ :=
    exists_twelve_actual_carrier_frame_alignment P hidem htrace hsum
  let schedule := scheduleOfLengthTwelve word hlen
  refine ⟨schedule, ?_⟩
  intro i
  dsimp only [schedule]
  rw [fixedTwelveMap_scheduleOfLengthTwelve]
  exact hintertwine i

end AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
