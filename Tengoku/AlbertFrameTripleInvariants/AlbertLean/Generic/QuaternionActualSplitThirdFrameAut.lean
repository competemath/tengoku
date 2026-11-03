import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowLabelledProbes
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CommonFrameScalarFibre
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionProjectorBlockBridge
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionScalarJordanAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms uncenteredCell_carrierLedger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms labelledProbe_eq_two_split_joint` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms grouped_frame_threeSumZero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_split_actual_three_frame_jordanAut_of_labelled_probes` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_split_actual_three_frame_jordanAut_of_same_ledger` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Comparing third frames after a common split

In common split coordinates, the labelled probes determine the top-left
blocks of the third frame under the stated probe nonvanishing condition.
The projector equations, trace and completeness, together with the
adjugate and rank assumptions, give one common scalar parameter. Its
scalar similitude fixes the first two frames and transports the third.
The final theorem derives the probe equalities from all 54 measurements.
-/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ActualSplitThirdFrameAut

open AlbertLean.Generic.FourRowLabelledProbes
open AlbertLean.Generic.FourRowProbeTrace
open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.ScalarJordanAut

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A displayed split carrier element.-/
def splitCarrier (a : Mat3 K) : Carrier K :=
  ⟨grouped a 0 0, grouped_symplectic_selfadjoint _ _ _⟩

/-- The literal 54 scalar cells for three labelled carrier frames: three
pair tables and the centered joint table, with the public `1/3, 2/9`
centering convention.-/
structure CarrierLedger (K : Type u) where
  pairEF : Fin 3 → Fin 3 → K
  pairFP : Fin 3 → Fin 3 → K
  pairPE : Fin 3 → Fin 3 → K
  centered : Fin 3 → Fin 3 → Fin 3 → K

def carrierLedger (E F P : Fin 3 → Carrier K) : CarrierLedger K :=
  let pairEF := fun i j =>
    jordanTrace (K := K) ((E i : Mat6 K) * (F j : Mat6 K))
  let pairFP := fun j l =>
    jordanTrace (K := K) ((F j : Mat6 K) * (P l : Mat6 K))
  let pairPE := fun l i =>
    jordanTrace (K := K) ((P l : Mat6 K) * (E i : Mat6 K))
  ⟨pairEF, pairFP, pairPE, fun i j l =>
    jordanTrace (K := K)
        ((E i : Mat6 K) * matrixJordan (F j : Mat6 K) (P l : Mat6 K)) -
      (pairEF i j + pairFP j l + pairPE l i) / 3 + 2 / 9⟩

def uncenteredCell (L : CarrierLedger K) (i j l : Fin 3) : K :=
  L.centered i j l +
    (L.pairEF i j + L.pairFP j l + L.pairPE l i) / 3 - 2 / 9

@[simp] theorem uncenteredCell_carrierLedger
    (E F P : Fin 3 → Carrier K) (i j l : Fin 3) :
    uncenteredCell (carrierLedger E F P) i j l =
      jordanTrace (K := K)
        ((E i : Mat6 K) * matrixJordan (F j : Mat6 K) (P l : Mat6 K)) := by
  simp [uncenteredCell, carrierLedger]
  ring

/-- In common split coordinates, an uncentered joint cell is exactly half
the corresponding division-free labelled FourRow probe.-/
theorem labelledProbe_eq_two_split_joint
    (f a : Mat3 K) (u v : Vec3 K) (i : Fin 3) :
    labelledProbe f a i = 2 * jordanTrace (K := K)
      (grouped (diagonalUnit i) 0 0 *
        matrixJordan (grouped f 0 0) (grouped a u v)) := by
  fin_cases i <;>
    simp [labelledProbe, jordanTrace, matrixJordan, grouped, diagonalUnit,
      Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, hat] <;> ring

/-- Completeness of an actual grouped frame gives both vector sum equations
used by `common_frame_scalar_fibre`.-/
theorem grouped_frame_threeSumZero
    (P : Fin 3 → Carrier K)
    (a : Fin 3 → Mat3 K) (u v : Fin 3 → Vec3 K)
    (hP : ∀ i, (P i : Mat6 K) = grouped (a i) (u i) (v i))
    (hsum : (P 0 : Mat6 K) + P 1 + P 2 = 1) :
    ThreeSumZero u ∧ ThreeSumZero v := by
  have hhatU : hat (u 0) + hat (u 1) + hat (u 2) = 0 := by
    ext i j
    have h := congrFun (congrFun hsum (Sum.inl i)) (Sum.inr j)
    simpa [hP 0, hP 1, hP 2, grouped, Matrix.one_apply] using h
  have hhatV : hat (v 0) + hat (v 1) + hat (v 2) = 0 := by
    ext i j
    have h := congrFun (congrFun hsum (Sum.inr i)) (Sum.inl j)
    simpa [hP 0, hP 1, hP 2, grouped, Matrix.one_apply] using h
  constructor
  · intro j
    have h := congrFun (congrArg unhat hhatU) j
    fin_cases j <;> simpa [unhat, hat, add_comm, add_left_comm, add_assoc] using h
  · intro j
    have h := congrFun (congrArg unhat hhatV) j
    fin_cases j <;> simpa [unhat, hat, add_comm, add_left_comm, add_assoc] using h

/-- In common split coordinates, the labelled probes determine the
third-frame top-left blocks under `hprobeOpen`. The frame equations,
`hadj` and `hrankTwo` then give a scalar similitude matching all nine
carrier elements. Here `hLabel` supplies the probe equalities; the later
same-measurement theorem derives them from the full measurement record.-/
theorem exists_split_actual_three_frame_jordanAut_of_labelled_probes
    (E F P E' F' P' : Fin 3 → Carrier K)
    (f a a' : Fin 3 → Mat3 K)
    (u v u' v' : Fin 3 → Vec3 K)
    (hE : ∀ i, (E i : Mat6 K) = grouped (diagonalUnit i) 0 0)
    (hE' : ∀ i, (E' i : Mat6 K) = grouped (diagonalUnit i) 0 0)
    (hF : ∀ i, (F i : Mat6 K) = grouped (f i) 0 0)
    (hF' : ∀ i, (F' i : Mat6 K) = grouped (f i) 0 0)
    (hP : ∀ i, (P i : Mat6 K) = grouped (a i) (u i) (v i))
    (hP' : ∀ i, (P' i : Mat6 K) = grouped (a' i) (u' i) (v' i))
    (hPidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (hPidem' : ∀ i, (P' i : Mat6 K) * P' i = P' i)
    (hPtrace : ∀ i, jordanTrace (K := K) (P i : Mat6 K) = 1)
    (hPtrace' : ∀ i, jordanTrace (K := K) (P' i : Mat6 K) = 1)
    (hPsum : (P 0 : Mat6 K) + P 1 + P 2 = 1)
    (hPsum' : (P' 0 : Mat6 K) + P' 1 + P' 2 = 1)
    (hfsum : f 0 + f 1 + f 2 = 1)
    (hf0 : f 0 * f 0 = f 0) (hf2 : f 2 * f 2 = f 2)
    (hf02 : f 0 * f 2 = 0) (hf20 : f 2 * f 0 = 0)
    (hprobeOpen : Matrix.det
      (grading * encoder (f 0) (f 2) - encoder (f 0) (f 2) * grading) ≠ 0)
    (hLabel : ∀ l i,
      labelledProbe (f 0) (a l) i = labelledProbe (f 0) (a' l) i ∧
      labelledProbe (f 1) (a l) i = labelledProbe (f 1) (a' l) i ∧
      labelledProbe (f 2) (a l) i = labelledProbe (f 2) (a' l) i)
    (hadj : ∀ l, Matrix.adjugate (a l) ≠ 0)
    (hrankTwo :
      (∃ p q, u 0 p * u 1 q - u 0 q * u 1 p ≠ 0) ∨
      (∃ p q, v 0 p * v 1 q - v 0 q * v 1 p ≠ 0)) :
    ∃ g : Aut (K := K),
      (∀ i, g.linear (E i) = E' i) ∧
      (∀ i, g.linear (F i) = F' i) ∧
      (∀ i, g.linear (P i) = P' i) := by
  have ha : ∀ l, a l = a' l := by
    intro l
    exact eq_of_orthogonal_idempotent_labelled_probes
      (f 0) (f 1) (f 2) (a l) (a' l)
      hfsum hf0 hf2 hf02 hf20 hprobeOpen (hLabel l)
  have hPcommon' : ∀ i, (P' i : Mat6 K) = grouped (a i) (u' i) (v' i) := by
    intro i
    rw [ha i]
    exact hP' i
  have hblock : ∀ i,
      a i * a i - a i = -(hat (u i) * hat (v i)) := by
    intro i
    apply top_left_projector_equation
    simpa [hP i] using hPidem i
  have hblock' : ∀ i,
      a i * a i - a i = -(hat (u' i) * hat (v' i)) := by
    intro i
    apply top_left_projector_equation
    simpa [hPcommon' i] using hPidem' i
  have htrace : ∀ i, Matrix.trace (a i) = 1 := by
    intro i
    apply grouped_trace_one (a i) (u i) (v i)
    simpa [hP i] using hPtrace i
  obtain ⟨hsumu, hsumv⟩ := grouped_frame_threeSumZero P a u v hP hPsum
  obtain ⟨hsumu', hsumv'⟩ :=
    grouped_frame_threeSumZero P' a u' v' hPcommon' hPsum'
  obtain ⟨t, ht, hu, hv⟩ := common_frame_scalar_fibre
    a u v u' v' hblock hblock' htrace hadj
      hsumu hsumu' hsumv hsumv' hrankTwo
  let g : Aut (K := K) := scalarAut t ht
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    change (((scalarAut t ht).linear (E i) : Carrier K) : Mat6 K) =
      (E' i : Mat6 K)
    rw [scalarAut_grouped t ht (diagonalUnit i) 0 0 (E i) (hE i), hE' i]
    simp
  · intro i
    apply Subtype.ext
    change (((scalarAut t ht).linear (F i) : Carrier K) : Mat6 K) =
      (F' i : Mat6 K)
    rw [scalarAut_grouped t ht (f i) 0 0 (F i) (hF i), hF' i]
    simp
  · intro i
    apply Subtype.ext
    change (((scalarAut t ht).linear (P i) : Carrier K) : Mat6 K) =
      (P' i : Mat6 K)
    rw [scalarAut_grouped t ht (a i) (u i) (v i) (P i) (hP i),
      hPcommon' i, hu i, hv i]

/-- Literal same-54-ledger endpoint after the pair has been put into common
split coordinates.  Ledger equality is converted here, rather than by a
premise, into the nine labelled probes consumed above.-/
theorem exists_split_actual_three_frame_jordanAut_of_same_ledger
    (E F P E' F' P' : Fin 3 → Carrier K)
    (f a a' : Fin 3 → Mat3 K)
    (u v u' v' : Fin 3 → Vec3 K)
    (hE : ∀ i, (E i : Mat6 K) = grouped (diagonalUnit i) 0 0)
    (hE' : ∀ i, (E' i : Mat6 K) = grouped (diagonalUnit i) 0 0)
    (hF : ∀ i, (F i : Mat6 K) = grouped (f i) 0 0)
    (hF' : ∀ i, (F' i : Mat6 K) = grouped (f i) 0 0)
    (hP : ∀ i, (P i : Mat6 K) = grouped (a i) (u i) (v i))
    (hP' : ∀ i, (P' i : Mat6 K) = grouped (a' i) (u' i) (v' i))
    (hPidem : ∀ i, (P i : Mat6 K) * P i = P i)
    (hPidem' : ∀ i, (P' i : Mat6 K) * P' i = P' i)
    (hPtrace : ∀ i, jordanTrace (K := K) (P i : Mat6 K) = 1)
    (hPtrace' : ∀ i, jordanTrace (K := K) (P' i : Mat6 K) = 1)
    (hPsum : (P 0 : Mat6 K) + P 1 + P 2 = 1)
    (hPsum' : (P' 0 : Mat6 K) + P' 1 + P' 2 = 1)
    (hfsum : f 0 + f 1 + f 2 = 1)
    (hf0 : f 0 * f 0 = f 0) (hf2 : f 2 * f 2 = f 2)
    (hf02 : f 0 * f 2 = 0) (hf20 : f 2 * f 0 = 0)
    (hprobeOpen : Matrix.det
      (grading * encoder (f 0) (f 2) - encoder (f 0) (f 2) * grading) ≠ 0)
    (hadj : ∀ l, Matrix.adjugate (a l) ≠ 0)
    (hrankTwo :
      (∃ p q, u 0 p * u 1 q - u 0 q * u 1 p ≠ 0) ∨
      (∃ p q, v 0 p * v 1 q - v 0 q * v 1 p ≠ 0))
    (hledger : carrierLedger E F P = carrierLedger E' F' P') :
    ∃ g : Aut (K := K),
      (∀ i, g.linear (E i) = E' i) ∧
      (∀ i, g.linear (F i) = F' i) ∧
      (∀ i, g.linear (P i) = P' i) := by
  have hLabel : ∀ l i,
      labelledProbe (f 0) (a l) i = labelledProbe (f 0) (a' l) i ∧
      labelledProbe (f 1) (a l) i = labelledProbe (f 1) (a' l) i ∧
      labelledProbe (f 2) (a l) i = labelledProbe (f 2) (a' l) i := by
    intro l i
    have hcell (j : Fin 3) :
        uncenteredCell (carrierLedger E F P) i j l =
          uncenteredCell (carrierLedger E' F' P') i j l :=
      congrArg (fun L : CarrierLedger K => uncenteredCell L i j l) hledger
    have hjoint (j : Fin 3) :
        jordanTrace (K := K)
            ((E i : Mat6 K) * matrixJordan (F j : Mat6 K) (P l : Mat6 K)) =
          jordanTrace (K := K)
            ((E' i : Mat6 K) * matrixJordan (F' j : Mat6 K) (P' l : Mat6 K)) := by
      simpa using hcell j
    have hprobe (j : Fin 3) :
        labelledProbe (f j) (a l) i = labelledProbe (f j) (a' l) i := by
      rw [labelledProbe_eq_two_split_joint (f j) (a l) (u l) (v l) i,
        labelledProbe_eq_two_split_joint (f j) (a' l) (u' l) (v' l) i]
      exact congrArg (fun x : K => 2 * x)
        (by simpa [hE i, hE' i, hF j, hF' j, hP l, hP' l] using hjoint j)
    exact ⟨hprobe 0, hprobe 1, hprobe 2⟩
  exact exists_split_actual_three_frame_jordanAut_of_labelled_probes
    E F P E' F' P' f a a' u v u' v'
    hE hE' hF hF' hP hP' hPidem hPidem' hPtrace hPtrace'
    hPsum hPsum' hfsum hf0 hf2 hf02 hf20 hprobeOpen hLabel hadj hrankTwo

end AlbertLean.Generic.QuaternionRow.ActualSplitThirdFrameAut
