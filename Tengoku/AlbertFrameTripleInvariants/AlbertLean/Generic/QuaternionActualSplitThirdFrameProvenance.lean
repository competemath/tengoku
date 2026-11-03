import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualSplitThirdFrameAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_split_actual_three_frame_scalar_provenance_of_same_ledger` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_split_actual_three_frame_jordanAut_from_scalar_provenance` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Scalar-similitude provenance for the actual third-frame comparison

This construction retains the scalar produced by the common-fibre argument and
exports its literal matrices, similitude law, and conjugation of all nine
carrier points.  It makes no representation claim about arbitrary carrier
automorphisms.
-/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ActualSplitThirdFrameProvenance

open AlbertLean.Generic.FourRowLabelledProbes
open AlbertLean.Generic.FourRowProbeTrace
open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
open AlbertLean.Generic.QuaternionRow.ProjectorBlockBridge
open AlbertLean.Generic.QuaternionRow.ScalarJordanAut
open AlbertLean.Generic.QuaternionRow.ActualSplitThirdFrameAut

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem exists_scalar_provenance_of_labelled_probes
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
    ∃ t : K, ∃ ht : t ≠ 0,
      scalarSimilitude t * scalarSimilitudeInv t = 1 ∧
      scalarSimilitudeInv t * scalarSimilitude t = 1 ∧
      (scalarSimilitude t).transpose * symplecticJ * scalarSimilitude t =
        t • symplecticJ ∧
      (∀ i, scalarSimilitude t * (E i : Mat6 K) * scalarSimilitudeInv t =
        (E' i : Mat6 K)) ∧
      (∀ i, scalarSimilitude t * (F i : Mat6 K) * scalarSimilitudeInv t =
        (F' i : Mat6 K)) ∧
      (∀ i, scalarSimilitude t * (P i : Mat6 K) * scalarSimilitudeInv t =
        (P' i : Mat6 K)) := by
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
  refine ⟨t, ht, scalarSimilitude_mul_inv t ht,
    scalarSimilitude_inv_mul t ht, scalarSimilitude_form t, ?_, ?_, ?_⟩
  · intro i
    rw [hE i, hE' i,
      scalarSimilitude_conjugates_grouped t ht (diagonalUnit i) 0 0]
    simp
  · intro i
    rw [hF i, hF' i,
      scalarSimilitude_conjugates_grouped t ht (f i) 0 0]
    simp
  · intro i
    rw [hP i, hPcommon' i,
      scalarSimilitude_conjugates_grouped t ht (a i) (u i) (v i),
      hu i, hv i]

/-- The same open hypotheses as the existing same-ledger theorem now retain
the constructed scalar similitude and its full nine-point conjugacy.
@isnad1 id=ex.21h14v.s13.9f4bf0942b64 from=translated src=- shape=8c5caf09 vocab=66192830
-/
theorem exists_split_actual_three_frame_scalar_provenance_of_same_ledger
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
    ∃ t : K, ∃ ht : t ≠ 0,
      scalarSimilitude t * scalarSimilitudeInv t = 1 ∧
      scalarSimilitudeInv t * scalarSimilitude t = 1 ∧
      (scalarSimilitude t).transpose * symplecticJ * scalarSimilitude t =
        t • symplecticJ ∧
      (∀ i, scalarSimilitude t * (E i : Mat6 K) * scalarSimilitudeInv t =
        (E' i : Mat6 K)) ∧
      (∀ i, scalarSimilitude t * (F i : Mat6 K) * scalarSimilitudeInv t =
        (F' i : Mat6 K)) ∧
      (∀ i, scalarSimilitude t * (P i : Mat6 K) * scalarSimilitudeInv t =
        (P' i : Mat6 K)) := by
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
  exact exists_scalar_provenance_of_labelled_probes
    E F P E' F' P' f a a' u v u' v'
    hE hE' hF hF' hP hP' hPidem hPidem' hPtrace hPtrace'
    hPsum hPsum' hfsum hf0 hf2 hf02 hf20 hprobeOpen hLabel hadj hrankTwo

/-- Forgetting the retained matrices recovers the original existential
Jordan-automorphism conclusion from the stronger provenance theorem.
@isnad1 id=ex.21h14v.s13.a629dec071ec from=translated src=- shape=70256771 vocab=e49bcf4a
-/
theorem exists_split_actual_three_frame_jordanAut_from_scalar_provenance
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
  obtain ⟨t, ht, _hMN, _hNM, _hform, hEc, hFc, hPc⟩ :=
    exists_split_actual_three_frame_scalar_provenance_of_same_ledger
      E F P E' F' P' f a a' u v u' v'
      hE hE' hF hF' hP hP' hPidem hPidem' hPtrace hPtrace'
      hPsum hPsum' hfsum hf0 hf2 hf02 hf20 hprobeOpen hadj hrankTwo hledger
  refine ⟨scalarAut t ht, ?_, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    change scalarSimilitude t * (E i : Mat6 K) * scalarSimilitudeInv t =
      (E' i : Mat6 K)
    exact hEc i
  · intro i
    apply Subtype.ext
    change scalarSimilitude t * (F i : Mat6 K) * scalarSimilitudeInv t =
      (F' i : Mat6 K)
    exact hFc i
  · intro i
    apply Subtype.ext
    change scalarSimilitude t * (P i : Mat6 K) * scalarSimilitudeInv t =
      (P' i : Mat6 K)
    exact hPc i

end AlbertLean.Generic.QuaternionRow.ActualSplitThirdFrameProvenance
