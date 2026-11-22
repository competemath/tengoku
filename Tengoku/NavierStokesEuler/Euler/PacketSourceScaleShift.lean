import Tengoku.NavierStokesEuler.Euler.PacketSourceParameterScales

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact reindexing of the prescribed scale sequence after finitely many
exceptional initial stages. No new choice of asymptotic scales is made. -/

noncomputable section

namespace EulerPacketSourceScaleSequence

open EulerPacketSourceScaleChoice EulerPacketUniformFrequencyScales

/--
@isnad1 id=eq.0h4v.s5.4b7a83a9f436 from=translated src=- shape=39279be5 vocab=aae4911f
-/
theorem scaleSequence_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    scaleSequence (J+r) (scaleSequence J X r) n=scaleSequence J X (r+n) := by
  induction n with
  | zero => simp only [scaleSequence_zero,Nat.add_zero]
  | succ n ih =>
    rw [scaleSequence_succ,ih,show r+(n+1)=(r+n)+1 by omega,scaleSequence_succ,Nat.add_assoc]

/--
@isnad1 id=eq.0h4v.s5.5aff2a84d0f6 from=translated src=- shape=e966aec3 vocab=30b5d623
-/
theorem frequency_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    frequency (J+r) (scaleSequence J X r) n=frequency J X (r+n) := by
  simp only [frequency,scaleSequence_shift,Nat.add_assoc]

/--
@isnad1 id=eq.0h4v.s5.a472555a1e2e from=translated src=- shape=e966aec3 vocab=96f87d58
-/
theorem supportScale_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    supportScale (J+r) (scaleSequence J X r) n=supportScale J X (r+n) := by
  simp only [supportScale,scaleSequence_shift,Nat.add_assoc]

/--
@isnad1 id=eq.0h4v.s5.91d8fafc29e4 from=translated src=- shape=e966aec3 vocab=3bfed255
-/
theorem spike_shift (J : ℕ) (X : ℝ) (r n : ℕ) :
    spike (J+r) (scaleSequence J X r) n=spike J X (r+n) := by
  simp only [spike,scaleSequence_shift,Nat.add_assoc]

/--
@isnad1 id=eq.1h8v.s5.dac8899de93a from=translated src=- shape=b2ba1457 vocab=f2a37166
-/
theorem parameterEnvelope_shift (J : ℕ) (hJ : 1 ≤ J) (C c : ℝ) (p q : ℕ)
    (X : ℝ) (r n : ℕ) :
    parameterEnvelope (J+r) C c p q (scaleSequence J X r) n=
      parameterEnvelope J C c p q X (r+n) := by
  have he : J+r-1+n=J-1+(r+n) := by omega
  simp only [parameterEnvelope,scaleSequence_shift,Nat.add_assoc,he]

end EulerPacketSourceScaleSequence
