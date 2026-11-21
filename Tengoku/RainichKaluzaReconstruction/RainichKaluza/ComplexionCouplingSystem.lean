import Tengoku.RainichKaluzaReconstruction.RainichKaluza.DualityComplexionDerivative
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Simultaneous recovery of complexion rate and EMD coupling

After a seed Maxwell two-form is chosen, evaluated differential channels are
linear in two unknown scalars: the infinitesimal duality complexion rate
`omega` and the EMD coupling `a`.  This file solves the resulting two-channel
system and identifies its exact degeneracy determinant.

The variables are scalar probe evaluations of the geometric forms.  Building
those probes from curvature and exterior calculus remains the geometric task.
-/

namespace RainichKaluza

/-- Determinant separating the complexion and scalar-coupling response
channels.-/
def complexionCouplingDet (z1 z2 y1 y2 : ℝ) : ℝ :=
  z1 * y2 - z2 * y1

/-- Reconstructed complexion rate from two evaluated channels.-/
noncomputable def complexionRateFromChannels
    (x1 x2 z1 z2 y1 y2 : ℝ) : ℝ :=
  (x1 * y2 - x2 * y1) / complexionCouplingDet z1 z2 y1 y2

/-- Reconstructed EMD coupling from two evaluated channels.  The factor two
matches equations whose scalar source occurs as `(a/2)Y`.-/
noncomputable def couplingFromComplexionChannels
    (x1 x2 z1 z2 y1 y2 : ℝ) : ℝ :=
  2 * (z1 * x2 - z2 * x1) / complexionCouplingDet z1 z2 y1 y2

/-- Orientation-independent squared coupling constructed directly from the
same two evaluated channels.-/
noncomputable def couplingSqFromComplexionChannels
    (x1 x2 z1 z2 y1 y2 : ℝ) : ℝ :=
  couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 ^ 2

/-- The channel equations determine the numerator of the complexion rate.-/
theorem complexionRate_channel_numerator
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    x1 * y2 - x2 * y1 =
      omega * complexionCouplingDet z1 z2 y1 y2 := by
  rw [h1, h2]
  unfold complexionCouplingDet
  ring

/-- The channel equations determine the numerator of the EMD coupling.-/
theorem coupling_channel_numerator
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    2 * (z1 * x2 - z2 * x1) =
      a * complexionCouplingDet z1 z2 y1 y2 := by
  rw [h1, h2]
  unfold complexionCouplingDet
  ring

/-- A nonzero channel determinant recovers the complexion rate exactly.-/
theorem complexionRateFromChannels_eq
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    complexionRateFromChannels x1 x2 z1 z2 y1 y2 = omega := by
  unfold complexionRateFromChannels
  rw [complexionRate_channel_numerator x1 x2 z1 z2 y1 y2 omega a h1 h2]
  field_simp [hdet]

/-- A nonzero channel determinant recovers the EMD coupling exactly.-/
theorem couplingFromComplexionChannels_eq
    (x1 x2 z1 z2 y1 y2 omega a : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2) :
    couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 = a := by
  unfold couplingFromComplexionChannels
  rw [coupling_channel_numerator x1 x2 z1 z2 y1 y2 omega a h1 h2]
  field_simp [hdet]

/-- **Constructive channel converse, first equation.** On the nondegenerate
branch, the reconstructed complexion rate and coupling solve the first input
channel without assuming that any compatible pair was supplied.-/
theorem recovered_complexion_coupling_channel_one
    (x1 x2 z1 z2 y1 y2 : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    x1 =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 * z1 +
        (couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 / 2) * y1 := by
  unfold complexionRateFromChannels couplingFromComplexionChannels
    complexionCouplingDet
  have hdet0 : z1 * y2 - z2 * y1 ≠ 0 := by
    simpa [complexionCouplingDet] using hdet
  have hdet' : y2 * z1 - y1 * z2 ≠ 0 := by
    simpa [mul_comm] using hdet0
  field_simp [hdet0, hdet']
  ring

/-- **Constructive channel converse, second equation.** The same reconstructed
pair solves the second channel.-/
theorem recovered_complexion_coupling_channel_two
    (x1 x2 z1 z2 y1 y2 : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    x2 =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 * z2 +
        (couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 / 2) * y2 := by
  unfold complexionRateFromChannels couplingFromComplexionChannels
    complexionCouplingDet
  have hdet0 : z1 * y2 - z2 * y1 ≠ 0 := by
    simpa [complexionCouplingDet] using hdet
  have hdet' : y2 * z1 - y1 * z2 ≠ 0 := by
    simpa [mul_comm] using hdet0
  field_simp [hdet0, hdet']
  ring

/-- The nonzero determinant is a sufficient constructive certificate for a
simultaneous complexion/coupling solution.-/
theorem exists_complexion_coupling_of_det_ne
    (x1 x2 z1 z2 y1 y2 : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    ∃ omega a : ℝ,
      x1 = omega * z1 + (a / 2) * y1 ∧
      x2 = omega * z2 + (a / 2) * y2 := by
  exact ⟨complexionRateFromChannels x1 x2 z1 z2 y1 y2,
    couplingFromComplexionChannels x1 x2 z1 z2 y1 y2,
    recovered_complexion_coupling_channel_one x1 x2 z1 z2 y1 y2 hdet,
    recovered_complexion_coupling_channel_two x1 x2 z1 z2 y1 y2 hdet⟩

/-- On the nondegenerate two-channel branch, the pair `(omega,a)` is unique.-/
theorem complexion_coupling_pair_unique
    (x1 x2 z1 z2 y1 y2 omega a omega' a' : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0)
    (h1 : x1 = omega * z1 + (a / 2) * y1)
    (h2 : x2 = omega * z2 + (a / 2) * y2)
    (h1' : x1 = omega' * z1 + (a' / 2) * y1)
    (h2' : x2 = omega' * z2 + (a' / 2) * y2) :
    omega = omega' ∧ a = a' := by
  constructor
  · rw [← complexionRateFromChannels_eq x1 x2 z1 z2 y1 y2 omega a
      hdet h1 h2]
    exact complexionRateFromChannels_eq x1 x2 z1 z2 y1 y2 omega' a'
      hdet h1' h2'
  · rw [← couplingFromComplexionChannels_eq x1 x2 z1 z2 y1 y2 omega a
      hdet h1 h2]
    exact couplingFromComplexionChannels_eq x1 x2 z1 z2 y1 y2 omega' a'
      hdet h1' h2'

/-- **Exact evaluated coupling detector.** A nonzero channel determinant
constructs the unique pair `(complexion rate, EMD coupling)` satisfying both
channel equations. This theorem no longer takes a compatible coupling as an
input.-/
theorem existsUnique_complexion_coupling_of_det_ne
    (x1 x2 z1 z2 y1 y2 : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    ∃! p : ℝ × ℝ,
      x1 = p.1 * z1 + (p.2 / 2) * y1 ∧
      x2 = p.1 * z2 + (p.2 / 2) * y2 := by
  let p : ℝ × ℝ :=
    (complexionRateFromChannels x1 x2 z1 z2 y1 y2,
      couplingFromComplexionChannels x1 x2 z1 z2 y1 y2)
  refine ⟨p, ?_, ?_⟩
  · exact ⟨recovered_complexion_coupling_channel_one
      x1 x2 z1 z2 y1 y2 hdet,
      recovered_complexion_coupling_channel_two
        x1 x2 z1 z2 y1 y2 hdet⟩
  · intro q hq
    have hunique := complexion_coupling_pair_unique
      x1 x2 z1 z2 y1 y2 p.1 p.2 q.1 q.2 hdet
      (recovered_complexion_coupling_channel_one
        x1 x2 z1 z2 y1 y2 hdet)
      (recovered_complexion_coupling_channel_two
        x1 x2 z1 z2 y1 y2 hdet) hq.1 hq.2
    exact Prod.ext hunique.1.symm hunique.2.symm

/-- Reversing the scalar source orientation preserves the reconstructed
complexion rate.-/
theorem complexionRateFromChannels_neg_scalarSource
    (x1 x2 z1 z2 y1 y2 : ℝ) :
    complexionRateFromChannels x1 x2 z1 z2 (-y1) (-y2) =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 := by
  unfold complexionRateFromChannels complexionCouplingDet
  have hnum : x1 * -y2 - x2 * -y1 = -(x1 * y2 - x2 * y1) := by ring
  have hden : z1 * -y2 - z2 * -y1 = -(z1 * y2 - z2 * y1) := by ring
  calc
    (x1 * -y2 - x2 * -y1) / (z1 * -y2 - z2 * -y1) =
        (-(x1 * y2 - x2 * y1)) / (-(z1 * y2 - z2 * y1)) := by
      rw [hnum, hden]
    _ = (x1 * y2 - x2 * y1) / (z1 * y2 - z2 * y1) :=
      neg_div_neg_eq _ _

/-- Reversing the scalar source orientation reverses the reconstructed EMD
coupling, as required by `(v,a)↦(-v,-a)`.-/
theorem couplingFromComplexionChannels_neg_scalarSource
    (x1 x2 z1 z2 y1 y2 : ℝ) :
    couplingFromComplexionChannels x1 x2 z1 z2 (-y1) (-y2) =
      -couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingFromComplexionChannels complexionCouplingDet
  have hden : z1 * -y2 - z2 * -y1 = -(z1 * y2 - z2 * y1) := by ring
  calc
    2 * (z1 * x2 - z2 * x1) / (z1 * -y2 - z2 * -y1) =
        2 * (z1 * x2 - z2 * x1) / (-(z1 * y2 - z2 * y1)) := by
      rw [hden]
    _ = -(2 * (z1 * x2 - z2 * x1) / (z1 * y2 - z2 * y1)) := by
      rw [div_neg_eq_neg_div]

/-- The channel-constructed squared coupling is independent of the global
scalar orientation.-/
theorem couplingSqFromComplexionChannels_neg_scalarSource
    (x1 x2 z1 z2 y1 y2 : ℝ) :
    couplingSqFromComplexionChannels x1 x2 z1 z2 (-y1) (-y2) =
      couplingSqFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingSqFromComplexionChannels
  rw [couplingFromComplexionChannels_neg_scalarSource]
  ring

/-- A variable duality transition shifts each evaluated differential channel
by its transition rate times the corresponding complexion-response channel.
On the nondegenerate branch, the reconstructed raw complexion rate therefore
acquires exactly that transition rate.-/
theorem complexionRateFromChannels_gauge_shift
    (x1 x2 z1 z2 y1 y2 tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    complexionRateFromChannels (x1 + tau * z1) (x2 + tau * z2)
        z1 z2 y1 y2 =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 + tau := by
  unfold complexionRateFromChannels complexionCouplingDet at *
  field_simp [hdet]
  ring

/-- The simultaneously reconstructed EMD coupling is invariant under the
same variable-duality channel shift.-/
theorem couplingFromComplexionChannels_gauge_invariant
    (x1 x2 z1 z2 y1 y2 tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    couplingFromComplexionChannels (x1 + tau * z1) (x2 + tau * z2)
        z1 z2 y1 y2 =
      couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingFromComplexionChannels complexionCouplingDet at *
  field_simp [hdet]
  ring

/-- The squared detector is invariant under the local duality-channel shift
that changes the raw complexion rate.-/
theorem couplingSqFromComplexionChannels_gauge_invariant
    (x1 x2 z1 z2 y1 y2 tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    couplingSqFromComplexionChannels (x1 + tau * z1) (x2 + tau * z2)
        z1 z2 y1 y2 =
      couplingSqFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingSqFromComplexionChannels
  rw [couplingFromComplexionChannels_gauge_invariant
    x1 x2 z1 z2 y1 y2 tau hdet]

/-- Multiplying every evaluated channel by the same nonzero seed scale leaves
the reconstructed complexion rate unchanged.  This is the algebraic overlap
law needed when two adapted principal frames select representatives of the
same Maxwell seed line.-/
theorem complexionRateFromChannels_common_smul
    (x1 x2 z1 z2 y1 y2 lambda : ℝ) (hlambda : lambda ≠ 0) :
    complexionRateFromChannels
        (lambda * x1) (lambda * x2)
        (lambda * z1) (lambda * z2)
        (lambda * y1) (lambda * y2) =
      complexionRateFromChannels x1 x2 z1 z2 y1 y2 := by
  unfold complexionRateFromChannels complexionCouplingDet
  field_simp [hlambda]

/-- The signed coupling detector is independent of a common nonzero scaling
of the seed-derived evaluated channels.-/
theorem couplingFromComplexionChannels_common_smul
    (x1 x2 z1 z2 y1 y2 lambda : ℝ) (hlambda : lambda ≠ 0) :
    couplingFromComplexionChannels
        (lambda * x1) (lambda * x2)
        (lambda * z1) (lambda * z2)
        (lambda * y1) (lambda * y2) =
      couplingFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingFromComplexionChannels complexionCouplingDet
  field_simp [hlambda]

/-- In particular the intrinsic squared detector is independent of the common
sign/scale ambiguity of an adapted Maxwell seed pair.-/
theorem couplingSqFromComplexionChannels_common_smul
    (x1 x2 z1 z2 y1 y2 lambda : ℝ) (hlambda : lambda ≠ 0) :
    couplingSqFromComplexionChannels
        (lambda * x1) (lambda * x2)
        (lambda * z1) (lambda * z2)
        (lambda * y1) (lambda * y2) =
      couplingSqFromComplexionChannels x1 x2 z1 z2 y1 y2 := by
  unfold couplingSqFromComplexionChannels
  rw [couplingFromComplexionChannels_common_smul
    x1 x2 z1 z2 y1 y2 lambda hlambda]

/-- Gauge-corrected complexion reconstructed from two evaluated channels.-/
noncomputable def gaugeCorrectedComplexionRateFromChannels
    (x1 x2 z1 z2 y1 y2 connection : ℝ) : ℝ :=
  gaugeCorrectedComplexionRate
    (complexionRateFromChannels x1 x2 z1 z2 y1 y2) connection

/-- **Overlap-invariant channel theorem.** If a variable duality transition
shifts both the evaluated differential channels and the local connection by
the same rate, the corrected reconstructed complexion is unchanged.-/
theorem gaugeCorrectedComplexionRateFromChannels_invariant
    (x1 x2 z1 z2 y1 y2 connection tau : ℝ)
    (hdet : complexionCouplingDet z1 z2 y1 y2 ≠ 0) :
    gaugeCorrectedComplexionRateFromChannels
        (x1 + tau * z1) (x2 + tau * z2) z1 z2 y1 y2
        (connection + tau) =
      gaugeCorrectedComplexionRateFromChannels
        x1 x2 z1 z2 y1 y2 connection := by
  unfold gaugeCorrectedComplexionRateFromChannels
  rw [complexionRateFromChannels_gauge_shift x1 x2 z1 z2 y1 y2 tau hdet]
  exact gaugeCorrectedComplexionRate_invariant
    (complexionRateFromChannels x1 x2 z1 z2 y1 y2) connection tau

section ChannelFields

variable {X : Type*}

/-- Pointwise complexion rate constructed from six scalar channel fields.-/
noncomputable def complexionRateFromChannelFields
    (x1 x2 z1 z2 y1 y2 : X → ℝ) (p : X) : ℝ :=
  complexionRateFromChannels (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p)

/-- Pointwise signed EMD coupling constructed from channel fields.-/
noncomputable def couplingFromComplexionChannelFields
    (x1 x2 z1 z2 y1 y2 : X → ℝ) (p : X) : ℝ :=
  couplingFromComplexionChannels
    (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p)

/-- Pointwise orientation-independent squared coupling constructed from
channel fields.-/
noncomputable def couplingSqFromComplexionChannelFields
    (x1 x2 z1 z2 y1 y2 : X → ℝ) (p : X) : ℝ :=
  couplingSqFromComplexionChannels
    (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p)

/-- Existence of one signed coupling valid throughout a patch, while the
complexion rate may vary from point to point.-/
def HasGlobalComplexionCouplingOn
    (U : Set X) (x1 x2 z1 z2 y1 y2 : X → ℝ) : Prop :=
  ∃ a : ℝ, ∀ p ∈ U, ∃ omega : ℝ,
    x1 p = omega * z1 p + (a / 2) * y1 p ∧
    x2 p = omega * z2 p + (a / 2) * y2 p

/-- The channel-constructed signed coupling is constant on a patch.-/
def RecoveredCouplingConstantOn
    (U : Set X) (x1 x2 z1 z2 y1 y2 : X → ℝ) : Prop :=
  ∃ a : ℝ, ∀ p ∈ U,
    couplingFromComplexionChannelFields x1 x2 z1 z2 y1 y2 p = a

/-- **Patch-level coupling detector.** When the channel determinant is
nonzero throughout the patch, existence of a single EMD coupling is exactly
constancy of the coupling constructed pointwise from the channel data. No
candidate coupling is supplied to the reconstructed side of the equivalence.-/
theorem hasGlobalComplexionCouplingOn_iff_recoveredCouplingConstantOn
    (U : Set X) (x1 x2 z1 z2 y1 y2 : X → ℝ)
    (hdet : ∀ p ∈ U,
      complexionCouplingDet (z1 p) (z2 p) (y1 p) (y2 p) ≠ 0) :
    HasGlobalComplexionCouplingOn U x1 x2 z1 z2 y1 y2 ↔
      RecoveredCouplingConstantOn U x1 x2 z1 z2 y1 y2 := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro p hp
    obtain ⟨omega, h1, h2⟩ := ha p hp
    exact couplingFromComplexionChannels_eq
      (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p) omega a
      (hdet p hp) h1 h2
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    intro p hp
    refine ⟨complexionRateFromChannelFields x1 x2 z1 z2 y1 y2 p,
      ?_, ?_⟩
    · rw [← ha p hp]
      exact recovered_complexion_coupling_channel_one
        (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p) (hdet p hp)
    · rw [← ha p hp]
      exact recovered_complexion_coupling_channel_two
        (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p) (hdet p hp)

/-- A global compatible coupling is recovered pointwise by the squared
detector, with no scalar-orientation choice in the conclusion.-/
theorem couplingSqFromComplexionChannelFields_eq_of_global
    (U : Set X) (x1 x2 z1 z2 y1 y2 : X → ℝ)
    (hdet : ∀ p ∈ U,
      complexionCouplingDet (z1 p) (z2 p) (y1 p) (y2 p) ≠ 0)
    (hglobal : HasGlobalComplexionCouplingOn U x1 x2 z1 z2 y1 y2) :
    ∃ a : ℝ, ∀ p ∈ U,
      couplingSqFromComplexionChannelFields x1 x2 z1 z2 y1 y2 p = a ^ 2 := by
  obtain ⟨a, ha⟩ :=
    (hasGlobalComplexionCouplingOn_iff_recoveredCouplingConstantOn
      U x1 x2 z1 z2 y1 y2 hdet).mp hglobal
  refine ⟨a, ?_⟩
  intro p hp
  unfold couplingSqFromComplexionChannelFields
    couplingSqFromComplexionChannels
  rw [show couplingFromComplexionChannels
      (x1 p) (x2 p) (z1 p) (z2 p) (y1 p) (y2 p) = a by
    exact ha p hp]

end ChannelFields

end RainichKaluza
