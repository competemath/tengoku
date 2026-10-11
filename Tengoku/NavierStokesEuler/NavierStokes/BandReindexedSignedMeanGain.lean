import Tengoku.NavierStokesEuler.NavierStokes.SignedMeanGain

/-!
# Signed mean gain with fixed physical labels

The physical wave family keeps its original label type.  At each band an
injection on the active finite set identifies its coefficient data with the
relative native labels used by `SignedMeanGain.NativeData`.  Finite-sum
reindexing then gives the actual native cross identity.  The mean-gain theorem
is applied to the original family, with its original uniform constants.
-/

noncomputable section

namespace NavierStokes.BandReindexedSignedMeanGain

open Set Function
open scoped BigOperators
open WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain

/-! ## Coefficient and carrier identities at one band -/

/-- The carrier metadata needed to compare the actual fields at one band.
No relationship at another band is required. -/
structure SameCarrierAt {D : Type} (a b : HarmonicBlock D) (n : ℕ) : Prop where
  frequency : b.frequency n = a.frequency n
  phase : b.phase n = a.phase n
  angular : b.angularFrequency n = a.angularFrequency n

theorem sameCarrierAt_of_sameCarrier {D : Type} {a b : HarmonicBlock D}
    (h : LabelSumBounds.SameCarrier a b) (n : ℕ) : SameCarrierAt a b n :=
  ⟨congrFun h.frequency n, congrFun h.phase n, congrFun h.angular n⟩

/-- Equality of the stored coefficients and carrier metadata identifies the
actual harmonic field at this band.  Pressure data are not used in covariance. -/
theorem oscillation_eq_at_band_of_coefficients {D : Type}
    (a b : HarmonicBlock D) (n : ℕ)
    (hv : a.velocity n = b.velocity n) (hc : SameCarrierAt a b n) :
    a.oscillation n = b.oscillation n := by
  funext p i
  simp only [HarmonicBlock.oscillation, hv, hc.frequency, hc.phase, hc.angular]

/-! ## Finite reindexing of actual fields -/

/-- Reindex a finite sum using only the coefficient and carrier identities
on its active labels.  Inactive labels need not have distinct images. -/
theorem fieldSum_reindex_of_coefficients {D ι κ : Type} [DecidableEq κ]
    (labels : ℕ → Finset ι) (nativeLabels : ℕ → Finset κ)
    (a : ι → HarmonicBlock D) (b : κ → HarmonicBlock D)
    (e : ℕ → ι → κ)
    (he : ∀ n, Set.InjOn (e n) (labels n : Set ι))
    (hlabels : ∀ n, (labels n).image (e n) = nativeLabels n)
    (hv : ∀ n l, l ∈ labels n → (a l).velocity n = (b (e n l)).velocity n)
    (hc : ∀ n l, l ∈ labels n → SameCarrierAt (a l) (b (e n l)) n) :
    LabelSumBounds.fieldSum labels (fun l => (a l).oscillation) =
      LabelSumBounds.fieldSum nativeLabels (fun l => (b l).oscillation) := by
  funext n p i
  simp only [LabelSumBounds.fieldSum]
  rw [← hlabels n, Finset.sum_image (he n)]
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (congrFun
    (oscillation_eq_at_band_of_coefficients (a l) (b (e n l)) n
      (hv n l hl) (hc n l hl)) p) i

/-! ## The native requested cross for arbitrary physical labels -/

/-- The actual primary and tangent sums agree with the native sums after
bandwise finite reindexing.  This theorem does not reindex `SignedFamily`,
so none of its uniform coefficient bounds acquire a label-dependent constant. -/
theorem native_fields
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P α δ β η) (a : Assembly f)
    (e : ℕ → ι → NativeIndex)
    (he : ∀ n, Set.InjOn (e n) (a.labels n : Set ι))
    (hlabels : ∀ n, (a.labels n).image (e n) = B.labels n)
    (hp : ∀ n l, l ∈ a.labels n →
      (f.primary l).velocity n = (B.primaryBlocks (e n l)).velocity n)
    (hcp : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.primary l) (B.primaryBlocks (e n l)) n)
    (ht : ∀ n l, l ∈ a.labels n →
      (f.tangent l).velocity n = (B.signedBlocks c u (e n l)).velocity n)
    (hct : ∀ n l, l ∈ a.labels n →
      SameCarrierAt (f.tangent l) (B.signedBlocks c u (e n l)) n) :
    primaryField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.primaryBlocks l).oscillation) ∧
    tangentField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.signedBlocks c u l).oscillation) := by
  exact ⟨fieldSum_reindex_of_coefficients a.labels B.labels f.primary B.primaryBlocks
      e he hlabels hp hcp,
    fieldSum_reindex_of_coefficients a.labels B.labels f.tangent (B.signedBlocks c u)
      e he hlabels ht hct⟩

/-! ## The gain for the original family and literal reconstructed state -/

end NavierStokes.BandReindexedSignedMeanGain
