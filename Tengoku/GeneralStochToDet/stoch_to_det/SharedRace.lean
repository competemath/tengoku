import Tengoku.GeneralStochToDet.stoch_to_det.Race
import Tengoku.GeneralStochToDet.stoch_to_det.Ledger96

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Final assembly of the all-label shared-race estimate

Everything in this file is finite-source bookkeeping.  The analytic input is
the coordinate moment `clockCoordinateIntegral_le`, proved by the exact
winner/loser clock analysis in `Race.lean`.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

/-- The one analytic clock estimate still abstracted by this assembly file.

The cardinality hypothesis deliberately lives inside the proposition: the
singleton label alphabet is discharged without invoking any coordinate
analysis.-/
def HasClockCoordinateBound (κ : Type)
    [Fintype κ] [DecidableEq κ] [Nonempty κ] : Prop :=
  ∀ (π : κ → ℝ), IsPMF π → (∀ i, 0 < π i) →
    2 ≤ Fintype.card κ → ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i

/-- Row-reference-loss assembly for one finite source context.
@isnad1 id=le.5h4v.s7.c7ccf6209a77 from=translated src=- shape=f9439eb7 vocab=fb2d738c
-/
theorem clockSharedRaceEntropy_le
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoordinate : HasClockCoordinateBound κ) :
    clockSharedRaceEntropy μ r ≤
      2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        categoricalMismatch μ r := by
  let π : κ → ℝ := posteriorMean μ r
  have hπ : IsPMF π := posteriorMean_isPMF_of_support hμ hr
  have hπpos : ∀ i, 0 < π i := posteriorMean_pos_of_support hμ hrpos
  have hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i :=
    hcoordinate π hπ hπpos hk
  apply clockSharedRaceEntropy_le_of_referenceLoss hμ hr hrpos
  · intro z hz
    exact integrable_log_inv_referencePMF_clockArgmin
      π (r z) hπ hπpos (hr z hz) (hrpos z hz) hk
  · intro z hz
    exact referenceLossIntegral_le_of_coordinate
      π (r z) hπ hπpos (hr z hz) (hrpos z hz) hk hcoord

/-- Nontrivial finite label alphabets satisfy the Gumbel shared-race theorem
as soon as the coordinate moment is available.
@isnad1 id=hasshare.2h2v.s5.e07a3934b4fe from=translated src=- shape=2fd866a4 vocab=7402aea5
-/
theorem hasSharedRaceBound_of_two_le_card
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (hk : 2 ≤ Fintype.card κ)
    (hcoordinate : HasClockCoordinateBound κ) :
    HasSharedRaceBound Ω κ := by
  intro μ r hμ hr hrpos
  rw [sharedRaceEntropy_eq_clockSharedRaceEntropy hrpos]
  exact clockSharedRaceEntropy_le hμ hr hrpos hk hcoordinate

/-- Singleton/nontrivial split for the universal shared-race theorem.
@isnad1 id=hasshare.1h2v.s5.d9f4a3416082 from=translated src=- shape=6e211c33 vocab=52d26b6d
-/
theorem hasSharedRaceBound_of_clockCoordinateBound
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (hcoordinate : HasClockCoordinateBound κ) :
    HasSharedRaceBound Ω κ := by
  classical
  by_cases hk : 2 ≤ Fintype.card κ
  · exact hasSharedRaceBound_of_two_le_card hk hcoordinate
  · have hcard : Fintype.card κ ≤ 1 := by omega
    exact @hasSharedRaceBound_of_subsingleton Ω κ _ _ _ _ _
      (Fintype.card_le_one_iff_subsingleton.mp hcard)

/-- Uniform coordinate interface, quantified over all finite nonempty label
alphabets exactly as required by the `96` ledger.-/
def UniversalClockCoordinateBound : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ],
    HasClockCoordinateBound κ

/-- The winner/loser pair-clock theorem supplies the coordinate interface for
every finite nonempty label alphabet.
@isnad1 id=universa.0h0v.s0.c5949cda0ff7 from=translated src=- shape=45709ebd vocab=c5949cda
-/
theorem universalClockCoordinateBound : UniversalClockCoordinateBound :=
  fun _κ _ _ _ π hπ hπpos hk i =>
    clockCoordinateIntegral_le π hπ hπpos hk i

/-- The shared-race theorem for every source-supported strictly positive
posterior family, including the singleton label alphabet.
@isnad1 id=hasshare.0h2v.s4.f9d59c2bb1a2 from=translated src=- shape=cdf5ba4d vocab=d463fc85
-/
theorem hasSharedRaceBound
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ] :
    HasSharedRaceBound Ω κ :=
  hasSharedRaceBound_of_clockCoordinateBound
    (universalClockCoordinateBound κ)

end SharedRace

end stoch_to_det
