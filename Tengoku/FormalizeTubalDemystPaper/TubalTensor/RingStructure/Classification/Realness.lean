import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.StarRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/RingStructure/Classification/Realness.lean
  Definition 12 (Realness) and basic properties.
-/

namespace TubalTensor

open Complex Matrix

variable {n : ℕ}

/-! ## Definition 12: Realness -/

/-- The realness of a TubalData is the number of real rows in M.
    (Definition 12 in the paper)-/
noncomputable def realness (td : TubalData n) : ℕ :=
  (Finset.univ.filter (fun i => ∀ j, (td.M i j).im = 0)).card

/-- A tubal ring K_M is *fully real* (or *real-like*) if its realness equals n,
    i.e., every row of M is real. (Definition 12 in the paper)-/
def IsFullyReal (td : TubalData n) : Prop := realness td = n

/-- Realness is at most n.
@isnad1 id=le.0h2v.s3.0c12700a684e from=translated src=- shape=26d77ceb vocab=a39e000a
-/
theorem realness_le (td : TubalData n) : realness td ≤ n := by
  unfold realness
  calc _ ≤ Finset.card Finset.univ := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

end TubalTensor
