import Tengoku.GeneralStochToDet.stoch_to_det.Race

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The improved seed constant

This file carries the sharpened scalar estimate and the Hellinger mismatch
charge through the four-line seed ledger. The
historical `RaceQuantities` API and its constants remain untouched.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

/-- The improved scalar and unchanged cone estimates combine to give
`D_lab ≤ S + beta d`.
@isnad1 id=le.0h6v.s6.30e63a676b32 from=translated src=- shape=a561e016 vocab=671ee9a2
-/
theorem seedLeak_bound_1771 (R : RaceQuantities1771 D K) :
    R.toRaceQuantities.seedLeak ≤ K.Sinfo + beta1771 * K.dMis := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcone : R.toRaceQuantities.cone ≤ K.dMis / Real.log 2 := by
    exact (le_div_iff₀ hlog).2 R.toRaceQuantities.cone_le_nats
  calc
    R.toRaceQuantities.seedLeak =
        R.toRaceQuantities.scalar + R.toRaceQuantities.cone :=
      R.toRaceQuantities.chain_split
    _ ≤ (K.Sinfo + kappa1771 * K.dMis) +
        K.dMis / Real.log 2 :=
      add_le_add R.scalar_le_1771 hcone
    _ = K.Sinfo + beta1771 * K.dMis := by
      unfold kappa1771 beta1771
      field_simp [hlog.ne']
      ring

end stoch_to_det
