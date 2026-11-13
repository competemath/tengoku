import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MK_RowTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: support separation and finite-window correctness

Row transport moves every mixed row to the cone side.  The cone side has the
explicit lower support `rowMin k`; this supplies all local-finiteness bounds
used by `MKcoeff` and by the final finite-sum interchange.
-/

namespace QseriesFormalization
namespace Ch10

set_option maxHeartbeats 400000

/--
@isnad1 id=le.0h1v.s3.d70d323aed0c from=translated src=- shape=8a62b088 vocab=c6f23c63
-/
theorem rowMin_nonneg (k : ℤ) : 0 ≤ rowMin k := by
  unfold rowMin
  split_ifs with hk
  · nlinarith [sq_nonneg k]
  · have hk' : k ≤ -1 := by omega
    nlinarith [sq_nonneg k]

/--
@isnad1 id=le.0h1v.s3.606d709394af from=translated src=- shape=5e17aa0a vocab=62d8f942
-/
theorem abs_k_le_rowMin (k : ℤ) : |k| ≤ rowMin k := by
  unfold rowMin
  split_ifs with hk
  · rw [abs_of_nonneg hk]
    nlinarith [sq_nonneg k]
  · have hk' : k ≤ -1 := by omega
    rw [abs_of_nonpos (by omega)]
    nlinarith [sq_nonneg k]

/--
@isnad1 id=le.1h2v.s4.8f0155f65def from=translated src=- shape=ae0a97bf vocab=9c32bd74
-/
theorem Hq_ge_rowMin_of_cone {k r : ℤ} (hcone : coneSide k r) :
    rowMin k ≤ Hq k r := by
  rcases hcone with hA | hD
  · have hp : 0 ≤ r * (r + 6 * k + 1) :=
      mul_nonneg hA.2 (by omega)
    simp only [rowMin, ite_eq_left hA.1, Hq, Q]
    nlinarith
  · have hk : ¬ 0 ≤ k := by omega
    have hp : 0 ≤ (r + 1) * (r + 6 * k) :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    simp only [rowMin, ite_eq_right hk, Hq, Q]
    nlinarith

/--
@isnad1 id=eq.1h2v.s4.7f1c4f765f43 from=translated src=- shape=4bb27f63 vocab=0234cd16
-/
theorem rowConeCoeff_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    rowConeCoeff k m = 0 := by
  unfold rowConeCoeff
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [rowFiber, Finset.mem_filter] at hr
  have hmin := Hq_ge_rowMin_of_cone hr.2
  omega

/--
@isnad1 id=eq.1h2v.s4.5242d234c4a0 from=translated src=- shape=4bb27f63 vocab=6e09c11c
-/
theorem rowMixed_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    rowMixedCoeff k m = 0 := by
  rw [row_transport_all, rowConeCoeff_vanish_below hm, neg_zero]

/--
@isnad1 id=eq.1h2v.s4.16890d676af3 from=translated src=- shape=4bb27f63 vocab=fec119a3
-/
theorem coneSignedCoeff_vanish_below {k m : ℤ} (hm : m < rowMin k) :
    coneSignedCoeff k m = 0 := by
  unfold coneSignedCoeff
  rw [rowConeCoeff_vanish_below hm, mul_zero]

/--
@isnad1 id=eq.1h1v.s4.cf3270a13361 from=translated src=- shape=278e0375 vocab=05d60d2c
-/
theorem coneDiffH_vanish_below_zero {m : ℤ} (hm : m < 0) :
    coneDiffH m = 0 := by
  unfold coneDiffH
  apply Finset.sum_eq_zero
  intro k _hk
  apply coneSignedCoeff_vanish_below
  have := rowMin_nonneg k
  omega

/-! ## The exact inner window and its rectangular extension -/

noncomputable def mkGlobalRowCoeff (k T : ℤ) : ℤ :=
  ∑ a ∈ Finset.Icc (-2) T, QoutCoeff a * rowMixedCoeff k (T - a)

/--
@isnad1 id=eq.0h2v.s3.0a611c4f8cce from=translated src=- shape=6c8684e5 vocab=f317e67a
-/
theorem mkRowCoeff_eq_global (k T : ℤ) :
    mkRowCoeff k T = mkGlobalRowCoeff k T := by
  unfold mkRowCoeff mkGlobalRowCoeff
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    have hmin := rowMin_nonneg k
    omega
  · intro a haGlobal haSmall
    rw [Finset.mem_Icc] at haGlobal
    have hlt : T - a < rowMin k := by
      by_contra h
      apply haSmall
      rw [Finset.mem_Icc]
      constructor <;> omega
    rw [rowMixed_vanish_below hlt, mul_zero]

/-! ## Comparing the `m`-window with the global `T`-window -/

/--
@isnad1 id=eq.1h2v.s6.e58585a5c5d3 from=translated src=- shape=b2d9ce30 vocab=a81334e8
-/
theorem coneDiffH_eq_sum_mk_window {T a : ℤ}
    (ha : a ∈ Finset.Icc (-2) T) :
    coneDiffH (T - a) =
      ∑ k ∈ Finset.Icc (-mkKBound T) (mkKBound T),
        coneSignedCoeff k (T - a) := by
  rw [Finset.mem_Icc] at ha
  have hm : 0 ≤ T - a := by omega
  have hcb : (0:ℤ) ≤ coneKBound (T - a) := by
    unfold coneKBound
    have := abs_nonneg (T - a)
    omega
  have hmb : (0:ℤ) ≤ mkKBound T := by
    unfold mkKBound
    have := abs_nonneg T
    omega
  have hvan : ∀ k : ℤ, coneKBound (T - a) < |k| →
      coneSignedCoeff k (T - a) = 0 := by
    intro k hk
    apply coneSignedCoeff_vanish_below
    have hkmin := abs_k_le_rowMin k
    unfold coneKBound at hk
    rw [abs_of_nonneg hm] at hk
    linarith
  have hvan2 : ∀ k : ℤ, mkKBound T < |k| →
      coneSignedCoeff k (T - a) = 0 := by
    intro k hk
    apply coneSignedCoeff_vanish_below
    have hkmin := abs_k_le_rowMin k
    have hT : T ≤ |T| := le_abs_self T
    unfold mkKBound at hk
    linarith
  set B : ℤ := coneKBound (T - a) + mkKBound T with hB
  have h1 : coneDiffH (T - a) =
      ∑ k ∈ Finset.Icc (-B) B, coneSignedCoeff k (T - a) := by
    unfold coneDiffH
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hknot
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Icc] at hknot
      apply hvan
      rcases abs_cases k with ⟨h1a, h2a⟩ | ⟨h1a, h2a⟩ <;> omega
  have h2 : (∑ k ∈ Finset.Icc (-(mkKBound T)) (mkKBound T),
        coneSignedCoeff k (T - a)) =
      ∑ k ∈ Finset.Icc (-B) B, coneSignedCoeff k (T - a) := by
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hknot
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_Icc] at hknot
      apply hvan2
      rcases abs_cases k with ⟨h1a, h2a⟩ | ⟨h1a, h2a⟩ <;> omega
  rw [h1, h2]

end Ch10
end QseriesFormalization
