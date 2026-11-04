import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.EntropyTopology
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ObjectiveContinuity
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Support
import Tengoku.Seed.Analysis.Normed.Lp.LpEquiv
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Attainment on a finite alphabet by compactness of the actual ℓ¹ simplex. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι : Type*}

/-- The point mass at a specified symbol, used to witness feasibility for every h≥0.-/
noncomputable def pointMass (i : ι) : ProbabilityVector ι := by
  classical
  exact ofHasSum (fun j => if j = i then 1 else 0) (by intro j; split_ifs <;> norm_num)
    (hasSum_ite_eq i 1)

/--
@isnad1 id=eq.0h2v.s4.ebd77f5c27b4 from=translated src=- shape=12ebe8e5 vocab=bd367617
-/
@[simp] theorem coord_pointMass_self (i : ι) : (pointMass i).coord i = 1 := by
  classical
  simp [pointMass]

/--
@isnad1 id=eq.1h3v.s4.55c2d95891f9 from=translated src=- shape=f9ed3753 vocab=bd367617
-/
@[simp] theorem coord_pointMass_of_ne (i j : ι) (hji : j ≠ i) :
    (pointMass i).coord j = 0 := by
  classical
  simp [pointMass, hji]

/--
@isnad1 id=eq.0h2v.s4.ebb717c7d64d from=translated src=- shape=d0dfd432 vocab=ab7f1f09
-/
@[simp] theorem entropy_pointMass (i : ι) : (pointMass i).entropy = 0 := by
  apply (pointMass i).entropy_eq_zero_iff.mpr
  exact ⟨i, by simp, fun j hj => by simp [hj]⟩

/--
@isnad1 id=mem.0h3v.s4.fe5204c6c462 from=translated src=- shape=ad9ae32c vocab=6cdb84be
-/
theorem pointMass_feasible (i : ι) (h : ℝ) : pointMass i ∈ (Feasible h : Set (ProbabilityVector ι)) := by
  simp [Feasible]

/--
@isnad1 id=nonempty.0h2v.s3.20bea602218e from=translated src=- shape=743405dd vocab=edf3b2cc
-/
theorem feasible_nonempty [Nonempty ι] (h : ℝ) :
    (Feasible h : Set (ProbabilityVector ι)).Nonempty :=
  ⟨pointMass (Classical.choice inferInstance), pointMass_feasible _ h⟩

section Finite
variable [Fintype ι]

/-- The finite probability simplex is closed in its ambient ℓ¹ space.
@isnad1 id=isclosed.0h1v.s10.addd9459ec13 from=translated src=- shape=d8f04d41 vocab=95d11793
-/
theorem isClosed_simplex : IsClosed
    {p : lp (fun _ : ι => ℝ) 1 | (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1} := by
  have hnonneg : IsClosed {p : lp (fun _ : ι => ℝ) 1 | ∀ i, 0 ≤ p i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous
  have hsum : Continuous (fun p : lp (fun _ : ι => ℝ) 1 => ∑' i, p i) := by
    simp only [tsum_fintype]
    exact continuous_finsetSum _ (fun i _ => (lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous)
  exact hnonneg.inter (isClosed_eq hsum continuous_const)

/--
@isnad1 id=iscompac.0h1v.s10.e59846c88367 from=translated src=- shape=d8f04d41 vocab=7b329137
-/
theorem isCompact_simplex : IsCompact
    {p : lp (fun _ : ι => ℝ) 1 | (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1} := by
  let : FiniteDimensional ℝ (lp (fun _ : ι => ℝ) 1) :=
    (lpPiLpₗᵢ (fun _ : ι => ℝ) ℝ (p := 1)).symm.toLinearEquiv.finiteDimensional
  apply (isCompact_closedBall (0 : lp (fun _ : ι => ℝ) 1) 1).of_isClosed_subset isClosed_simplex
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right,
    lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs,
    abs_of_nonneg (hp.1 _), hp.2, le_refl]

/--
@isnad1 id=compacts.0h1v.s4.22a5c8f8d6dc from=translated src=- shape=1666ae32 vocab=fdc03904
-/
noncomputable instance compactSpace : CompactSpace (ProbabilityVector ι) :=
  isCompact_iff_compactSpace.mp isCompact_simplex

/--
@isnad1 id=iscompac.0h2v.s4.6b17d0c7a285 from=translated src=- shape=743405dd vocab=2ad2d196
-/
theorem isCompact_feasible (h : ℝ) : IsCompact (Feasible h : Set (ProbabilityVector ι)) :=
  (isClosed_feasible h).isCompact

/-- The finite-alphabet attainment assertion of the main theorem, including h=0.
The conclusion is a genuine maximum over all feasible vectors.
@isnad1 id=ex.1h3v.s6.6cff5664cdd5 from=translated src=- shape=2778b605 vocab=fe5b10b7
-/
theorem exists_global_maximizer_finite [Nonempty ι] (t : ℕ) (h : ℝ) (_hh : 0 ≤ h) :
    ∃ p : ProbabilityVector ι, p ∈ Feasible h ∧
      ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  exact (isCompact_feasible h).exists_isMaxOn (feasible_nonempty h)
    (continuous_objective t).continuousOn

end Finite
end EntropyConstrainedMissingMass.ProbabilityVector
