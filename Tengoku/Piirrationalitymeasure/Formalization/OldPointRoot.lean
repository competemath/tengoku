import Tengoku.Piirrationalitymeasure.Formalization.OldPointPartition
import Tengoku.Piirrationalitymeasure.Formalization.ParameterStationary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual positive stationary root and exact isolation in Appendix A.5. -/

namespace PiIrrationality

def oldStationaryCubic (y : ℝ) : ℝ := 2 * y ^ 3 - 125 * y ^ 2 - 500 * y - 625

/--
@isnad1 id=eq.0h1v.s4.e43d34439d8e from=translated src=- shape=53b14b72 vocab=d0a1253d
-/
theorem oldPoint_stationary (y : ℝ) :
    3 * parameterStationary oldPoint y = oldStationaryCubic y := by
  dsimp [parameterStationary, oldPoint, oldStationaryCubic]
  ring

noncomputable def oldRootLower : ℝ := 6633950152462140818 / 10 ^ 17

noncomputable def oldRootUpper : ℝ := 6633950152462140819 / 10 ^ 17

/--
@isnad1 id=and.0h0v.s4.c66d2295f05b from=translated src=- shape=31a23145 vocab=3a4a45a8
-/
theorem oldRoot_endpoint_signs :
    oldStationaryCubic oldRootLower < 0 ∧ 0 < oldStationaryCubic oldRootUpper := by
  constructor <;> norm_num [oldStationaryCubic, oldRootLower, oldRootUpper]

/--
@isnad1 id=strictmo.0h0v.s5.dddc1c5f3cbe from=translated src=- shape=987ab001 vocab=a81353f4
-/
theorem oldStationaryCubic_strictMonoOn :
    StrictMonoOn oldStationaryCubic (Set.Ici (125 / 2 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by unfold oldStationaryCubic; fun_prop)
  intro x hx
  have hx' : 125 / 2 ≤ x := by simpa using (interior_subset hx : x ∈ Set.Ici (125 / 2 : ℝ))
  have hd : HasDerivAt oldStationaryCubic (6 * x ^ 2 - 250 * x - 500) x := by
    have h := (((((hasDerivAt_id x).pow 3).const_mul 2).sub
      (((hasDerivAt_id x).pow 2).const_mul 125)).sub
      ((hasDerivAt_id x).const_mul 500)).sub_const 625
    convert! h using 1 <;> simp only [oldStationaryCubic, Pi.sub_apply,
      Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one, mul_one] <;> ring
  rw [hd.deriv]
  nlinarith [sq_nonneg (x - 125 / 2)]

/--
@isnad1 id=lt.2h1v.s5.5a4efd578c39 from=translated src=- shape=66e1f691 vocab=2539f5af
-/
theorem oldStationaryCubic_root_gt {y : ℝ} (hy : 0 < y) (hroot : oldStationaryCubic y = 0) :
    125 / 2 < y := by
  by_contra h
  have hterm : y ^ 2 * (2 * y - 125) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  unfold oldStationaryCubic at hroot
  nlinarith

/--
@isnad1 id=existsun.0h0v.s4.1185bc00f2db from=translated src=- shape=bdb07295 vocab=dadf65e0
-/
theorem oldStationaryCubic_unique_positive_root :
    ∃! y : ℝ, 0 < y ∧ oldStationaryCubic y = 0 := by
  have hcont : ContinuousOn oldStationaryCubic (Set.Icc oldRootLower oldRootUpper) := by
    unfold oldStationaryCubic
    fun_prop
  obtain ⟨y, hy, hroot⟩ := intermediate_value_Icc
    (show oldRootLower ≤ oldRootUpper by norm_num [oldRootLower, oldRootUpper]) hcont
    ⟨oldRoot_endpoint_signs.1.le, oldRoot_endpoint_signs.2.le⟩
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num [oldRootLower]) hy.1
  refine ⟨y, ⟨hy0, hroot⟩, ?_⟩
  intro z hz
  exact oldStationaryCubic_strictMonoOn.injOn
    (oldStationaryCubic_root_gt hz.1 hz.2).le
    (oldStationaryCubic_root_gt hy0 hroot).le (hz.2.trans hroot.symm)

noncomputable def oldStationaryRoot : ℝ :=
  Classical.choose oldStationaryCubic_unique_positive_root

/--
@isnad1 id=and.0h0v.s4.2ad67c64ad3b from=translated src=- shape=3728abe1 vocab=a536dfde
-/
theorem oldStationaryRoot_spec : 0 < oldStationaryRoot ∧ oldStationaryCubic oldStationaryRoot = 0 :=
  (Classical.choose_spec oldStationaryCubic_unique_positive_root).1

/--
@isnad1 id=and.0h0v.s3.52fc4875d956 from=translated src=- shape=9cf45692 vocab=36a3aa2f
-/
theorem oldStationaryRoot_isolation : oldRootLower < oldStationaryRoot ∧
    oldStationaryRoot < oldRootUpper := by
  have hroot := oldStationaryRoot_spec
  have hy : oldStationaryRoot ∈ Set.Ici (125 / 2 : ℝ) :=
    (oldStationaryCubic_root_gt hroot.1 hroot.2).le
  have hL : oldRootLower ∈ Set.Ici (125 / 2 : ℝ) := by
    norm_num [Set.mem_Ici, oldRootLower]
  have hU : oldRootUpper ∈ Set.Ici (125 / 2 : ℝ) := by
    norm_num [Set.mem_Ici, oldRootUpper]
  constructor
  · by_contra h
    have hm := oldStationaryCubic_strictMonoOn.monotoneOn hy hL (le_of_not_gt h)
    linarith [oldRoot_endpoint_signs.1]
  · by_contra h
    have hm := oldStationaryCubic_strictMonoOn.monotoneOn hU hy (le_of_not_gt h)
    linarith [oldRoot_endpoint_signs.2]

/--
@isnad1 id=lt.0h0v.s6.89631c9ee91a from=translated src=- shape=5f4ce588 vocab=d16179b5
-/
theorem oldStationaryRoot_simple :
    0 < 6 * oldStationaryRoot ^ 2 - 250 * oldStationaryRoot - 500 := by
  have hy := oldStationaryCubic_root_gt oldStationaryRoot_spec.1 oldStationaryRoot_spec.2
  nlinarith [sq_nonneg (oldStationaryRoot - 125 / 2)]

/--
@isnad1 id=eq.0h0v.s8.5158554e3bde from=translated src=- shape=722e33d9 vocab=d13119ac
-/
theorem oldStationaryCubic_discriminant :
    (-125 : ℤ) ^ 2 * (-500) ^ 2 - 4 * 2 * (-500) ^ 3 -
      4 * (-125) ^ 3 * (-625) - 27 * 2 ^ 2 * (-625) ^ 2 +
      18 * 2 * (-125) * (-500) * (-625) = -1425000000 := by
  norm_num

end PiIrrationality
