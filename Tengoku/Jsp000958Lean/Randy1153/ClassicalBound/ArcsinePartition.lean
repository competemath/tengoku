import Tengoku.Jsp000958Lean.Randy1153.ClassicalBound.ArcsineBins

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit geometric arcsine partitions

For q > 1, let c be the positive cubic Chebyshev floor and set

    level i = min (q^i c) 1.

The half-angle endpoints are zero followed by the arcsines of levels
zero through K.  Thus the construction has K+1 bins.  If q^K c ≥ 1,
the final endpoint is pi/2.  This file proves the construction satisfies
the exact HalfArcsinePartition interface.

The endpoint zero is kept separate because c is positive: starting the
geometric levels themselves at index zero would incorrectly begin at
arcsin c rather than at the endpoint x = 1.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- The clipped geometric scale level before applying arcsine.-/
def geometricScaleLevel (d : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  min (q ^ i * cubicChebyshevFloor d) 1

/--
@isnad1 id=le.1h3v.s4.078a30e71aa4 from=translated src=- shape=c318d537 vocab=52ba6d3d
-/
lemma geometricScaleLevel_nonneg {d i : ℕ} {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ geometricScaleLevel d q i := by
  rw [geometricScaleLevel]
  exact le_min
    (mul_nonneg (pow_nonneg hq _) (cubicChebyshevFloor_nonneg d))
    zero_le_one

/--
@isnad1 id=le.0h3v.s4.eff3176bac33 from=translated src=- shape=141332ea vocab=52ba6d3d
-/
lemma geometricScaleLevel_le_one (d : ℕ) (q : ℝ) (i : ℕ) :
    geometricScaleLevel d q i ≤ 1 :=
  min_le_right _ _

/--
@isnad1 id=monotone.1h2v.s4.a48f6dd67b2e from=translated src=- shape=093e6b8c vocab=07b434f5
-/
lemma geometricScaleLevel_mono {d : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    Monotone (geometricScaleLevel d q) := by
  intro i j hij
  rw [geometricScaleLevel, geometricScaleLevel]
  apply min_le_min
  · exact mul_le_mul_of_nonneg_right
      (pow_right_mono₀ hq hij) (cubicChebyshevFloor_nonneg d)
  · exact le_rfl

/--
@isnad1 id=le.1h3v.s5.6695ccdd2031 from=translated src=- shape=82945e52 vocab=cfdbb549
-/
lemma geometricScaleLevel_succ_le_mul {d i : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    geometricScaleLevel d q (i + 1) ≤ q * geometricScaleLevel d q i := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  by_cases hi : q ^ i * cubicChebyshevFloor d ≤ 1
  · rw [geometricScaleLevel, geometricScaleLevel, min_eq_left hi]
    calc
      min (q ^ (i + 1) * cubicChebyshevFloor d) 1 ≤
          q ^ (i + 1) * cubicChebyshevFloor d := min_le_left _ _
      _ = q * (q ^ i * cubicChebyshevFloor d) := by
        rw [pow_succ]
        ring
  · have hi' : 1 ≤ q ^ i * cubicChebyshevFloor d := le_of_not_ge hi
    simp only [geometricScaleLevel]
    rw [min_eq_right hi']
    exact (geometricScaleLevel_le_one d q (i + 1)).trans (by simpa using hq)

/--
@isnad1 id=eq.1h3v.s5.fc1ee9964838 from=translated src=- shape=bd60ca23 vocab=638e8618
-/
lemma geometricScaleLevel_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricScaleLevel d q K = 1 := by
  exact min_eq_right hterminal

/-- The natural-index endpoint sequence: zero first, then arcsines of the
geometric scale levels.-/
def geometricHalfAngle (d : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0
  else Real.arcsin (geometricScaleLevel d q (j - 1))

/--
@isnad1 id=eq.0h2v.s4.0d9f2c976204 from=translated src=- shape=c1a5d958 vocab=60249fb5
-/
@[simp]
lemma geometricHalfAngle_zero (d : ℕ) (q : ℝ) :
    geometricHalfAngle d q 0 = 0 := by
  simp [geometricHalfAngle]

/--
@isnad1 id=eq.0h3v.s4.1124db7ab0de from=translated src=- shape=ca8a6f3d vocab=3855dc43
-/
lemma geometricHalfAngle_succ (d : ℕ) (q : ℝ) (i : ℕ) :
    geometricHalfAngle d q (i + 1) =
      Real.arcsin (geometricScaleLevel d q i) := by
  simp [geometricHalfAngle]

/--
@isnad1 id=le.1h3v.s4.9e69b0384be4 from=translated src=- shape=c318d537 vocab=b1939811
-/
lemma geometricHalfAngle_nonneg {d j : ℕ} {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ geometricHalfAngle d q j := by
  by_cases hj : j = 0
  · simp [hj]
  · rw [geometricHalfAngle, ite_eq_right hj]
    exact Real.arcsin_nonneg.mpr (geometricScaleLevel_nonneg hq)

/--
@isnad1 id=monotone.1h2v.s4.893f6eed0b6a from=translated src=- shape=093e6b8c vocab=116d0675
-/
lemma geometricHalfAngle_mono {d : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    Monotone (geometricHalfAngle d q) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    exact geometricHalfAngle_nonneg (zero_le_one.trans hq)
  · have hj : j ≠ 0 := by omega
    rw [geometricHalfAngle, ite_eq_right hi, geometricHalfAngle, ite_eq_right hj]
    exact Real.arcsin_le_arcsin
      (geometricScaleLevel_mono hq (Nat.sub_le_sub_right hij 1))

/--
@isnad1 id=eq.1h3v.s6.dcfec70569b5 from=translated src=- shape=953f05af vocab=994bff80
-/
lemma geometricHalfAngle_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricHalfAngle d q (K + 1) = Real.pi / 2 := by
  rw [geometricHalfAngle_succ, geometricScaleLevel_terminal hterminal,
    Real.arcsin_one]

/--
@isnad1 id=le.0h3v.s4.05a3a8690909 from=translated src=- shape=fbf07d71 vocab=16d01e74
-/
lemma geometricHalfAngle_le_pi_div_two (d : ℕ) (q : ℝ) (j : ℕ) :
    geometricHalfAngle d q j ≤ Real.pi / 2 := by
  by_cases hj : j = 0
  · simp [hj]
    positivity
  · rw [geometricHalfAngle, ite_eq_right hj]
    exact Real.arcsin_le_pi_div_two _

/-- At a geometric angle endpoint, the clipped scale is the maximum of
that level and the floor.
@isnad1 id=eq.1h3v.s5.904c5831e26f from=translated src=- shape=dcb7af80 vocab=2841df9b
-/
lemma clippedArcsineScale_cos_geometricHalfAngle_succ
    (d i : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    clippedArcsineScale d
        (Real.cos (geometricHalfAngle d q (i + 1))) =
      max (geometricScaleLevel d q i) (cubicChebyshevFloor d) := by
  rw [geometricHalfAngle_succ,
    clippedArcsineScale_cos
      (Real.arcsin_nonneg.mpr (geometricScaleLevel_nonneg hq))
      (Real.arcsin_le_pi_div_two _ |>.trans
        (by linarith [Real.pi_pos]))]
  rw [Real.sin_arcsin
    (by linarith [geometricScaleLevel_nonneg (d := d) (i := i) hq])
    (geometricScaleLevel_le_one d q i)]

/--
@isnad1 id=eq.0h2v.s4.79eddf10150e from=translated src=- shape=85f09f4b vocab=47d323d5
-/
lemma clippedArcsineScale_cos_geometricHalfAngle_zero (d : ℕ) (q : ℝ) :
    clippedArcsineScale d
        (Real.cos (geometricHalfAngle d q 0)) =
      cubicChebyshevFloor d := by
  simp [geometricHalfAngle, clippedArcsineScale,
    cubicChebyshevFloor_nonneg]

/--
@isnad1 id=le.1h3v.s5.cc5b733349ac from=translated src=- shape=982d4e7d vocab=8ae8eed9
-/
lemma max_geometricScaleLevel_floor_succ_le_mul
    {d i : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    max (geometricScaleLevel d q (i + 1)) (cubicChebyshevFloor d) ≤
      q * max (geometricScaleLevel d q i) (cubicChebyshevFloor d) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  apply max_le
  · exact (geometricScaleLevel_succ_le_mul hq).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hq0)
  · calc
      cubicChebyshevFloor d ≤ q * cubicChebyshevFloor d := by
        nlinarith [cubicChebyshevFloor_nonneg d]
      _ ≤ q * max (geometricScaleLevel d q i)
          (cubicChebyshevFloor d) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hq0

/-- The explicit K+1-bin half partition generated by geometric scale
levels through exponent K.-/
def geometricHalfArcsinePartition (d K : ℕ) (q : ℝ)
    (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    HalfArcsinePartition d (K + 1) q where
  positive_bins := Nat.succ_pos K
  angle j := geometricHalfAngle d q j.val
  monotone_angle := by
    intro i j hij
    exact geometricHalfAngle_mono (d := d) hq.le hij
  angle_zero := geometricHalfAngle_zero d q
  angle_last := geometricHalfAngle_terminal hterminal
  scale_ratio := by
    intro i
    by_cases hi : i.val = 0
    · have hiright : (angleBinRight i).val = 1 := by
        simp [angleBinRight, hi]
      have hileft : (angleBinLeft i).val = 0 := by
        simp [angleBinLeft, hi]
      rw [show geometricHalfAngle d q (angleBinRight i).val =
          geometricHalfAngle d q 1 by rw [hiright],
        show geometricHalfAngle d q (angleBinLeft i).val =
          geometricHalfAngle d q 0 by rw [hileft],
        clippedArcsineScale_cos_geometricHalfAngle_succ d 0
          (zero_le_one.trans hq.le),
        clippedArcsineScale_cos_geometricHalfAngle_zero]
      have hlevel0 :
          geometricScaleLevel d q 0 ≤ cubicChebyshevFloor d := by
        rw [geometricScaleLevel, pow_zero, one_mul]
        exact min_le_left _ _
      rw [max_eq_right hlevel0]
      exact (le_mul_of_one_le_left
        (cubicChebyshevFloor_nonneg d) hq.le)
    · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := by
        exact ⟨i.val - 1, by omega⟩
      have hiright : (angleBinRight i).val = j + 2 := by
        simp [angleBinRight, hj]
      have hileft : (angleBinLeft i).val = j + 1 := by
        simp [angleBinLeft, hj]
      rw [show geometricHalfAngle d q (angleBinRight i).val =
          geometricHalfAngle d q (j + 2) by rw [hiright],
        show geometricHalfAngle d q (angleBinLeft i).val =
          geometricHalfAngle d q (j + 1) by rw [hileft],
        show j + 2 = (j + 1) + 1 by omega,
        clippedArcsineScale_cos_geometricHalfAngle_succ d (j + 1)
          (zero_le_one.trans hq.le),
        clippedArcsineScale_cos_geometricHalfAngle_succ d j
          (zero_le_one.trans hq.le)]
      exact max_geometricScaleLevel_floor_succ_le_mul hq.le

/-- The explicit construction inherits the exact full reflected
length-over-scale budget.
@isnad1 id=le.2h3v.s7.e448a11e9064 from=translated src=- shape=a1f11dab vocab=7063506c
-/
theorem geometricPartition_full_budget_le
    {d K : ℕ} {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    2 * (∑ i : Fin (K + 1),
      cosineBinLength (geometricHalfArcsinePartition d K q hq hterminal).angle i /
        cosineBinLowerScale d
          (geometricHalfArcsinePartition d K q hq hterminal).angle i) ≤
      q * Real.pi :=
  (geometricHalfArcsinePartition d K q hq hterminal).two_mul_sum_cosineBinLength_div_lowerScale_le

/-- The actual clipped-scale threshold attached to geometric level i.-/
def geometricScaleThreshold (d : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  max (geometricScaleLevel d q i) (cubicChebyshevFloor d)

/--
@isnad1 id=eq.1h3v.s5.ee9851803a79 from=translated src=- shape=47e7c153 vocab=62b15a32
-/
lemma geometricScaleThreshold_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricScaleThreshold d q K =
      max 1 (cubicChebyshevFloor d) := by
  rw [geometricScaleThreshold,
    geometricScaleLevel_terminal hterminal]

/-- Every clipped scale is below the terminal threshold once the geometric
levels have reached one.
@isnad1 id=le.1h4v.s5.d825fa752048 from=translated src=- shape=09bc3a16 vocab=59aeca5d
-/
lemma clippedArcsineScale_le_terminalThreshold {d K : ℕ} {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤ geometricScaleThreshold d q K := by
  rw [geometricScaleThreshold_terminal hterminal, clippedArcsineScale]
  apply max_le_max
  · rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg x]
  · exact le_rfl

/-- Some geometric threshold with index at most K contains every real
point.
@isnad1 id=ex.1h4v.s5.0c64921f4c8f from=translated src=- shape=ee067220 vocab=59aeca5d
-/
lemma exists_scaleThreshold_index {d K : ℕ} {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    ∃ i : ℕ, i ≤ K ∧
      clippedArcsineScale d x ≤ geometricScaleThreshold d q i :=
  ⟨K, le_rfl, clippedArcsineScale_le_terminalThreshold hterminal⟩

/-- Least geometric scale shell containing x.  The terminal hypothesis
makes this a total function into the K+1 half-shell indices.-/
noncomputable def geometricScaleBinIndex (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) : Fin (K + 1) :=
  ⟨Nat.find (exists_scaleThreshold_index (d := d) (K := K)
      (q := q) (x := x) hterminal),
    by
      have hspec := Nat.find_spec
        (exists_scaleThreshold_index (d := d) (K := K)
          (q := q) (x := x) hterminal)
      omega⟩

/--
@isnad1 id=le.1h4v.s6.fdbbb2c1a5e4 from=translated src=- shape=9df33848 vocab=dd16ecd6
-/
lemma clippedArcsineScale_le_assignedThreshold
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤
      geometricScaleThreshold d q
        (geometricScaleBinIndex d K q x hterminal).val := by
  exact (Nat.find_spec
    (exists_scaleThreshold_index (d := d) (K := K)
      (q := q) (x := x) hterminal)).2

/--
@isnad1 id=le.1h3v.s5.0addc8851424 from=translated src=- shape=82945e52 vocab=4d933eae
-/
lemma geometricScaleThreshold_succ_le_mul {d i : ℕ} {q : ℝ}
    (hq : 1 ≤ q) :
    geometricScaleThreshold d q (i + 1) ≤
      q * geometricScaleThreshold d q i := by
  simpa only [geometricScaleThreshold] using
    (max_geometricScaleLevel_floor_succ_le_mul (d := d) (i := i) hq)

/-- Lower scale attached to a shell.  The first shell starts at the cubic
floor; later shells start at the preceding threshold.-/
def geometricBinLowerScale (d : ℕ) (q : ℝ) {K : ℕ}
    (i : Fin (K + 1)) : ℝ :=
  if i.val = 0 then cubicChebyshevFloor d
  else geometricScaleThreshold d q (i.val - 1)

/--
@isnad1 id=lt.0h4v.s5.2971157994b8 from=translated src=- shape=563de37f vocab=71b4dfcd
-/
lemma geometricBinLowerScale_pos (d : ℕ) {q : ℝ} {K : ℕ}
    (i : Fin (K + 1)) :
    0 < geometricBinLowerScale d q i := by
  rw [geometricBinLowerScale]
  split_ifs
  · exact cubicChebyshevFloor_pos d
  · exact (cubicChebyshevFloor_pos d).trans_le (le_max_right _ _)

/-- The shell lower scales used by the canonical assignment are exactly
the lower scales of the explicit cosine bins.
@isnad1 id=eq.2h4v.s6.421b2efe6cb7 from=translated src=- shape=cd80b3cd vocab=e208ff3f
-/
lemma geometricBinLowerScale_eq_cosineBinLowerScale
    (d K : ℕ) {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (i : Fin (K + 1)) :
    geometricBinLowerScale d q i =
      cosineBinLowerScale d
        (geometricHalfArcsinePartition d K q hq hterminal).angle i := by
  change geometricBinLowerScale d q i =
    clippedArcsineScale d
      (Real.cos (geometricHalfAngle d q (angleBinLeft i).val))
  by_cases hi : i.val = 0
  · have hleft : (angleBinLeft i).val = 0 := by
      simp [angleBinLeft, hi]
    rw [geometricBinLowerScale, ite_eq_left hi,
      show geometricHalfAngle d q (angleBinLeft i).val =
        geometricHalfAngle d q 0 by rw [hleft],
      clippedArcsineScale_cos_geometricHalfAngle_zero]
  · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
    have hleft : (angleBinLeft i).val = j + 1 := by
      simp [angleBinLeft, hj]
    rw [geometricBinLowerScale, ite_eq_right hi,
      show geometricHalfAngle d q (angleBinLeft i).val =
        geometricHalfAngle d q (j + 1) by rw [hleft],
      clippedArcsineScale_cos_geometricHalfAngle_succ d j
        (zero_le_one.trans hq.le),
      geometricScaleThreshold, hj, Nat.add_sub_cancel]

/-- Minimality of the assigned threshold gives a strict lower bound by the
preceding threshold away from the first shell.
@isnad1 id=lt.2h4v.s6.0b48004f16a7 from=translated src=- shape=0af2562c vocab=d285558b
-/
lemma previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (hi : (geometricScaleBinIndex d K q x hterminal).val ≠ 0) :
    geometricScaleThreshold d q
        ((geometricScaleBinIndex d K q x hterminal).val - 1) <
      clippedArcsineScale d x := by
  let hex := exists_scaleThreshold_index (d := d) (K := K)
    (q := q) (x := x) hterminal
  let j := Nat.find hex
  have hjeq :
      (geometricScaleBinIndex d K q x hterminal).val = j := rfl
  have hjpos : 0 < j := by
    rw [hjeq] at hi
    omega
  by_contra h
  have hle :
      clippedArcsineScale d x ≤ geometricScaleThreshold d q (j - 1) :=
    not_lt.mp h
  have hspec := Nat.find_spec hex
  have hcand :
      (j - 1) ≤ K ∧
        clippedArcsineScale d x ≤ geometricScaleThreshold d q (j - 1) :=
    ⟨by omega, hle⟩
  have hmin : j ≤ j - 1 := Nat.find_min' hex hcand
  omega

/-- Every assigned point lies above its shell lower scale.
@isnad1 id=le.1h4v.s5.9a066efc4ba5 from=translated src=- shape=c14ebc9e vocab=ec8f8c10
-/
lemma geometricBinLowerScale_le_assignedScale
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricBinLowerScale d q
        (geometricScaleBinIndex d K q x hterminal) ≤
      clippedArcsineScale d x := by
  rw [geometricBinLowerScale]
  split_ifs with hi
  · exact le_max_right _ _
  · exact (previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
      d K q x hterminal hi).le

/-- The upper threshold of a shell is at most q times its lower scale.
@isnad1 id=le.1h4v.s6.28c103392084 from=translated src=- shape=95e395d8 vocab=8e27fad8
-/
lemma assignedThreshold_le_mul_geometricBinLowerScale
    (d K : ℕ) {q : ℝ} (hq : 1 ≤ q) (i : Fin (K + 1)) :
    geometricScaleThreshold d q i.val ≤ q * geometricBinLowerScale d q i := by
  rw [geometricBinLowerScale]
  split_ifs with hi
  · have hlevel0 :
        geometricScaleLevel d q 0 ≤ cubicChebyshevFloor d := by
      rw [geometricScaleLevel, pow_zero, one_mul]
      exact min_le_left _ _
    rw [show i.val = 0 from hi, geometricScaleThreshold,
      max_eq_right hlevel0]
    exact le_mul_of_one_le_left (cubicChebyshevFloor_nonneg d) hq
  · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    exact geometricScaleThreshold_succ_le_mul hq

/-- Assigned scales oscillate by at most q inside every canonical shell.
@isnad1 id=le.2h4v.s6.1aa30bc1e4c3 from=translated src=- shape=ee0a6712 vocab=ec8f8c10
-/
theorem assignedScale_le_mul_geometricBinLowerScale
    (d K : ℕ) {q x : ℝ} (hq : 1 ≤ q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤ q * geometricBinLowerScale d q
      (geometricScaleBinIndex d K q x hterminal) := by
  exact (clippedArcsineScale_le_assignedThreshold
    d K q x hterminal).trans
      (assignedThreshold_le_mul_geometricBinLowerScale d K hq _)

/-- Side and least scale shell form a canonical full-interval bin label.
False is the negative half and true is the nonnegative half; hence zero is
assigned only once.-/
noncomputable def arcsineBinAssignment (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    Bool × Fin (K + 1) :=
  (decide (0 ≤ x), geometricScaleBinIndex d K q x hterminal)

/-- The set-theoretic bin determined by a canonical label.  These are the
half-open geometric scale shells, split by sign.-/
def arcsineAssignedBin (d K : ℕ) (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1)) : Set ℝ :=
  {x | arcsineBinAssignment d K q x hterminal = b}

/--
@isnad1 id=iff.1h5v.s6.3a8a2d70e622 from=translated src=- shape=61bba44e vocab=ce5d232f
-/
lemma mem_arcsineAssignedBin_iff (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1)) :
    x ∈ arcsineAssignedBin d K q hterminal b ↔
      arcsineBinAssignment d K q x hterminal = b :=
  Iff.rfl

/-- Membership in a canonical bin gives the exact lower-scale and
factor-q upper-scale bounds used by the local energy estimate.
@isnad1 id=and.3h5v.s7.f6aa0ce038a0 from=translated src=- shape=89e96333 vocab=b0bf07cb
-/
theorem mem_arcsineAssignedBin_scale_bounds
    (d K : ℕ) {q x : ℝ} (hq : 1 ≤ q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1))
    (hx : x ∈ arcsineAssignedBin d K q hterminal b) :
    geometricBinLowerScale d q b.2 ≤ clippedArcsineScale d x ∧
      clippedArcsineScale d x ≤ q * geometricBinLowerScale d q b.2 := by
  have hindex :
      geometricScaleBinIndex d K q x hterminal = b.2 :=
    congrArg Prod.snd hx
  constructor
  · rw [← hindex]
    exact geometricBinLowerScale_le_assignedScale d K q x hterminal
  · rw [← hindex]
    exact assignedScale_le_mul_geometricBinLowerScale d K hq hterminal

/--
@isnad1 id=eq.2h5v.s6.3c9acade0f5d from=translated src=- shape=5fbb971b vocab=4c4a6ad0
-/
lemma mem_arcsineAssignedBin_side
    (d K : ℕ) {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1))
    (hx : x ∈ arcsineAssignedBin d K q hterminal b) :
    decide (0 ≤ x) = b.1 :=
  congrArg Prod.fst hx

/-- Every point has exactly one canonical full-interval bin label.
@isnad1 id=existsun.1h4v.s6.6360b7e5723c from=translated src=- shape=39b21c11 vocab=a524b86c
-/
theorem existsUnique_mem_arcsineAssignedBin (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    ∃! b : Bool × Fin (K + 1),
      x ∈ arcsineAssignedBin d K q hterminal b := by
  refine ⟨arcsineBinAssignment d K q x hterminal, rfl, ?_⟩
  intro b hb
  exact hb.symm

/-- Distinct canonical bins are disjoint.
@isnad1 id=disjoint.2h5v.s7.d93d86fb5cbb from=translated src=- shape=de84ae74 vocab=34d6e087
-/
lemma arcsineAssignedBin_disjoint {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    {b c : Bool × Fin (K + 1)} (hbc : b ≠ c) :
    Disjoint (arcsineAssignedBin d K q hterminal b)
      (arcsineAssignedBin d K q hterminal c) := by
  rw [Set.disjoint_left]
  intro x hxb hxc
  exact hbc (hxb.symm.trans hxc)

/-- The canonical bins cover the real line, hence in particular
the interpolation interval.
@isnad1 id=eq.1h3v.s6.755df61ac647 from=translated src=- shape=cf7091d2 vocab=9a584190
-/
lemma iUnion_arcsineAssignedBin (d K : ℕ) (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    (⋃ b : Bool × Fin (K + 1),
      arcsineAssignedBin d K q hterminal b) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨arcsineBinAssignment d K q x hterminal, rfl⟩

/-- Fiber of a finite assignment.-/
def assignmentFiber {n : ℕ} {β : Type*} [DecidableEq β]
    (assign : Fin n → β) (b : β) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ assign i = b

/-- Cardinality of one assignment fiber.-/
def assignmentCount {n : ℕ} {β : Type*} [DecidableEq β]
    (assign : Fin n → β) (b : β) : ℕ :=
  (assignmentFiber assign b).card

/-- Assignment-fiber counts sum to the total number of indices.
@isnad1 id=eq.0h3v.s5.db0178244236 from=translated src=- shape=8a86c287 vocab=91c26bb7
-/
theorem sum_assignmentCount {n : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (assign : Fin n → β) :
    ∑ b : β, assignmentCount assign b = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset β)) (f := assign)
    (fun _ _ ↦ Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin,
    assignmentCount, assignmentFiber] using h.symm

/-- Increasing enumeration of the indices in one assignment fiber.-/
noncomputable def assignmentEmbedding {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β) :
    Fin (assignmentCount assign b) ↪o Fin n :=
  (assignmentFiber assign b).orderEmbOfFin rfl

/--
@isnad1 id=eq.0h5v.s6.3220ce61822c from=translated src=- shape=1964a2d6 vocab=22d35a31
-/
lemma assignmentEmbedding_mem_fiber {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β)
    (i : Fin (assignmentCount assign b)) :
    assign (assignmentEmbedding assign b i) = b := by
  have hmem := Finset.orderEmbOfFin_mem
    (assignmentFiber assign b) rfl i
  exact (Finset.mem_filter.mp hmem).2

/--
@isnad1 id=strictmo.0h4v.s6.23e7179bc8be from=translated src=- shape=c3a2e1bf vocab=b970e00a
-/
lemma assignmentEmbedding_strictMono {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β) :
    StrictMono (assignmentEmbedding assign b) :=
  (assignmentEmbedding assign b).strictMono

/-- Canonical bin count for an ordered node family.-/
noncomputable def arcsineNodeBinCount {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) : ℕ :=
  assignmentCount
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b

/--
@isnad1 id=eq.1h5v.s7.41849bc93bb3 from=translated src=- shape=e7219895 vocab=2b964c64
-/
theorem sum_arcsineNodeBinCount {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) :
    ∑ b : Bool × Fin (K + 1),
      arcsineNodeBinCount q hterminal nodes b = n :=
  sum_assignmentCount
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal)

/-- Strict increasing global-index embedding for one canonical node bin.-/
noncomputable def arcsineNodeBinEmbedding {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) :
    Fin (arcsineNodeBinCount q hterminal nodes b) ↪o Fin n :=
  assignmentEmbedding
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b

/--
@isnad1 id=strictmo.1h6v.s7.08f8991a1d1d from=translated src=- shape=f47ff079 vocab=b4f6e8c1
-/
lemma arcsineNodeBinEmbedding_strictMono {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) :
    StrictMono (arcsineNodeBinEmbedding q hterminal nodes b) :=
  (arcsineNodeBinEmbedding q hterminal nodes b).strictMono

end

end ClassicalBound
end Randy1153
