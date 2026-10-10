import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.GraphObstruction

namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem lipschitz_sub_const {V : Type uV} [NormedAddCommGroup V] (f : M → V)
    {K : ℝ≥0} (hf : LipschitzWith K f) (c : V) :
    LipschitzWith K (fun x => f x - c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hf.dist_le_mul x y

omit [Zero M] in
theorem lipschitz_const_sub {V : Type uV} [NormedAddCommGroup V] (f : M → V)
    {K : ℝ≥0} (hf : LipschitzWith K f) (c : V) :
    LipschitzWith K (fun x => c - f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_left] using hf.dist_le_mul x y

def normalized (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) : FreeSpace.LipZero M :=
  ⟨fun x => f x - f 0, ⟨by simp, C, by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y⟩⟩

def test (f : FreeSpace.LipZero M) : FreeSpace.Space M →L[ℝ] ℝ :=
  ({ toFun := fun μ => FreeSpace.inclusion μ f
     map_add' := by intro μ ν; rfl
     map_smul' := by intro c μ; rfl } : FreeSpace.Space M →ₗ[ℝ] ℝ).mkContinuous
    ‖f‖ (by
      intro μ
      change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
      simpa only [mul_comm] using μ.1.le_opNorm f)

@[simp] theorem test_point (f : FreeSpace.LipZero M) (x : M) :
    test f (FreeSpace.point x) = f.1 x := rfl

def cutoff (z : M) (s : ℝ≥0) (x : M) : ℝ :=
  max 0 (min 1 (2 - (2 / (s : ℝ)) * dist x z))

omit [Zero M] in
theorem cutoff_nonneg (z : M) (s : ℝ≥0) (x : M) : 0 ≤ cutoff z s x := le_max_left _ _
omit [Zero M] in
theorem cutoff_le_one (z : M) (s : ℝ≥0) (x : M) : cutoff z s x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

omit [Zero M] in
theorem cutoff_zero (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : (s : ℝ) ≤ dist x z) :
    cutoff z s x = 0 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : 2 ≤ (2 / (s : ℝ)) * dist x z := by
    calc
      2 = (2 / (s : ℝ)) * s := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [Zero M] in
theorem cutoff_one (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : dist x z ≤ s / 2) :
    cutoff z s x = 1 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : (2 / (s : ℝ)) * dist x z ≤ 1 := by
    calc
      _ ≤ (2 / (s : ℝ)) * ((s : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 1 := by field_simp
  unfold cutoff
  rw [min_eq_left (by linarith)]
  norm_num

omit [Zero M] in
theorem cutoff_lipschitz (z : M) (s : ℝ≥0) : LipschitzWith (2 / s) (cutoff z s) := by
  have h : LipschitzWith (2 / s) (fun x : M => 2 - (2 / (s : ℝ)) * dist x z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc
      |(2 - 2 / (s : ℝ) * dist x z) - (2 - 2 / (s : ℝ) * dist y z)| =
          (2 / (s : ℝ)) * |dist x z - dist y z| := by
            rw [show (2 - 2 / (s : ℝ) * dist x z) - (2 - 2 / (s : ℝ) * dist y z) =
              -(2 / (s : ℝ) * (dist x z - dist y z)) by ring,
              abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / (s : ℝ))]
      _ ≤ (2 / (s : ℝ)) * dist x y := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y z) (by positivity)
      _ = _ := by simp
  exact (h.const_min 1).const_max 0

omit [Zero M] in

theorem product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f ψ : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0)
    (hψ : LipschitzWith (2 / s) ψ) (hb : ∀ x, |ψ x| ≤ 1)
    (hv : ∀ x y, ψ x ≠ ψ y → dist x z < s ∨ dist y z < s) :
    LipschitzWith (3 * C) (fun x => f x * ψ x) := by
  have hs' : 0 < (s : ℝ) := hs
  have hfbound (x : M) (hx : dist x z < s) : |f x| ≤ C * s := by
    have h := hf.dist_le_mul x z
    rw [hfz, dist_zero_right, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hx.le C.coe_nonneg)
  have hsmall (x y : M) (hx : dist x z < s) :
      |f x * ψ x - f y * ψ y| ≤ (3 * (C : ℝ)) * dist x y := by
    have hfxy : |f x - f y| ≤ C * dist x y := hf.dist_le_mul x y
    have hψxy : |ψ x - ψ y| ≤ (2 / (s : ℝ)) * dist x y := hψ.dist_le_mul x y
    calc
      |f x * ψ x - f y * ψ y| = |ψ y * (f x - f y) + f x * (ψ x - ψ y)| := by congr 1; ring
      _ ≤ |ψ y * (f x - f y)| + |f x * (ψ x - ψ y)| := abs_add_le _ _
      _ = |ψ y| * |f x - f y| + |f x| * |ψ x - ψ y| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (C * dist x y) + (C * s) * ((2 / (s : ℝ)) * dist x y) :=
        add_le_add (mul_le_mul (hb y) hfxy (abs_nonneg _) (by norm_num))
          (mul_le_mul (hfbound x hx) hψxy (abs_nonneg _) (by positivity))
      _ = (3 * (C : ℝ)) * dist x y := by field_simp; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat]
  by_cases heq : ψ x = ψ y
  · rw [← heq, ← sub_mul, abs_mul]
    have hxy : |f x - f y| ≤ C * dist x y := hf.dist_le_mul x y
    calc
      _ ≤ (C * dist x y) * 1 := mul_le_mul hxy (hb x) (abs_nonneg _) (by positivity)
      _ ≤ 3 * (C : ℝ) * dist x y := by nlinarith [C.coe_nonneg, dist_nonneg (x := x) (y := y)]
  · rcases hv x y heq with hx | hy
    · exact hsmall x y hx
    · simpa only [abs_sub_comm, dist_comm] using hsmall y x hy

omit [Zero M] in
theorem cutoff_product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0) :
    LipschitzWith (3 * C) (fun x => f x * cutoff z s x) := by
  apply product_lipschitz z hs f _ hf hfz (cutoff_lipschitz z s)
  · intro x
    rw [abs_of_nonneg (cutoff_nonneg z s x)]
    exact cutoff_le_one z s x
  · intro x y h
    by_contra! hc
    exact h ((cutoff_zero z hs hc.1).trans (cutoff_zero z hs hc.2).symm)

def DisjointTests (h : ℕ → M → ℝ) : Prop :=
  ∀ x i j, h i x ≠ 0 → h j x ≠ 0 → i = j

omit [Zero M] [MetricSpace M] in
theorem DisjointTests.exists_index {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∃ i, ∀ j, j ≠ i → h j x = 0 := by
  classical
  by_cases he : ∃ i, h i x ≠ 0
  · obtain ⟨i, hi⟩ := he
    exact ⟨i, fun j hj => by by_contra hh; exact hj (hd x j i hh hi)⟩
  · push Not at he
    exact ⟨0, fun j _ => he j⟩

noncomputable def activeIndex {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) : ℕ :=
  (hd.exists_index x).choose

noncomputable def disjointMap {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    WeakSequences.RealL1 := lp.single 1 (activeIndex hd x) (h (activeIndex hd x) x)

noncomputable def disjointOperator {h : ℕ → M → ℝ} (hd : DisjointTests h) :
    FreeSpace.Space M →L[ℝ] WeakSequences.RealL1 :=
  FreeSpace.linearize (fun x => disjointMap hd x - disjointMap hd 0)

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI
