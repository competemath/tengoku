import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardPrelim

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sard's theorem, Step 3: the Taylor estimate and deeply critical points

Following Milnor §3, Step 3.  We prove:

* `Submission.norm_sub_le_of_vanishing_derivs` — if all derivatives of `f` of
  orders `1, …, k` vanish at `x` and `‖D^{k+1} f‖ ≤ M` on a convex set `s ∋ x`,
  then `‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k+1)` for `y ∈ s`;
* `Submission.step3` — the image `f (C_k)` of the set of "deeply critical"
  points is null, provided `p < (k+1) * q`.

The cube-counting argument works in `Fin p → ℝ` with the sup norm, where closed
balls are exactly cubes and subdivide evenly.
-/

namespace Submission

noncomputable section

open Function MeasureTheory Metric Set Filter
open scoped ContDiff Topology NNReal

/-! ## Vanishing iterated derivatives transfer to the derivative function -/

theorem fderiv_eq_zero_of_iteratedFDeriv_one_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : iteratedFDeriv ℝ 1 f x = 0) : fderiv ℝ f x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 : fderiv ℝ f x v = iteratedFDeriv ℝ 1 f x (fun _ => v) := by
    rw [iteratedFDeriv_one_apply]
  rw [h2, h]
  simp

theorem iteratedFDeriv_fderiv_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} {j : ℕ}
    (h : iteratedFDeriv ℝ (j + 1) f x = 0) :
    iteratedFDeriv ℝ j (fderiv ℝ f) x = 0 := by
  refine ContinuousMultilinearMap.ext fun m => ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := f) (x := x)
    (Fin.snoc m v)
  rw [h] at h2
  simp only [Fin.init_snoc, Fin.snoc_last, zero_apply] at h2
  exact h2.symm.trans rfl

/-! ## The Taylor-type estimate -/

/-- **Taylor estimate with vanishing derivatives.**  If `f` is `C^∞` on an open
set `U`, `s ⊆ U` is convex, all iterated derivatives of orders `1, …, k` of `f`
vanish at `x ∈ s`, and `‖D^{k+1} f‖ ≤ M` on `s`, then
`‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k+1)` for all `y ∈ s`.-/
theorem norm_sub_le_of_vanishing_derivs
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {U : Set E}, IsOpen U → ∀ {f : E → F}, ContDiffOn ℝ ∞ f U →
      ∀ {s : Set E}, Convex ℝ s → s ⊆ U → ∀ {M : ℝ},
      (∀ z ∈ s, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ M) →
      ∀ {x : E}, x ∈ s → (∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0) →
      ∀ {y : E}, y ∈ s → ‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k + 1) := by
  induction k with
  | zero =>
    intro F _ _ U hU f hf s hs hsU M hM x hx _ y hy
    have hdiff : ∀ z ∈ s, DifferentiableAt ℝ f z := fun z hz =>
      (hf.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt infty_ne_zero
    have hbound : ∀ z ∈ s, ‖fderiv ℝ f z‖ ≤ M := by
      intro z hz
      have h1 := hM z hz
      rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h1
    have h2 := hs.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
    simpa using h2
  | succ k IH =>
    intro F _ _ U hU f hf s hs hsU M hM x hx hvan y hy
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x hx)
    -- apply the inductive hypothesis to `fderiv ℝ f`
    have hg : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
      hf.fderiv_of_isOpen hU (by exact_mod_cast le_top)
    have hM' : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k + 1) (fderiv ℝ f) z‖ ≤ M := by
      intro z hz
      rw [norm_iteratedFDeriv_fderiv]
      exact hM z hz
    have hvan' : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j (fderiv ℝ f) x = 0 :=
      fun j h1 h2 => iteratedFDeriv_fderiv_eq_zero
        (hvan (j + 1) (by omega) (by omega))
    have hgx : fderiv ℝ f x = 0 :=
      fderiv_eq_zero_of_iteratedFDeriv_one_eq_zero (hvan 1 le_rfl (by omega))
    have hIH : ∀ z ∈ s, ‖fderiv ℝ f z‖ ≤ M * ‖z - x‖ ^ (k + 1) := by
      intro z hz
      have h1 := IH hU hg hs hsU hM' hx hvan' hz
      rwa [hgx, sub_zero] at h1
    -- mean value inequality on the segment `[x, y]`
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    have hzx_le : ∀ z ∈ segment ℝ x y, ‖z - x‖ ≤ ‖y - x‖ := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩
      have hb1 : b ≤ 1 := by linarith
      have ha1 : a = 1 - b := by linarith
      have hz' : a • x + b • y - x = b • (y - x) := by
        rw [ha1, sub_smul, one_smul, smul_sub]
        abel
      rw [hz', norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg _) hb1
    have hbound : ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ f z‖ ≤ M * ‖y - x‖ ^ (k + 1) := by
      intro z hz
      refine (hIH z (hseg hz)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hzx_le z hz) (k + 1)) hM0
    have hdiff : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z := fun z hz =>
      (hf.contDiffAt (hU.mem_nhds (hsU (hseg hz)))).differentiableAt
        infty_ne_zero
    have h2 := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le hdiff
      hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    calc ‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k + 1) * ‖y - x‖ := h2
      _ = M * ‖y - x‖ ^ (k + 2) := by rw [mul_assoc, ← pow_succ]

/-! ## The subdivision grid -/

/-- One-dimensional grid: any `u ∈ [0, 2ρ]` is within `ρ/m` of one of the `m`
points `(2j+1)ρ/m`, `j = 0, …, m-1`.-/
theorem exists_grid_index {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ} (hm : 0 < m) {u : ℝ}
    (h0 : 0 ≤ u) (h2 : u ≤ 2 * ρ) :
    ∃ j : ℕ, j < m ∧ |u - (2 * j + 1) * ρ / m| ≤ ρ / m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set t : ℝ := u * m / (2 * ρ) with htdef
  have ht0 : 0 ≤ t := by positivity
  have htm : t ≤ m := by
    rw [htdef, div_le_iff₀ (by positivity)]
    calc u * m ≤ (2 * ρ) * m := by gcongr
      _ = (m : ℝ) * (2 * ρ) := by ring
  set j : ℕ := min ⌊t⌋₊ (m - 1) with hjdef
  have hjm : j < m := by
    have h1 : j ≤ m - 1 := min_le_right _ _
    omega
  have hjt : (j : ℝ) ≤ t := by
    rcases le_or_gt ⌊t⌋₊ (m - 1) with h | h
    · have : j = ⌊t⌋₊ := by rw [hjdef, min_eq_left h]
      rw [this]
      exact Nat.floor_le ht0
    · have hj' : j = m - 1 := by rw [hjdef, min_eq_right (le_of_lt h)]
      have h2' : (m : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_of_lt_succ (by omega)
      have h3 : (⌊t⌋₊ : ℝ) ≤ t + 1 := by
        have := Nat.lt_floor_add_one t
        linarith [Nat.floor_le ht0]
      rw [hj']
      have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have : (1 : ℕ) ≤ m := hm
        push_cast [Nat.cast_sub this]
        ring
      rw [this]
      have h4 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      linarith
  have htj1 : t ≤ j + 1 := by
    rcases le_or_gt ⌊t⌋₊ (m - 1) with h | h
    · have hj' : j = ⌊t⌋₊ := by rw [hjdef, min_eq_left h]
      rw [hj']
      exact le_of_lt (Nat.lt_floor_add_one t)
    · have hj' : j = m - 1 := by rw [hjdef, min_eq_right (le_of_lt h)]
      have : (j : ℝ) + 1 = m := by
        rw [hj']
        have h1 : (1 : ℕ) ≤ m := hm
        push_cast [Nat.cast_sub h1]
        ring
      rw [this]
      exact htm
  refine ⟨j, hjm, ?_⟩
  have hu : u = t * (2 * ρ) / m := by
    rw [htdef]
    field_simp
  have hexpr : u - (2 * j + 1) * ρ / m = (2 * ρ / m) * (t - j - 1 / 2) := by
    rw [hu]
    field_simp
    ring
  rw [hexpr, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * ρ / m)]
  have habs : |t - j - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> [linarith; linarith]
  calc 2 * ρ / m * |t - j - 1 / 2| ≤ 2 * ρ / m * (1 / 2) := by gcongr
    _ = ρ / m := by ring

variable {p q : ℕ}

/-- Center of the subcube indexed by `v` in the subdivision of the cube
`closedBall x₀ ρ` into `m^p` subcubes.-/
def gridCenter (x₀ : Fin p → ℝ) (ρ : ℝ) (m : ℕ) (v : Fin p → Fin m) :
    Fin p → ℝ :=
  fun i => x₀ i - ρ + (2 * (v i : ℕ) + 1) * ρ / m

/-- The subcubes cover the cube.-/
theorem closedBall_subset_iUnion_grid {x₀ : Fin p → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {m : ℕ} (hm : 0 < m) :
    closedBall x₀ ρ ⊆
      ⋃ v : Fin p → Fin m, closedBall (gridCenter x₀ ρ m v) (ρ / m) := by
  intro y hy
  have hy' : ∀ i, |y i - x₀ i| ≤ ρ := by
    intro i
    have h1 : dist (y i) (x₀ i) ≤ ρ :=
      (dist_pi_le_iff hρ.le).1 (mem_closedBall.1 hy) i
    rwa [Real.dist_eq] at h1
  have hchoice : ∀ i : Fin p, ∃ j : ℕ, j < m ∧
      |y i - x₀ i + ρ - (2 * j + 1) * ρ / m| ≤ ρ / m := by
    intro i
    have h0 : 0 ≤ y i - x₀ i + ρ := by have := (abs_le.1 (hy' i)).1; linarith
    have h2 : y i - x₀ i + ρ ≤ 2 * ρ := by
      have := (abs_le.1 (hy' i)).2; linarith
    exact exists_grid_index hρ hm h0 h2
  choose jf hjf1 hjf2 using hchoice
  refine mem_iUnion.2 ⟨fun i => ⟨jf i, hjf1 i⟩, ?_⟩
  rw [mem_closedBall]
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  rw [Real.dist_eq, gridCenter]
  have h3 := hjf2 i
  have h4 : y i - (x₀ i - ρ + (2 * ↑(jf i) + 1) * ρ / ↑m)
      = y i - x₀ i + ρ - (2 * ↑(jf i) + 1) * ρ / ↑m := by ring
  rw [h4]
  exact h3

/-- Each subcube is contained in the big cube.-/
theorem grid_subset_closedBall {x₀ : Fin p → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ}
    (hm : 0 < m) (v : Fin p → Fin m) :
    closedBall (gridCenter x₀ ρ m v) (ρ / m) ⊆ closedBall x₀ ρ := by
  intro z hz
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hz' : ∀ i, |z i - gridCenter x₀ ρ m v i| ≤ ρ / m := by
    intro i
    have h1 : dist (z i) (gridCenter x₀ ρ m v i) ≤ ρ / m :=
      (dist_pi_le_iff (by positivity)).1 (mem_closedBall.1 hz) i
    rwa [Real.dist_eq] at h1
  rw [mem_closedBall]
  refine (dist_pi_le_iff hρ.le).2 fun i => ?_
  rw [Real.dist_eq]
  have hcb : |gridCenter x₀ ρ m v i - x₀ i| ≤ ρ - ρ / m := by
    rw [gridCenter]
    have hw0 : (0 : ℝ) ≤ ρ / m := by positivity
    have hmw : (m : ℝ) * (ρ / m) = ρ := by field_simp
    have hv0 : (0 : ℝ) ≤ ((v i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hv1 : ((v i : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast (v i).2
    have hexpr : x₀ i - ρ + (2 * ↑(v i : ℕ) + 1) * ρ / ↑m - x₀ i
        = 2 * (((v i : ℕ) : ℝ) * (ρ / m)) + ρ / m - ρ := by ring
    have hvw0 : (0 : ℝ) ≤ ((v i : ℕ) : ℝ) * (ρ / m) := mul_nonneg hv0 hw0
    have hvw1 : ((v i : ℕ) : ℝ) * (ρ / m) + ρ / m ≤ ρ := by
      have h9 : (((v i : ℕ) : ℝ) + 1) * (ρ / m) ≤ (m : ℝ) * (ρ / m) :=
        mul_le_mul_of_nonneg_right hv1 hw0
      rw [hmw] at h9
      nlinarith
    rw [hexpr, abs_le]
    constructor
    · linarith
    · linarith
  calc |z i - x₀ i| ≤ |z i - gridCenter x₀ ρ m v i|
        + |gridCenter x₀ ρ m v i - x₀ i| := abs_sub_le _ _ _
    _ ≤ ρ / m + (ρ - ρ / m) := add_le_add (hz' i) hcb
    _ = ρ := by ring

/-! ## Step 3: deeply critical points -/

/-- Milnor's Step 3, local version: on a closed cube inside `U`, the image of
the set of points where all derivatives up to order `k` vanish is null,
provided `p + 1 ≤ (k+1) q`.-/
theorem step3_ball {U : Set (Fin p → ℝ)} (hU : IsOpen U)
    {f : (Fin p → ℝ) → Fin q → ℝ} (hf : ContDiffOn ℝ ∞ f U) {k : ℕ}
    (hk : p + 1 ≤ (k + 1) * q) {x₀ : Fin p → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall x₀ ρ ⊆ U) :
    volume (f '' (vanishSet U f k ∩ closedBall x₀ ρ)) = 0 := by
  -- a uniform bound for the `(k+1)`-st derivative on the cube
  have hcw : ContinuousOn (iteratedFDerivWithin ℝ (k + 1) f U) U :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
      hU.uniqueDiffOn
  have hc : ContinuousOn (iteratedFDeriv ℝ (k + 1) f) U :=
    hcw.congr ((iteratedFDerivWithin_of_isOpen (k + 1) hU).symm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn
    (hc.mono hball)
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ z ∈ closedBall x₀ ρ, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ M :=
    fun z hz => (hC z hz).trans (le_max_left _ _)
  set Cst : ℝ := (2 * M) ^ q * (2 * ρ) ^ ((k + 1) * q) with hCstdef
  -- the key estimate for the subdivision into `m^p` subcubes
  have key : ∀ m : ℕ, 0 < m →
      volume (f '' (vanishSet U f k ∩ closedBall x₀ ρ))
        ≤ ENNReal.ofReal (Cst / m) := by
    intro m hm
    have hb0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
    have hb1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    set R : ℝ := M * (2 * ρ / m) ^ (k + 1) with hRdef
    have hR0 : 0 ≤ R := by positivity
    -- image of each subcube piece is inside a ball of radius `R`
    have percube : ∀ v : Fin p → Fin m,
        volume (f '' (vanishSet U f k
          ∩ closedBall (gridCenter x₀ ρ m v) (ρ / m)))
          ≤ ENNReal.ofReal ((2 * R) ^ q) := by
      intro v
      rcases eq_empty_or_nonempty
        (vanishSet U f k ∩ closedBall (gridCenter x₀ ρ m v) (ρ / m)) with
        hemp | ⟨xh, hxhK, hxhB⟩
      · rw [hemp, image_empty, measure_empty]
        simp
      have hBU : closedBall (gridCenter x₀ ρ m v) (ρ / m) ⊆ U :=
        (grid_subset_closedBall hρ hm v).trans hball
      have himg : f '' (vanishSet U f k
          ∩ closedBall (gridCenter x₀ ρ m v) (ρ / m))
          ⊆ closedBall (f xh) R := by
        rintro _ ⟨y, ⟨hyK, hyB⟩, rfl⟩
        rw [mem_closedBall, dist_eq_norm]
        have htay := norm_sub_le_of_vanishing_derivs k hU hf
          (convex_closedBall (gridCenter x₀ ρ m v) (ρ / m)) hBU
          (fun z hz => hM z (grid_subset_closedBall hρ hm v hz)) hxhB
          (fun j h1 h2 => hxhK.2 j h1 h2) hyB
        refine htay.trans ?_
        rw [hRdef]
        refine mul_le_mul_of_nonneg_left ?_ hM0
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ (k + 1)
        have hd : dist y xh ≤ 2 * ρ / m := by
          calc dist y xh ≤ dist y (gridCenter x₀ ρ m v)
              + dist (gridCenter x₀ ρ m v) xh :=
                dist_triangle _ _ _
            _ ≤ ρ / m + ρ / m := add_le_add (mem_closedBall.1 hyB)
                (by rw [dist_comm]; exact mem_closedBall.1 hxhB)
            _ = 2 * ρ / m := by ring
        rwa [← dist_eq_norm]
      refine (measure_mono himg).trans ?_
      rw [Real.volume_pi_closedBall (f xh) hR0]
      simp
    -- sum over the `m^p` subcubes
    have hcover : f '' (vanishSet U f k ∩ closedBall x₀ ρ)
        ⊆ ⋃ v : Fin p → Fin m, f '' (vanishSet U f k
          ∩ closedBall (gridCenter x₀ ρ m v) (ρ / m)) := by
      rintro _ ⟨y, ⟨hyK, hyB⟩, rfl⟩
      obtain ⟨v, hv⟩ := mem_iUnion.1 (closedBall_subset_iUnion_grid hρ hm hyB)
      exact mem_iUnion.2 ⟨v, ⟨y, ⟨hyK, hv⟩, rfl⟩⟩
    have hcount : volume (f '' (vanishSet U f k ∩ closedBall x₀ ρ))
        ≤ (m ^ p : ℕ) * ENNReal.ofReal ((2 * R) ^ q) := by
      refine (measure_mono hcover).trans ?_
      refine (measure_iUnion_le _).trans ?_
      calc ∑' v : Fin p → Fin m, volume (f '' (vanishSet U f k
            ∩ closedBall (gridCenter x₀ ρ m v) (ρ / m)))
          ≤ ∑' _ : Fin p → Fin m, ENNReal.ofReal ((2 * R) ^ q) :=
            ENNReal.tsum_le_tsum percube
        _ = (Fintype.card (Fin p → Fin m) : ENNReal)
            * ENNReal.ofReal ((2 * R) ^ q) := by
            rw [tsum_fintype]
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = (m ^ p : ℕ) * ENNReal.ofReal ((2 * R) ^ q) := by
            have hcard : Fintype.card (Fin p → Fin m) = m ^ p := by
              simp
            rw [hcard]
    refine hcount.trans ?_
    -- arithmetic: `m^p (2R)^q ≤ Cst / m`
    have hcast : ((m ^ p : ℕ) : ENNReal) = ENNReal.ofReal ((m : ℝ) ^ p) := by
      rw [← ENNReal.ofReal_natCast]
      congr 1
      push_cast
      ring
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcalc : (m : ℝ) ^ p * (2 * R) ^ q
        = Cst * ((m : ℝ) ^ p / (m : ℝ) ^ ((k + 1) * q)) := by
      have h1 : 2 * R = (2 * M) * ((2 * ρ) ^ (k + 1) / (m : ℝ) ^ (k + 1)) := by
        rw [hRdef, div_pow]
        ring
      rw [h1, mul_pow, div_pow, ← pow_mul, ← pow_mul, hCstdef]
      ring
    have hfrac : (m : ℝ) ^ p / (m : ℝ) ^ ((k + 1) * q) ≤ 1 / m := by
      rw [div_le_div_iff₀ (by positivity) hb0]
      calc (m : ℝ) ^ p * m = (m : ℝ) ^ (p + 1) := (pow_succ _ _).symm
        _ ≤ (m : ℝ) ^ ((k + 1) * q) := pow_le_pow_right₀ hb1 hk
        _ = 1 * (m : ℝ) ^ ((k + 1) * q) := (one_mul _).symm
    have hCst0 : 0 ≤ Cst := by positivity
    calc (m : ℝ) ^ p * (2 * R) ^ q
        = Cst * ((m : ℝ) ^ p / (m : ℝ) ^ ((k + 1) * q)) := hcalc
      _ ≤ Cst * (1 / m) := mul_le_mul_of_nonneg_left hfrac hCst0
      _ = Cst / m := by ring
  -- let `m → ∞`
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (Cst / m)) atTop (𝓝 0) := by
    have h1 := ENNReal.tendsto_ofReal
      (tendsto_const_div_atTop_nhds_zero_nat Cst)
    rwa [ENNReal.ofReal_zero] at h1
  have h0 : volume (f '' (vanishSet U f k ∩ closedBall x₀ ρ)) ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact key m hm
  exact le_zero_iff.1 h0

/-- **Milnor's Step 3.**  The image of the set of deeply critical points
(`C_k` with `p + 1 ≤ (k+1) q`) is null.-/
theorem step3 {U : Set (Fin p → ℝ)} (hU : IsOpen U)
    {f : (Fin p → ℝ) → Fin q → ℝ} (hf : ContDiffOn ℝ ∞ f U) {k : ℕ}
    (hk : p + 1 ≤ (k + 1) * q) :
    volume (f '' vanishSet U f k) = 0 := by
  apply image_null_of_locally_image_null
  intro x hx
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, closedBall x ρ ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx.1)
  exact ⟨closedBall x ρ, Metric.closedBall_mem_nhds x hρ,
    step3_ball hU hf hk hρ hball⟩

end

end Submission
