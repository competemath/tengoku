import Tengoku.Seed.Analysis.Complex.HasPrimitives
import Tengoku.Seed.Analysis.Complex.LocallyUniformLimit
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic linear initial-value problems on a disk

Existence and uniqueness for homogeneous linear equations with values in a
complex Banach space.  The construction is the Liouville--Neumann (Picard)
series on the whole disk; smaller concentric closed balls are used only for
estimates.
-/

open Filter Function Metric Set
open scoped Topology

namespace LMLF.ODE

private lemma exists_intermediate_radius {q x₀ z : ℂ} {R : ℝ}
    (hR : 0 < R) (hx₀ : x₀ ∈ ball q R) (hz : z ∈ ball q R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ x₀ ∈ ball q r ∧ z ∈ ball q r ∧
      closedBall q r ⊆ ball q R := by
  let m := max (dist x₀ q) (dist z q)
  let r := (m + R) / 2
  have hmx₀ : dist x₀ q ≤ m := le_max_left _ _
  have hmz : dist z q ≤ m := le_max_right _ _
  have hmR : m < R := max_lt (mem_ball.mp hx₀) (mem_ball.mp hz)
  have hm0 : 0 ≤ m := (dist_nonneg : 0 ≤ dist x₀ q).trans hmx₀
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hmr : m < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  exact ⟨r, hr0, hrR, mem_ball.mpr (hmx₀.trans_lt hmr),
    mem_ball.mpr (hmz.trans_lt hmr), closedBall_subset_ball hrR⟩

private lemma exists_operator_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {q : ℂ} {R r : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hr : 0 < r) (hrR : r < R) (hA : AnalyticOnNhd ℂ A (ball q R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedBall q r, ‖A z‖ ≤ M := by
  have hcompact : IsCompact (closedBall q r) := isCompact_closedBall q r
  have hnonempty : (closedBall q r).Nonempty := ⟨q, mem_closedBall_self hr.le⟩
  have hcont : ContinuousOn (fun z ↦ ‖A z‖) (closedBall q r) :=
    (hA.continuousOn.mono (closedBall_subset_ball hrR)).norm
  obtain ⟨w, hw, hwmax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  exact ⟨‖A w‖, norm_nonneg _, fun z hz ↦ hwmax hz⟩

private noncomputable def normalizedPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {f : ℂ → E} (hf : DifferentiableOn ℂ f (ball q R))
    (x₀ : ℂ) : ℂ → E :=
  Classical.choose (hf.isExactOn_ball.with_val_at x₀ 0)

private lemma normalizedPrimitive_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {f : ℂ → E} (hf : DifferentiableOn ℂ f (ball q R))
    (x₀ : ℂ) : normalizedPrimitive hf x₀ x₀ = 0 :=
  (Classical.choose_spec (hf.isExactOn_ball.with_val_at x₀ 0)).1

private lemma normalizedPrimitive_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {f : ℂ → E} (hf : DifferentiableOn ℂ f (ball q R))
    (x₀ : ℂ) {z : ℂ} (hz : z ∈ ball q R) :
    HasDerivAt (normalizedPrimitive hf x₀) (f z) z :=
  (Classical.choose_spec (hf.isExactOn_ball.with_val_at x₀ 0)).2 z hz

private noncomputable def picardState
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) :
    (n : ℕ) → {P : ℂ → E // DifferentiableOn ℂ P (ball q R)}
  | 0 => ⟨fun _ ↦ u₀, differentiableOn_const u₀⟩
  | n + 1 => by
      let P := picardState hA x₀ u₀ n
      have hdiff : DifferentiableOn ℂ (fun z ↦ A z (P.1 z)) (ball q R) :=
        hA.differentiableOn.clm_apply P.2
      exact ⟨normalizedPrimitive hdiff x₀, fun z hz ↦
        normalizedPrimitive_hasDerivAt hdiff x₀ hz |>.differentiableAt.differentiableWithinAt⟩

private noncomputable def picard
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) (n : ℕ) : ℂ → E :=
  (picardState hA x₀ u₀ n).1

private lemma picard_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) :
    picard hA x₀ u₀ 0 = fun _ ↦ u₀ := rfl

private lemma picard_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) (n : ℕ) :
    DifferentiableOn ℂ (picard hA x₀ u₀ n) (ball q R) :=
  (picardState hA x₀ u₀ n).2

private lemma picard_succ_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) (n : ℕ) :
    picard hA x₀ u₀ (n + 1) x₀ = 0 := by
  simp only [picard, picardState]
  exact normalizedPrimitive_value _ _

private lemma picard_succ_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) (x₀ : ℂ) (u₀ : E) (n : ℕ)
    {z : ℂ} (hz : z ∈ ball q R) :
    HasDerivAt (picard hA x₀ u₀ (n + 1))
      (A z (picard hA x₀ u₀ n z)) z := by
  simp only [picard, picardState]
  exact normalizedPrimitive_hasDerivAt _ _ hz

private lemma picard_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R r : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) {x₀ : ℂ} (u₀ : E) (n : ℕ)
    (hsub : closedBall q r ⊆ ball q R) (hx₀ : x₀ ∈ closedBall q r)
    {z : ℂ} (hz : z ∈ closedBall q r) :
    picard hA x₀ u₀ (n + 1) z =
      (z - x₀) • ∫ t : ℝ in 0..1,
        A (x₀ + t • (z - x₀)) (picard hA x₀ u₀ n (x₀ + t • (z - x₀))) := by
  let F : ℂ → E := fun w ↦ A w (picard hA x₀ u₀ n w)
  have hFdiff : DifferentiableOn ℂ F (ball q R) :=
    hA.differentiableOn.clm_apply (picard_differentiableOn hA x₀ u₀ n)
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (z - x₀) ∈ closedBall q r := by
    intro t ht
    simpa [AffineMap.lineMap_apply, add_comm] using
      (convex_closedBall q r).lineMap_mem hx₀ hz ht
  have hcont : ContinuousOn (fun t : ℝ ↦ F (x₀ + t • (z - x₀))) (Icc 0 1) := by
    apply hFdiff.continuousOn.comp (by fun_prop)
    intro t ht
    exact hsub (hline t ht)
  have hftc := intervalIntegral.integral_unitInterval_deriv_eq_sub hcont
    (fun t ht ↦ picard_succ_hasDerivAt hA x₀ u₀ n (hsub (hline t ht)))
  have hzadd : x₀ + (z - x₀) = z := by abel
  rw [hzadd, picard_succ_value hA x₀ u₀ n] at hftc
  simpa [F] using hftc.symm

private lemma picard_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R r M : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) {x₀ : ℂ} (u₀ : E)
    (hsub : closedBall q r ⊆ ball q R) (hx₀ : x₀ ∈ closedBall q r)
    (hM : 0 ≤ M) (hbound : ∀ z ∈ closedBall q r, ‖A z‖ ≤ M) :
    ∀ (n : ℕ) (z : ℂ), z ∈ closedBall q r →
      ‖picard hA x₀ u₀ n z‖ ≤
        ‖u₀‖ * M ^ n * ‖z - x₀‖ ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp [picard_zero]
  | succ n ih =>
      intro z hz
      have hline : ∀ t ∈ Icc (0 : ℝ) 1,
          x₀ + t • (z - x₀) ∈ closedBall q r := by
        intro t ht
        simpa [AffineMap.lineMap_apply, add_comm] using
          (convex_closedBall q r).lineMap_mem hx₀ hz ht
      let C : ℝ := ‖u₀‖ * M ^ (n + 1) * ‖z - x₀‖ ^ n / (n.factorial : ℝ)
      have hC : 0 ≤ C := by positivity
      have hintegrand : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖A (x₀ + t • (z - x₀))
              (picard hA x₀ u₀ n (x₀ + t • (z - x₀)))‖ ≤ C * t ^ n := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have hAt := hbound _ (hline t ht)
        have hPt := ih _ (hline t ht)
        have hdist : ‖x₀ + t • (z - x₀) - x₀‖ = t * ‖z - x₀‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        calc
          ‖A (x₀ + t • (z - x₀))
              (picard hA x₀ u₀ n (x₀ + t • (z - x₀)))‖
              ≤ ‖A (x₀ + t • (z - x₀))‖ *
                  ‖picard hA x₀ u₀ n (x₀ + t • (z - x₀))‖ :=
                ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * (‖u₀‖ * M ^ n *
                ‖x₀ + t • (z - x₀) - x₀‖ ^ n / (n.factorial : ℝ)) := by
              gcongr
          _ = C * t ^ n := by
              rw [hdist]
              dsimp [C]
              rw [mul_pow]
              ring
      have hint :
          ‖∫ t : ℝ in 0..1,
              A (x₀ + t • (z - x₀))
                (picard hA x₀ u₀ n (x₀ + t • (z - x₀)))‖
            ≤ ∫ t : ℝ in 0..1, C * t ^ n := by
        apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        · filter_upwards with t
          intro ht
          exact hintegrand t ⟨le_of_lt ht.1, ht.2⟩
        · exact (by fun_prop : Continuous (fun t : ℝ ↦ C * t ^ n)).intervalIntegrable 0 1
      rw [picard_ray hA u₀ n hsub hx₀ hz, norm_smul]
      calc
        ‖z - x₀‖ *
              ‖∫ t : ℝ in 0..1,
                A (x₀ + t • (z - x₀))
                  (picard hA x₀ u₀ n (x₀ + t • (z - x₀)))‖
            ≤ ‖z - x₀‖ * (∫ t : ℝ in 0..1, C * t ^ n) :=
              mul_le_mul_of_nonneg_left hint (norm_nonneg _)
        _ = ‖u₀‖ * M ^ (n + 1) * ‖z - x₀‖ ^ (n + 1) /
              ((n + 1).factorial : ℝ) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            simp only [one_pow, zero_pow (Nat.succ_ne_zero n), Nat.factorial_succ]
            dsimp [C]
            push_cast
            field_simp
            ring

private lemma picard_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R r M : ℝ} {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) {x₀ : ℂ} (u₀ : E)
    (hsub : closedBall q r ⊆ ball q R) (hx₀ : x₀ ∈ closedBall q r)
    (hM : 0 ≤ M) (hbound : ∀ z ∈ closedBall q r, ‖A z‖ ≤ M)
    (n : ℕ) {w : ℂ} (hw : w ∈ closedBall q r) :
    ‖picard hA x₀ u₀ n w‖ ≤
      ‖u₀‖ * (M * (r + dist q x₀)) ^ n / (n.factorial : ℝ) := by
  have hr0 : 0 ≤ r := by
    have := mem_closedBall.mp hx₀
    exact (dist_nonneg.trans this)
  have hd : ‖w - x₀‖ ≤ r + dist q x₀ := by
    rw [← dist_eq_norm]
    exact (dist_triangle w q x₀).trans
      (add_le_add (mem_closedBall.mp hw) le_rfl)
  calc
    ‖picard hA x₀ u₀ n w‖ ≤
        ‖u₀‖ * M ^ n * ‖w - x₀‖ ^ n / (n.factorial : ℝ) :=
      picard_norm_le hA u₀ hsub hx₀ hM hbound n w hw
    _ ≤ ‖u₀‖ * M ^ n * (r + dist q x₀) ^ n / (n.factorial : ℝ) := by
      gcongr
    _ = ‖u₀‖ * (M * (r + dist q x₀)) ^ n / (n.factorial : ℝ) := by
      rw [mul_pow]
      ring

private lemma picard_majorant_summable (C d : ℝ) :
    Summable (fun n : ℕ ↦ C * (d ^ n / (n.factorial : ℝ))) :=
  (Real.summable_pow_div_factorial d).mul_left C

private lemma solution_unique_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} (hR : 0 < R) {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R)) {x₀ : ℂ} (hx₀ : x₀ ∈ ball q R)
    {u v : ℂ → E} (hu₀ : u x₀ = v x₀)
    (hu : ∀ z ∈ ball q R, HasDerivAt u (A z (u z)) z)
    (hv : ∀ z ∈ ball q R, HasDerivAt v (A z (v z)) z) :
    EqOn u v (ball q R) := by
  intro z hz
  obtain ⟨r, hr0, hrR, hx₀r, hzr, hsub⟩ := exists_intermediate_radius hR hx₀ hz
  obtain ⟨M, hM, hbound⟩ := exists_operator_bound hr0 hrR hA
  let D : ℂ → E := fun w ↦ u w - v w
  let δ : ℂ := z - x₀
  let γ : ℝ → ℂ := fun t ↦ x₀ + t • δ
  let W : ℝ → E := fun t ↦ D (γ t)
  let G : ℝ → E := fun t ↦ δ • A (γ t) (W t)
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall q r := by
    intro t ht
    simpa [γ, δ, AffineMap.lineMap_apply, add_comm] using
      (convex_closedBall q r).lineMap_mem (ball_subset_closedBall hx₀r)
        (ball_subset_closedBall hzr) ht
  have hD : ∀ w ∈ ball q R, HasDerivAt D (A w (D w)) w := by
    intro w hw
    change HasDerivAt (u - v) (A w ((u - v) w)) w
    simpa only [Pi.sub_apply, ContinuousLinearMap.map_sub] using (hu w hw).sub (hv w hw)
  have hW : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt W (G t) t := by
    intro t ht
    have hinner : HasDerivAt γ δ t := by
      have hγeq : γ = (⇑(AffineMap.lineMap x₀ z) : ℝ → ℂ) := by
        funext s
        simp [γ, δ, AffineMap.lineMap_apply, add_comm]
      rw [hγeq]
      have hlineDeriv :
          HasDerivAt (⇑(AffineMap.lineMap x₀ z) : ℝ → ℂ) (z - x₀) t :=
        AffineMap.hasDerivAt_lineMap
      simpa [δ] using hlineDeriv
    change HasDerivAt (D ∘ γ) (G t) t
    simpa [G, W] using (hD (γ t) (hsub (hline t ht))).scomp t hinner
  have hWcont : ContinuousOn W (Icc (0 : ℝ) 1) :=
    fun t ht ↦ (hW t ht).continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (Icc (0 : ℝ) 1) := by
    have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
      exact (by fun_prop : Continuous γ).continuousOn
    have hAcomp : ContinuousOn (fun t ↦ A (γ t)) (Icc (0 : ℝ) 1) :=
      hA.continuousOn.comp hγcont (fun t ht ↦ hsub (hline t ht))
    exact (hAcomp.clm_apply hWcont).const_smul δ
  have hW0 : W 0 = 0 := by
    simp [W, D, γ, hu₀]
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr zero_le_one) hWcont.norm
  let C : ℝ := ‖W tmax‖
  let L : ℝ := ‖δ‖ * M
  have hC : 0 ≤ C := norm_nonneg _
  have hL : 0 ≤ L := mul_nonneg (norm_nonneg _) hM
  have hfactorial : ∀ (n : ℕ) (t : ℝ), t ∈ Icc 0 1 →
      ‖W t‖ ≤ C * (L * t) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro t ht
        simpa [C] using hmax ht
    | succ n ih =>
        intro t ht
        have hsubIcc : Icc (0 : ℝ) t ⊆ Icc 0 1 := fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
        have hGint : IntervalIntegrable G MeasureTheory.volume 0 t := by
          apply ContinuousOn.intervalIntegrable
          simpa [uIcc_of_le ht.1] using hGcont.mono hsubIcc
        have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
          (hWcont.mono hsubIcc)
          (fun s hs ↦ hW s (hsubIcc ⟨hs.1.le, hs.2.le⟩)) hGint
        have hIntegral : W t = ∫ s : ℝ in 0..t, G s := by
          simpa [hW0] using hFTC.symm
        let B : ℝ := C * L ^ (n + 1) / (n.factorial : ℝ)
        have hB : 0 ≤ B := by positivity
        have hGest : ∀ s ∈ Icc (0 : ℝ) t, ‖G s‖ ≤ B * s ^ n := by
          intro s hs
          have hs01 := hsubIcc hs
          have hs0 : 0 ≤ s := hs.1
          have hAs := hbound _ (hline s hs01)
          have hWs := ih s hs01
          calc
            ‖G s‖ ≤ ‖δ‖ * ‖A (γ s) (W s)‖ := by
              simpa [G] using norm_smul_le δ (A (γ s) (W s))
            _ ≤ ‖δ‖ * (‖A (γ s)‖ * ‖W s‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖δ‖ * (M * (C * (L * s) ^ n / (n.factorial : ℝ))) := by
              gcongr
            _ = B * s ^ n := by
              dsimp [B, L]
              rw [mul_pow]
              ring
        have hint : ‖∫ s : ℝ in 0..t, G s‖ ≤ ∫ s : ℝ in 0..t, B * s ^ n := by
          apply intervalIntegral.norm_integral_le_of_norm_le ht.1
          · filter_upwards with s
            intro hs
            exact hGest s ⟨le_of_lt hs.1, hs.2⟩
          · exact (by fun_prop : Continuous (fun s : ℝ ↦ B * s ^ n)).intervalIntegrable 0 t
        rw [hIntegral]
        calc
          ‖∫ s : ℝ in 0..t, G s‖ ≤ ∫ s : ℝ in 0..t, B * s ^ n := hint
          _ = C * (L * t) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ]
            dsimp [B]
            push_cast
            field_simp
            rw [mul_pow]
            ring
  have hW1 : W 1 = D z := by simp [W, γ, δ]
  have hupper : ∀ n : ℕ, ‖W 1‖ ≤ C * (L ^ n / (n.factorial : ℝ)) := by
    intro n
    simpa [mul_one, mul_div_assoc] using hfactorial n 1 ⟨zero_le_one, le_rfl⟩
  have hlim : Tendsto (fun n : ℕ ↦ C * (L ^ n / (n.factorial : ℝ))) atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C)).mul
          (FloorSemiring.tendsto_pow_div_factorial_atTop L))
  have hnormlim : Tendsto (fun _ : ℕ ↦ ‖W 1‖) atTop (nhds 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hupper hlim
  have hnorm : ‖W 1‖ = 0 := tendsto_nhds_unique tendsto_const_nhds hnormlim
  have hDz : D z = 0 := by
    rw [← hW1]
    exact norm_eq_zero.mp hnorm
  simpa [D] using sub_eq_zero.mp hDz

/-- A holomorphic homogeneous linear initial-value problem on a complex disk has a
unique solution on the whole disk.
@isnad1 id=ex.3h6v.s9.6ed35bc82401 from=translated src=- shape=f786d6a6 vocab=5baff900
-/
theorem exists_unique_holomorphicLinearIVP_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {q : ℂ} {R : ℝ} (hR : 0 < R)
    {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A (ball q R))
    {x₀ : ℂ} (hx₀ : x₀ ∈ ball q R) (u₀ : E) :
    ∃ u : ℂ → E, u x₀ = u₀ ∧ AnalyticOnNhd ℂ u (ball q R) ∧
      (∀ z ∈ ball q R, HasDerivAt u (A z (u z)) z) ∧
      ∀ v : ℂ → E, v x₀ = u₀ → AnalyticOnNhd ℂ v (ball q R) →
        (∀ z ∈ ball q R, HasDerivAt v (A z (v z)) z) → EqOn u v (ball q R) := by
  let P : ℕ → ℂ → E := picard hA x₀ u₀
  let u : ℂ → E := fun z ↦ ∑' n : ℕ, P n z
  have hu₀ : u x₀ = u₀ := by
    rw [show u x₀ = ∑' n : ℕ, P n x₀ by rfl, tsum_eq_single 0]
    · simp [P, picard_zero]
    · intro n hn
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact picard_succ_value hA x₀ u₀ n
  have local_data (z : ℂ) (hz : z ∈ ball q R) :
      ∃ r M : ℝ, 0 < r ∧ r < R ∧ x₀ ∈ ball q r ∧ z ∈ ball q r ∧
        closedBall q r ⊆ ball q R ∧ 0 ≤ M ∧
        (∀ w ∈ closedBall q r, ‖A w‖ ≤ M) := by
    obtain ⟨r, hr0, hrR, hx₀r, hzr, hsub⟩ := exists_intermediate_radius hR hx₀ hz
    obtain ⟨M, hM, hbound⟩ := exists_operator_bound hr0 hrR hA
    exact ⟨r, M, hr0, hrR, hx₀r, hzr, hsub, hM, hbound⟩
  have hdiff : DifferentiableOn ℂ u (ball q R) := by
    intro z hz
    obtain ⟨r, M, hr0, hrR, hx₀r, hzr, hsub, hM, hbound⟩ := local_data z hz
    let majorant : ℕ → ℝ := fun n ↦
      ‖u₀‖ * (M * (r + dist q x₀)) ^ n / (n.factorial : ℝ)
    have hmajor : Summable majorant := by
      simpa only [majorant, mul_div_assoc] using
        picard_majorant_summable ‖u₀‖ (M * (r + dist q x₀))
    have hPbound : ∀ (n : ℕ) (w : ℂ), w ∈ ball q r → ‖P n w‖ ≤ majorant n := by
      intro n w hw
      simpa [P, majorant] using
        picard_uniform_bound hA u₀ hsub (ball_subset_closedBall hx₀r)
          hM hbound n (ball_subset_closedBall hw)
    have hs := Complex.differentiableOn_tsum_of_summable_norm hmajor
      (fun n ↦ (picard_differentiableOn hA x₀ u₀ n).mono
        (ball_subset_closedBall.trans hsub)) isOpen_ball hPbound
    exact (hs.differentiableAt (isOpen_ball.mem_nhds hzr)).differentiableWithinAt
  have hode : ∀ z ∈ ball q R, HasDerivAt u (A z (u z)) z := by
    intro z hz
    obtain ⟨r, M, hr0, hrR, hx₀r, hzr, hsub, hM, hbound⟩ := local_data z hz
    let majorant : ℕ → ℝ := fun n ↦
      ‖u₀‖ * (M * (r + dist q x₀)) ^ n / (n.factorial : ℝ)
    have hmajor : Summable majorant := by
      simpa only [majorant, mul_div_assoc] using
        picard_majorant_summable ‖u₀‖ (M * (r + dist q x₀))
    have hPbound : ∀ (n : ℕ) (w : ℂ), w ∈ ball q r → ‖P n w‖ ≤ majorant n := by
      intro n w hw
      simpa [P, majorant] using
        picard_uniform_bound hA u₀ hsub (ball_subset_closedBall hx₀r)
          hM hbound n (ball_subset_closedBall hw)
    have hsumP : HasSum (fun n ↦ P n z) (u z) := by
      exact (Summable.of_norm_bounded hmajor (fun n ↦ hPbound n z hzr)).hasSum
    have hsumDeriv := Complex.hasSum_deriv_of_summable_norm hmajor
      (fun n ↦ (picard_differentiableOn hA x₀ u₀ n).mono
        (ball_subset_closedBall.trans hsub)) isOpen_ball hPbound hzr
    have htail : HasSum (fun n ↦ deriv (P (n + 1)) z) (deriv u z) := by
      have h := (hasSum_nat_add_iff' 1).2 hsumDeriv
      simpa [P, picard_zero] using h
    have htail' : HasSum (fun n ↦ A z (P n z)) (deriv u z) := by
      simpa only [P, (picard_succ_hasDerivAt hA x₀ u₀ _ hz).deriv] using htail
    have hderiv : deriv u z = A z (u z) := htail'.unique ((A z).hasSum hsumP)
    rw [← hderiv]
    exact (hdiff.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  refine ⟨u, hu₀, hdiff.analyticOnNhd isOpen_ball, hode, ?_⟩
  intro v hv₀ hvAnalytic hvOde
  apply solution_unique_on_ball hR hA hx₀
  · exact hu₀.trans hv₀.symm
  · exact hode
  · exact hvOde

end LMLF.ODE
