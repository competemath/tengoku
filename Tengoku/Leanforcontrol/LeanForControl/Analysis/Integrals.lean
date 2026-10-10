import Tengoku

open MeasureTheory intervalIntegral Set Topology

open MeasureTheory intervalIntegral Real Set Filter

lemma ContinuousOn.integral_sub_adjacent_intervals {a t : ℝ} {μ : ℝ → ℝ} {s : ℝ}
    (hμ_t : ContinuousOn μ (Icc a t))
    (hs : s ∈ Icc a t) :
    (∫ τ in a..t, μ τ) - ∫ τ in a..s, μ τ = ∫ τ in s..t, μ τ := by
  linarith [intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hμ_t.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
    ((hμ_t.mono (Icc_subset_Icc_left hs.1)).intervalIntegrable_of_Icc hs.2)]

lemma intervalIntegral.norm_integral_le_of_norm_le_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {v : ℝ → ℝ} {a b L : ℝ}
    (hab : a ≤ b)
    (hu_norm_int : IntervalIntegrable (fun s => ‖u s‖) volume a b)
    (hv_int : IntervalIntegrable v volume a b)
    (h_bound : ∀ s ∈ Icc a b, ‖u s‖ ≤ L * v s) :
    ‖∫ s in a..b, u s‖ ≤ L * ∫ s in a..b, v s := by
  calc ‖∫ s in a..b, u s‖
    _ ≤ ∫ s in a..b, ‖u s‖   := norm_integral_le_integral_norm hab
    _ ≤ ∫ s in a..b, L * v s := integral_mono_on hab hu_norm_int (hv_int.const_mul L) h_bound
    _ = L * ∫ s in a..b, v s := integral_const_mul L v

/-- `‖∫ a..b, u‖ ≤ C * (b - a)` from a uniform pointwise bound `‖u s‖ ≤ C` on `Icc a b`.
Hides the `uIoc`-to-`Icc` membership conversion required by Mathlib's
`norm_integral_le_of_norm_le_const`. -/
lemma intervalIntegral.norm_integral_le_const_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {C : ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, ‖u s‖ ≤ C) :
    ‖∫ s in a..b, u s‖ ≤ C * (b - a) := by
  have key : ‖∫ s in a..b, u s‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hab] at hs
    exact h s ⟨hs.1.le, hs.2⟩
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at key

/-- The interval integral of a real constant equals `(b - a) * C`.
Convenience form of `intervalIntegral.integral_const` for `ℝ`, avoiding `•` notation. -/
lemma intervalIntegral.integral_const_eq {a b C : ℝ} :
    ∫ _ in a..b, C = (b - a) * C := by
  rw [intervalIntegral.integral_const, smul_eq_mul]

/-- The composition `s ↦ f(s, z(s))` is interval-integrable on `[t₀, t₁]` when `f` is
    jointly continuous and `z` is continuous on the interval. -/
lemma Continuous.intervalIntegrable_comp {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E → E} {z : ℝ → E}
    (hf_cont : Continuous (fun p : ℝ × E => f p.1 p.2))
    (hz : ContinuousOn z (Icc t₀ t₁)) :
    IntervalIntegrable (fun s => f s (z s)) volume t₀ t₁ := by
  rw [← uIcc_of_le hle] at hz
  exact (hf_cont.comp_continuousOn
    (ContinuousOn.prodMk continuous_id.continuousOn hz)).intervalIntegrable

/-! ## Moving window integrals -/

/-- The scaled half-window average `η ↦ (2/η) * ∫ s in (η/2)..η, f s` is antitone on `(0, ∞)`
    whenever `f` is antitone on `(0, ∞)`. -/
lemma antitoneOn_halfWindow_average {f : ℝ → ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b) :
    AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, f s) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  have hη₁_pos : (0 : ℝ) < η₁ := hη₁
  have hη₂_pos : (0 : ℝ) < η₂ := hη₂
  -- Rewrite: (2/η) * ∫ (η/2)..η, f = 2 * ∫ (1/2)..1, f(η·) via substitution s = η*t
  have hrw : ∀ η : ℝ, 0 < η → (2 / η) * ∫ s in (η / 2)..η, f s =
      2 * ∫ t in (1/2 : ℝ)..(1 : ℝ), f (η * t) := fun η hη => by
    have key : η • ∫ x in (1/2 : ℝ)..(1 : ℝ), f (η * x) =
        ∫ x in η * (1/2 : ℝ)..η * (1 : ℝ), f x := smul_integral_comp_mul_left f η
    simp only [smul_eq_mul, mul_one, show η * (1 / 2 : ℝ) = η / 2 from by ring] at key
    rw [← key, ← mul_assoc, div_mul_cancel₀ 2 hη.ne']
  dsimp only
  rw [hrw η₁ hη₁_pos, hrw η₂ hη₂_pos]
  -- Need: 2 * ∫ (1/2)..1, f(η₂·) ≤ 2 * ∫ (1/2)..1, f(η₁·)
  gcongr
  -- Integrability of f(ηᵢ·) on [1/2, 1]
  have mk_int : ∀ η : ℝ, 0 < η →
      IntervalIntegrable (fun t => f (η * t)) volume (1/2 : ℝ) 1 := fun η hη => by
    have h := (hf_int (η / 2) η (by linarith) hη).comp_mul_left (c := η)
    have heq1 : η / 2 / η = 1 / 2 := by field_simp
    rwa [heq1, div_self hη.ne'] at h
  -- Pointwise: f(η₂·t) ≤ f(η₁·t) for t ∈ [1/2, 1] since η₁·t ≤ η₂·t and f antitone
  refine integral_mono_on (by norm_num) (mk_int η₂ hη₂_pos) (mk_int η₁ hη₁_pos)
    fun t ht => hf_anti (mul_pos hη₁_pos (by linarith [ht.1]))
      (mul_pos hη₂_pos (by linarith [ht.1]))
      (by gcongr; linarith [ht.1])
