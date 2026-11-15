import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace HalfLine

def slope (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F (R + 1) - F R)

def intercept (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F R - (R : ℂ) * slope F)

/--
@isnad1 id=eq.1h3v.s5.9e88e0a8762f from=translated src=- shape=08eb6347 vocab=9854facc
-/
theorem slope_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : slope F = ν := by
  obtain ⟨R₀, hR⟩ := h
  unfold slope
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hR (R + 1) (by linarith), hR R hRle]
  push_cast
  ring

/--
@isnad1 id=eq.1h3v.s5.f9ddb7e52218 from=translated src=- shape=02b598db vocab=e8d99566
-/
theorem intercept_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : intercept F = μ := by
  have hs : slope F = ν := slope_eq_of_forall_le_eq_add_mul h
  obtain ⟨R₀, hR⟩ := h
  unfold intercept
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hs, hR R hRle]
  ring

theorem eq_and_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν μ' ν' : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ)
    (h' : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν' + μ') : μ = μ' ∧ ν = ν' :=
  ⟨(intercept_eq_of_forall_le_eq_add_mul h).symm.trans (intercept_eq_of_forall_le_eq_add_mul h'),
    (slope_eq_of_forall_le_eq_add_mul h).symm.trans (slope_eq_of_forall_le_eq_add_mul h')⟩

def affineExample (R : ℝ) : ℂ :=
  if R < 5 then 37 else (R : ℂ) * 3 + 7

/--
@isnad1 id=eq.1h1v.s5.14abb9dde397 from=translated src=- shape=8adf043e vocab=9313972a
-/
theorem affineExample_eq (R : ℝ) (hR : 5 ≤ R) : affineExample R = (R : ℂ) * 3 + 7 := by
  simp [affineExample, not_lt.mpr hR]

/--
@isnad1 id=eq.0h0v.s3.8f107e187620 from=translated src=- shape=b0ae1d2b vocab=58208b00
-/
theorem slope_affineExample : slope affineExample = 3 :=
  slope_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

/--
@isnad1 id=eq.0h0v.s3.45be6bd13a51 from=translated src=- shape=b0ae1d2b vocab=f7b2c2c5
-/
theorem intercept_affineExample : intercept affineExample = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

/--
@isnad1 id=eq.0h0v.s4.c8df11cdc42b from=translated src=- shape=1ac31801 vocab=760ac7bf
-/
theorem affineExample_zero : affineExample 0 = 37 := by
  norm_num [affineExample]

end HalfLine

end
