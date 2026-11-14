import Tengoku.Piirrationalitymeasure.Formalization.SavingFloor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform integral bounds for changing a floor value under a bounded perturbation. -/

namespace PiIrrationality

open MeasureTheory Set Filter

noncomputable def floorBand (m d h : ℝ) (j : ℤ) : Set ℝ :=
  Icc (((j : ℝ) - d) / m - h / |m|) (((j : ℝ) - d) / m + h / |m|)

/--
@isnad1 id=mem.2h5v.s6.c1fb12f9c4cd from=translated src=- shape=6d3ddf61 vocab=a4e1c239
-/
theorem mem_floorBand_of_abs_le {m d h u : ℝ} {j : ℤ} (hm : m ≠ 0)
    (hu : |m * u + d - j| ≤ h) : u ∈ floorBand m d h j := by
  have he : m * u + d - j = m * (u - ((j : ℝ) - d) / m) := by field_simp; ring
  rw [he, abs_mul, mul_comm] at hu
  have hbound := (le_div_iff₀ (abs_pos.mpr hm)).mpr hu
  rw [abs_le] at hbound
  constructor <;> linarith [hbound.1, hbound.2]

/--
@isnad1 id=measurab.2h2v.s5.4679fbd7c45f from=translated src=- shape=27df870c vocab=f9bd552f
-/
theorem measurable_floorDisagreement {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun t => floorDisagreement (f t) (g t)) := by
  have hf' : Measurable (fun t => ⌊f t⌋) := by fun_prop
  have hg' : Measurable (fun t => ⌊g t⌋) := by fun_prop
  exact Measurable.ite (measurableSet_eq_fun hf' hg') measurable_const measurable_const

/--
@isnad1 id=integrab.2h2v.s6.ebbf341c3b32 from=translated src=- shape=f23d821f vocab=27bdeaf7
-/
theorem integrableOn_floorDisagreement {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    IntegrableOn (fun t => floorDisagreement (f t) (g t)) (Ioc (0 : ℝ) 1) := by
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  apply hi.mono' (measurable_floorDisagreement hf hg).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (floorDisagreement_nonneg _ _)]
    exact floorDisagreement_le_one _ _

/--
@isnad1 id=integrab.0h4v.s5.2edf935182d5 from=translated src=- shape=cdfd432c vocab=b33271db
-/
theorem integrable_floorBand_indicator (m d h : ℝ) (j : ℤ) :
    Integrable ((floorBand m d h j).indicator (fun _ => (1 : ℝ))) :=
  (integrable_indicator_iff measurableSet_Icc).mpr continuousOn_const.integrableOn_Icc

/--
@isnad1 id=eq.1h4v.s6.956dd65e5c16 from=translated src=- shape=1efb487c vocab=9af0233d
-/
theorem integral_floorBand_indicator (m d h : ℝ) (j : ℤ) (hh : 0 ≤ h) :
    (∫ t : ℝ, (floorBand m d h j).indicator (fun _ => (1 : ℝ)) t) = 2 * h / |m| := by
  unfold floorBand
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Icc]
  rw [max_eq_left (by have := div_nonneg hh (abs_nonneg m); linarith)]
  ring

/--
@isnad1 id=le.3h6v.s7.d85cdd7a1f8b from=translated src=- shape=a6db758b vocab=a5d84ad3
-/
theorem floorDisagreement_le_sum_bands {m d h u : ℝ} {N : ℕ} {e : ℝ}
    (hm : m ≠ 0) (he : |e| ≤ h) (hN : |m * u + d| + h ≤ (N : ℝ)) :
    floorDisagreement (m * u + d) (m * u + d + e) ≤
      ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (floorBand m d h j).indicator (fun _ => (1 : ℝ)) u := by
  classical
  by_cases hfloor : ⌊m * u + d⌋ = ⌊m * u + d + e⌋
  · simp only [floorDisagreement, hfloor, ite_true]
    exact Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => by norm_num) u)
  · obtain ⟨j, hj⟩ := floor_ne_exists_int_near hfloor
      (show |(m * u + d) - (m * u + d + e)| ≤ h by simpa using he)
    have hjbound : |(j : ℝ)| ≤ (N : ℝ) := by
      have h := abs_add_le (m * u + d) (-(m * u + d - j))
      simp only [abs_neg] at h
      have heq : m * u + d + -(m * u + d - j) = (j : ℝ) := by ring
      rw [heq] at h
      linarith
    have hjmem : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      rw [abs_le] at hjbound
      exact_mod_cast hjbound
    have hjband := mem_floorBand_of_abs_le hm hj
    simp only [floorDisagreement, hfloor, ite_false]
    calc
      (1 : ℝ) = (floorBand m d h j).indicator (fun _ => (1 : ℝ)) u :=
        (indicator_of_mem hjband (fun _ => (1 : ℝ))).symm
      _ ≤ _ := Finset.single_le_sum
        (fun i _ => indicator_nonneg (fun _ _ => by norm_num) u) hjmem

/--
@isnad1 id=le.5h5v.s8.a538fc0c9b7f from=translated src=- shape=892ae52d vocab=684c0908
-/
theorem integral_floorDisagreement_le {m d h : ℝ} {N : ℕ} {e : ℝ → ℝ}
    (hm : m ≠ 0) (hh : 0 ≤ h) (hmeas : Measurable e)
    (he : ∀ u ∈ Icc (0 : ℝ) 1, |e u| ≤ h)
    (hN : ∀ u ∈ Icc (0 : ℝ) 1, |m * u + d| + h ≤ (N : ℝ)) :
    (∫ u in (0 : ℝ)..1, floorDisagreement (m * u + d) (m * u + d + e u)) ≤
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) * (2 * h / |m|) := by
  classical
  let J := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let B (u : ℝ) := ∑ j ∈ J, (floorBand m d h j).indicator (fun _ => (1 : ℝ)) u
  have hB : Integrable B volume :=
    integrable_finsetSum J (fun j _ => integrable_floorBand_indicator m d h j)
  have hBnonneg : ∀ u, 0 ≤ B u := fun u =>
    Finset.sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => by norm_num) u)
  have hF : IntegrableOn (fun u => floorDisagreement (m * u + d) (m * u + d + e u))
      (Ioc (0 : ℝ) 1) := integrableOn_floorDisagreement (by fun_prop) (by fun_prop)
  calc
    _ = ∫ u in Ioc (0 : ℝ) 1, floorDisagreement (m * u + d) (m * u + d + e u) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ ≤ ∫ u in Ioc (0 : ℝ) 1, B u := by
      apply setIntegral_mono_on hF hB.restrict measurableSet_Ioc
      intro u hu
      exact floorDisagreement_le_sum_bands hm (he u ⟨hu.1.le, hu.2⟩) (hN u ⟨hu.1.le, hu.2⟩)
    _ ≤ ∫ u : ℝ, B u := setIntegral_le_integral hB (Eventually.of_forall hBnonneg)
    _ = ∑ j ∈ J, 2 * h / |m| := by
      rw [show B = fun u : ℝ => ∑ j ∈ J,
        (floorBand m d h j).indicator (fun _ => (1 : ℝ)) u from rfl,
        integral_finsetSum J (fun j _ => integrable_floorBand_indicator m d h j)]
      exact Finset.sum_congr rfl (fun j _ => integral_floorBand_indicator m d h j hh)
    _ = _ := by simp [J]

noncomputable def floorBandCount (m : ℝ) : ℕ := ⌈|m| + 8⌉₊

noncomputable def floorChangeConstant (m : ℝ) : ℝ :=
  ((Finset.Icc (-(floorBandCount m : ℤ)) (floorBandCount m : ℤ)).card : ℝ) * 2 / |m|

/--
@isnad1 id=le.0h1v.s3.cf857a054a21 from=translated src=- shape=8a62b088 vocab=cd33bdb7
-/
theorem floorChangeConstant_nonneg (m : ℝ) : 0 ≤ floorChangeConstant m := by
  unfold floorChangeConstant
  positivity

/--
@isnad1 id=le.6h4v.s7.a8f1b3bff26e from=translated src=- shape=84d7c8ae vocab=58b4e96e
-/
theorem integral_floorDisagreement_uniform {m d h : ℝ} {e : ℝ → ℝ}
    (hm : m ≠ 0) (hd : |d| ≤ 4) (hh0 : 0 ≤ h) (hh4 : h ≤ 4)
    (hmeas : Measurable e) (he : ∀ u ∈ Icc (0 : ℝ) 1, |e u| ≤ h) :
    (∫ u in (0 : ℝ)..1, floorDisagreement (m * u + d) (m * u + d + e u)) ≤
      floorChangeConstant m * h := by
  have hN : ∀ u ∈ Icc (0 : ℝ) 1,
      |m * u + d| + h ≤ (floorBandCount m : ℝ) := by
    intro u hu
    have huabs : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hprod := mul_le_mul_of_nonneg_left huabs (abs_nonneg m)
    have habs := abs_add_le (m * u) d
    rw [abs_mul] at habs
    have hceil : |m| + 8 ≤ (floorBandCount m : ℝ) := Nat.le_ceil _
    linarith
  have h := integral_floorDisagreement_le hm hh0 hmeas he hN
  convert h using 1
  unfold floorChangeConstant
  ring

end PiIrrationality
