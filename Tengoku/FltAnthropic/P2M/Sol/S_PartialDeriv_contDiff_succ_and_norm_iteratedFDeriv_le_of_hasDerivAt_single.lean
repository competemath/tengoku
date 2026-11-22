import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single

set_option autoImplicit false

open Filter Topology Asymptotics

noncomputable section

namespace KcPartialDeriv

abbrev ev {n : ℕ} (j : Fin n) : Fin n → ℝ := Pi.single j 1

def trunc {n : ℕ} (h : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun i => if (i : ℕ) < k then h i else 0

/--
@isnad1 id=eq.0h2v.s5.87f34bbf3fd1 from=translated src=- shape=baff65c4 vocab=e16aca3a
-/
theorem trunc_zero {n : ℕ} (h : Fin n → ℝ) : trunc h 0 = 0 := by
  funext i
  simp [trunc]

/--
@isnad1 id=eq.0h2v.s4.8b3fe79a1474 from=translated src=- shape=f2f6f2fc vocab=e16aca3a
-/
theorem trunc_self {n : ℕ} (h : Fin n → ℝ) : trunc h n = h := by
  funext i
  simp [trunc, i.isLt]

/--
@isnad1 id=eq.0h3v.s6.ab7f4bb21d8a from=translated src=- shape=45fc751b vocab=3114406c
-/
theorem trunc_succ {n : ℕ} (h : Fin n → ℝ) (j : Fin n) : trunc h ((j : ℕ) + 1) = trunc h j + h j • ev j := by
  funext i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp
  · have hne : (i : ℕ) ≠ (j : ℕ) := fun h' => hij (Fin.ext h')
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · rw [ite_eq_left (by omega), ite_eq_left hlt, ite_eq_right hij, mul_zero, add_zero]
    · rw [ite_eq_right (by omega), ite_eq_right hlt, ite_eq_right hij, mul_zero, add_zero]

/--
@isnad1 id=le.1h4v.s7.f457fc868769 from=translated src=- shape=b6ea50e4 vocab=3e3f5c94
-/
theorem norm_trunc_add_smul_le {n : ℕ} (h : Fin n → ℝ) (j : Fin n) (s : ℝ) (hs : |s| ≤ |h j|) :
    ‖trunc h j + s • ev j‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg h)]
  intro i
  simp only [trunc, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Real.norm_eq_abs]
  have hi : |h i| ≤ ‖h‖ := by
    have := norm_le_pi_norm h i
    rwa [Real.norm_eq_abs] at this
  have hj : |h j| ≤ ‖h‖ := by
    have := norm_le_pi_norm h j
    rwa [Real.norm_eq_abs] at this
  by_cases hij : i = j
  · subst hij
    simp only [lt_self_iff_false, ite_false, ite_true, zero_add, mul_one]
    exact hs.trans hj
  · rw [ite_eq_right hij, mul_zero, add_zero]
    split_ifs
    · exact hi
    · rw [abs_zero]; exact norm_nonneg h

section Line

variable {n : ℕ} {f : (Fin n → ℝ) → ℂ} {g : Fin n → (Fin n → ℝ) → ℂ}

/--
@isnad1 id=hasderiv.1h6v.s8.0df6fe80e1ea from=translated src=- shape=4d7db0d3 vocab=4e7a2aef
-/
theorem hasDerivAt_line
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (p : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => f (p + s' • ev j)) (g j (p + s • ev j)) s := by
  have h0 : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) 0 := hfg (p + s • ev j) j
  have hfun : (fun s' : ℝ => f (p + s' • ev j)) = fun s' => f (p + s • ev j + (s' - s) • ev j) := by
    funext s'
    congr 1
    rw [add_assoc, ← add_smul, add_sub_cancel]
  rw [hfun]
  have h0' : HasDerivAt (fun τ : ℝ => f (p + s • ev j + τ • ev j)) (g j (p + s • ev j)) (s - s) := by
    rw [sub_self]; exact h0
  exact h0'.comp_sub_const s s

/--
@isnad1 id=le.2h7v.s8.00da13ee3b79 from=translated src=- shape=5e55a6a4 vocab=1ca49e4d
-/
theorem norm_sub_sub_smul_le
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (t h : Fin n → ℝ) (j : Fin n) {C : ℝ}
    (hC : ∀ s ∈ Set.uIcc (0 : ℝ) (h j), ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ C) :
    ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ ≤ C * |h j| := by
  set φ : ℝ → ℂ := fun s => f (t + trunc h j + s • ev j) - s • g j t with hφ
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (h j),
      HasDerivWithinAt φ (g j (t + trunc h j + s • ev j) - g j t) (Set.uIcc (0 : ℝ) (h j)) s := by
    intro s _
    have h1 := hasDerivAt_line hfg (t + trunc h j) j s
    have h2 : HasDerivAt (fun s : ℝ => s • g j t) (g j t) s := by
      simpa using (hasDerivAt_id s).smul_const (g j t)
    exact (h1.sub h2).hasDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hC (convex_uIcc (0 : ℝ) (h j))
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hφeq : φ (h j) - φ 0 = f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t := by
    simp only [hφ, zero_smul, add_zero, sub_zero, trunc_succ, add_assoc]
    abel
  rw [← hφeq]
  simpa [Real.norm_eq_abs] using hmv

/--
@isnad1 id=hasfderi.2h4v.s9.5e7d806a8bd2 from=translated src=- shape=d4947569 vocab=9db76e2a
-/
theorem hasFDerivAt_of_partials (hgc : ∀ j, Continuous (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0)
    (t : Fin n → ℝ) :
    HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc

  have hG : Continuous (fun p : Fin n → ℝ => fun j : Fin n => g j p) := continuous_pi fun j => hgc j
  have hc' : 0 < c / ((n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hG t (c / ((n : ℝ) + 1)) hc'
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh

  have hnear : ∀ (j : Fin n) (s : ℝ), s ∈ Set.uIcc (0 : ℝ) (h j) →
      ‖g j (t + trunc h j + s • ev j) - g j t‖ ≤ c / ((n : ℝ) + 1) := by
    intro j s hs
    have hs' : |s| ≤ |h j| := by simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hd : dist (t + trunc h j + s • ev j) t < δ := by
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      exact (norm_trunc_add_smul_le h j s hs').trans_lt hh
    have hlt := hδ' _ hd
    rw [dist_eq_norm] at hlt
    have hcomp := norm_le_pi_norm ((fun j' : Fin n => g j' (t + trunc h j + s • ev j)) - fun j' => g j' t) j
    simp only [Pi.sub_apply] at hcomp
    exact hcomp.trans hlt.le

  have htel : f (t + h) - f t = ∑ j : Fin n, (f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j)) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => f (t + trunc h (k + 1)) - f (t + trunc h k)) n,
      Finset.sum_range_sub (fun k => f (t + trunc h k)) n, trunc_self, trunc_zero, add_zero]
  have hL : (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) h =
      ∑ j, h j • g j t := by
    simp [ContinuousLinearMap.smulRight_apply]
  rw [hL, htel, ← Finset.sum_sub_distrib]
  have hn : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc ‖∑ j : Fin n, (f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t)‖
      ≤ ∑ j : Fin n, ‖f (t + trunc h ((j : ℕ) + 1)) - f (t + trunc h j) - h j • g j t‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * |h j| :=
        Finset.sum_le_sum fun j _ => norm_sub_sub_smul_le hfg t h j (hnear j)
    _ ≤ ∑ j : Fin n, c / ((n : ℝ) + 1) * ‖h‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : |h j| ≤ ‖h‖ := by
          have := norm_le_pi_norm h j
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_left hj hc'.le
    _ = c * ((n : ℝ) / ((n : ℝ) + 1)) * ‖h‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ c * 1 * ‖h‖ := by gcongr
    _ = c * ‖h‖ := by ring

end Line

section ClassOfDerivative

variable {n : ℕ}

def A (j : Fin n) : ℂ →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

/--
@isnad1 id=eq.0h3v.s10.45c71739cc6c from=translated src=- shape=b7d4dba0 vocab=8af637ed
-/
theorem A_apply (j : Fin n) (c : ℂ) :
    A j c = (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight c :=
  rfl

/--
@isnad1 id=le.0h2v.s9.dde9a894fe86 from=translated src=- shape=45794a70 vocab=b6d3976c
-/
theorem norm_A_le (j : Fin n) : ‖A j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c => ?_
  rw [one_mul, A_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c) fun v => ?_
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg c)

variable {g : Fin n → (Fin n → ℝ) → ℂ}

/--
@isnad1 id=eq.0h3v.s10.badb1fdd995a from=translated src=- shape=fb14285c vocab=e479817f
-/
theorem sum_smulRight_eq (t : Fin n → ℝ) :
    (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) = ∑ j, A j (g j t) :=
  rfl

/--
@isnad1 id=contdiff.1h3v.s9.3ba1e7f1d30d from=translated src=- shape=04b9055c vocab=2e0fb738
-/
theorem contDiff_sum_A {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) :
    ContDiff ℝ m (fun t => ∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) := by
  simp only [sum_smulRight_eq]
  exact ContDiff.sum fun j _ => (A j).contDiff.comp (hg j)

/--
@isnad1 id=le.2h5v.s11.a65ed3f7f42f from=translated src=- shape=1d26b4ab vocab=77b29f88
-/
theorem norm_iteratedFDeriv_sum_A_le {m : ℕ} (hg : ∀ j, ContDiff ℝ m (g j)) {k : ℕ} (hk : k ≤ m)
    (t : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  have hk' : (k : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hk
  have hsum : iteratedFDeriv ℝ k (fun t => ∑ j, A j (g j t)) t = ∑ j, iteratedFDeriv ℝ k (fun t => A j (g j t)) t := by
    have := iteratedFDeriv_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin n))) (i := k)
      (f := fun j t => A j (g j t)) (fun j _ => ((A j).contDiff.comp (hg j)).of_le hk')
    rw [this]
    exact Finset.sum_apply (M := fun _ : Fin n → ℝ =>
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ((Fin n → ℝ) →L[ℝ] ℂ)) t Finset.univ
      (fun j => iteratedFDeriv ℝ k (fun t => A j (g j t)))
  rw [hsum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hcomp : iteratedFDeriv ℝ k (fun t => A j (g j t)) t =
      (A j).compContinuousMultilinearMap (iteratedFDeriv ℝ k (g j) t) :=
    (A j).iteratedFDeriv_comp_left (hg j).contDiffAt hk'
  rw [hcomp]
  refine ((A j).norm_compContinuousMultilinearMap_le _).trans ?_
  have := norm_A_le j
  have h0 := norm_nonneg (iteratedFDeriv ℝ k (g j) t)
  nlinarith

end ClassOfDerivative

end KcPartialDeriv

end

open KcPartialDeriv in
/--
@isnad1 id=and.2h4v.s10.4ae44c06e8c1 from=translated src=- shape=5e11e3fe vocab=df1298bf
-/
theorem solution
    (n m : ℕ) (f : (Fin n → ℝ) → ℂ) (g : Fin n → (Fin n → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ m (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
    ContDiff ℝ (m + 1) f ∧
      (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧
      ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by
  have hderiv : ∀ t, HasFDerivAt f
      (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t :=
    hasFDerivAt_of_partials (fun j => (hg j).continuous) hfg
  refine ⟨contDiff_succ_iff_hasFDerivAt.mpr ⟨_, contDiff_sum_A hg, hderiv⟩, hderiv, ?_⟩
  intro k hk t
  have hfd : fderiv ℝ f = fun t => ∑ j, A j (g j t) :=
    funext fun t => (hderiv t).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  exact norm_iteratedFDeriv_sum_A_le hg hk t
