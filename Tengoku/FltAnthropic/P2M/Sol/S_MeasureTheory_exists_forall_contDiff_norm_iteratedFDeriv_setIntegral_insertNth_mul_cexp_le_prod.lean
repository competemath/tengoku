import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod

set_option autoImplicit false

open MeasureTheory

namespace PMDK6A

variable {n d : ℕ}

abbrev P (n : ℕ) := (Fin (n + 1) → ℝ) × ℝ

def cube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1)

/--
@isnad1 id=measurab.0h1v.s4.fb824754e9cc from=translated src=- shape=fe6f4f64 vocab=7fdbc6e2
-/
lemma measurableSet_cube : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/--
@isnad1 id=le.0h1v.s6.47c09408029e from=translated src=- shape=fb5c701c vocab=c20a3d97
-/
lemma cube_subset_Icc : cube d ⊆ Set.Icc (0 : Fin d → ℝ) 1 := by
  intro θ hθ
  simp only [cube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_true_left] at hθ
  exact ⟨fun i => (hθ i).1, fun i => (hθ i).2.le⟩

/--
@isnad1 id=eq.0h1v.s6.6f3964fbacba from=translated src=- shape=529c28aa vocab=278a5f22
-/
lemma volume_cube : volume (cube d) = 1 := by
  rw [cube, Real.volume_pi_Ico]; simp

/--
@isnad1 id=lt.0h1v.s6.3e9f2a0e8909 from=translated src=- shape=4387ef5c vocab=74d60c84
-/
lemma volume_cube_lt_top : volume (cube d) < ⊤ := by
  rw [volume_cube]; exact ENNReal.one_lt_top

noncomputable def em (m : Fin d → ℤ) (θ : Fin d → ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))

/--
@isnad1 id=eq.0h3v.s4.08506f302a10 from=translated src=- shape=36da4e2e vocab=51c5d042
-/
lemma norm_em (m : Fin d → ℤ) (θ : Fin d → ℝ) : ‖em m θ‖ = 1 := by
  rw [em, Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [this, Real.exp_zero]

/--
@isnad1 id=continuo.0h2v.s5.d19fdf925449 from=translated src=- shape=fd391d93 vocab=ddbd6b10
-/
lemma continuous_em (m : Fin d → ℤ) : Continuous (em m) := by
  unfold em
  refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
    (Complex.continuous_ofReal.comp ?_)))
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

structure IsWin (R : ℝ) (V : P n × (Fin d → ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) V
  supp : ∀ q : P n × (Fin d → ℝ), (∃ k, R < |q.1.1 k|) → V q = 0
  per : ∀ (q : P n × (Fin d → ℝ)) (i : Fin d), V (q.1, q.2 + Pi.single i 1) = V q
  pert : ∀ (q : P n × (Fin d → ℝ)), V ((q.1.1, q.1.2 + 1), q.2) = V q

private noncomputable def _root_.PMDK6A.dir (u : P n × (Fin d → ℝ)) (V : P n × (Fin d → ℝ) → ℂ) :
    P n × (Fin d → ℝ) → ℂ := fun q => fderiv ℝ V q u

export _root_.PMDK6A (dir)
/--
@isnad1 id=isopen.0h3v.s7.905232495c53 from=translated src=- shape=3429ae20 vocab=6d2ea383
-/
lemma isOpen_outside (R : ℝ) : IsOpen {q : P n × (Fin d → ℝ) | ∃ k, R < |q.1.1 k|} := by
  have : {q : P n × (Fin d → ℝ) | ∃ k, R < |q.1.1 k|} = ⋃ k, {q | R < |q.1.1 k|} := by
    ext q; simp
  rw [this]
  exact isOpen_iUnion fun k => isOpen_lt continuous_const
    (continuous_abs.comp ((continuous_apply k).comp (continuous_fst.comp continuous_fst)))

def vT (i : Fin d) : P n × (Fin d → ℝ) := ((0 : P n), (Pi.single i (1 : ℝ) : Fin d → ℝ))
def vt : P n × (Fin d → ℝ) := (((0 : Fin (n + 1) → ℝ), (1 : ℝ)), (0 : Fin d → ℝ))

/--
@isnad1 id=eq.0h4v.s7.1230945e13e8 from=translated src=- shape=59d84ab0 vocab=a4e71975
-/
lemma add_vT (q : P n × (Fin d → ℝ)) (i : Fin d) : q + vT i = (q.1, q.2 + Pi.single i 1) := by
  ext <;> simp [vT]

/--
@isnad1 id=eq.0h3v.s7.8d864fcc890f from=translated src=- shape=fed00f7a vocab=ce12b221
-/
lemma add_vt (q : P n × (Fin d → ℝ)) : q + (vt : P n × (Fin d → ℝ)) = ((q.1.1, q.1.2 + 1), q.2) := by
  ext <;> simp [vt]

/--
@isnad1 id=eq.1h5v.s7.c2297b2a68fe from=translated src=- shape=cb47bc9c vocab=b941f072
-/
lemma IsWin.comp_add_vT {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V) (i : Fin d) :
    (fun q => V (q + vT i)) = V := by
  funext q; rw [add_vT, hV.per]

/--
@isnad1 id=eq.1h4v.s7.521f85d55b29 from=translated src=- shape=d25fed53 vocab=ade98d0e
-/
lemma IsWin.comp_add_vt {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V) :
    (fun q => V (q + vt)) = V := by
  funext q; rw [add_vt, hV.pert]

/--
@isnad1 id=iswin.1h5v.s5.d3f1da92fced from=translated src=- shape=3420fbaa vocab=8dacdce6
-/
lemma IsWin.dir {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V)
    (u : P n × (Fin d → ℝ)) : IsWin R (dir u V) where
  smooth := ((contDiff_infty_iff_fderiv.1 hV.smooth).2).clm_apply contDiff_const
  supp := by
    intro q hq
    have hev : V =ᶠ[nhds q] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_outside R).mem_nhds hq] with q' hq'
      exact hV.supp q' hq'
    show fderiv ℝ V q u = 0
    rw [hev.fderiv_eq]; simp
  per := by
    intro q i
    show fderiv ℝ V (q.1, q.2 + Pi.single i 1) u = fderiv ℝ V q u
    rw [← add_vT, ← fderiv_comp_add_right (vT i), hV.comp_add_vT]
  pert := by
    intro q
    show fderiv ℝ V ((q.1.1, q.1.2 + 1), q.2) u = fderiv ℝ V q u
    rw [← add_vt, ← fderiv_comp_add_right vt, hV.comp_add_vt]

noncomputable def Ψ (m : Fin d → ℤ) (V : P n × (Fin d → ℝ) → ℂ) (p : P n) : ℂ :=
  ∫ θ in cube d, V (p, θ) * em m θ

noncomputable def dV (V : P n × (Fin d → ℝ) → ℂ) (q : P n × (Fin d → ℝ)) : P n →L[ℝ] ℂ :=
  (fderiv ℝ V q).comp (ContinuousLinearMap.inl ℝ (P n) (Fin d → ℝ))

/--
@isnad1 id=continuo.1h3v.s10.82b5d5a5b25b from=translated src=- shape=2e8f1fda vocab=dc6ff629
-/
lemma continuous_dV {V : P n × (Fin d → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Continuous (dV V) :=
  (((contDiff_infty_iff_fderiv.1 hV).2).continuous).clm_comp continuous_const

/--
@isnad1 id=hasfderi.1h5v.s9.ca50a74e2998 from=translated src=- shape=eed972e5 vocab=1c383333
-/
lemma hasFDerivAt_slice {V : P n × (Fin d → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (p : P n) (θ : Fin d → ℝ) :
    HasFDerivAt (fun p' : P n => V (p', θ)) (dV V (p, θ)) p := by
  have hd : HasFDerivAt V (fderiv ℝ V (p, θ)) (p, θ) :=
    (hV.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp p (hasFDerivAt_prodMk_left p θ)

/--
@isnad1 id=ex.1h5v.s8.7abafd9d9082 from=translated src=- shape=390e70ef vocab=504c225e
-/
lemma exists_local_bound {Y : Type*} [NormedAddCommGroup Y]
    {F : P n × (Fin d → ℝ) → Y} (hF : Continuous F) (p₀ : P n) :
    ∃ C : ℝ, ∀ p ∈ Metric.closedBall p₀ 1, ∀ θ ∈ cube d, ‖F (p, θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ (1 : ℝ)).prod
    (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1))).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun p hp θ hθ => hC (p, θ) (Set.mem_prod.mpr ⟨hp, cube_subset_Icc hθ⟩)⟩

/--
@isnad1 id=integrab.1h3v.s6.5b76a0f289b7 from=translated src=- shape=d93e3b88 vocab=b80d35ef
-/
lemma integrableOn_cube_of_continuous {Y : Type*} [NormedAddCommGroup Y] {f : (Fin d → ℝ) → Y}
    (hf : Continuous f) : IntegrableOn f (cube d) volume :=
  (hf.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1))).mono_set
    cube_subset_Icc

/--
@isnad1 id=hasfderi.1h6v.s11.8b3772de2a61 from=translated src=- shape=4da3709c vocab=a93c6264
-/
lemma hasFDerivAt_Ψ {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin d → ℤ) (p₀ : P n) :
    HasFDerivAt (Ψ m V) (∫ θ in cube d, em m θ • dV V (p₀, θ)) p₀ := by
  have hVc : Continuous V := hV.smooth.continuous
  have hdVc : Continuous (dV V) := continuous_dV hV.smooth
  obtain ⟨C, hC⟩ := exists_local_bound hdVc p₀
  have hslice : ∀ p, Continuous fun θ : Fin d → ℝ => em m θ • V (p, θ) := fun p =>
    (continuous_em m).smul (hVc.comp (continuous_const.prodMk continuous_id))
  have hslice' : ∀ p, Continuous fun θ : Fin d → ℝ => em m θ • dV V (p, θ) := fun p =>
    (continuous_em m).smul (hdVc.comp (continuous_const.prodMk continuous_id))
  have e : Ψ m V = fun p => ∫ θ in cube d, em m θ • V (p, θ) := by
    funext p; simp only [Ψ, smul_eq_mul, mul_comm]
  rw [e]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (cube d))
    (F := fun p θ => em m θ • V (p, θ)) (F' := fun p θ => em m θ • dV V (p, θ)) (x₀ := p₀)
    (s := Metric.ball p₀ 1) (bound := fun _ => C) (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p => (hslice p).aestronglyMeasurable)
    (integrableOn_cube_of_continuous (hslice p₀))
    (hslice' p₀).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_cube).mpr (ae_of_all _ fun θ hθ p hp => by
      rw [norm_smul, norm_em, one_mul]
      exact hC p (Metric.ball_subset_closedBall hp) θ hθ))
    (integrableOn_const volume_cube_lt_top.ne)
    (ae_of_all _ fun θ p _ => (hasFDerivAt_slice hV.smooth p θ).const_smul (em m θ))

/--
@isnad1 id=eq.1h7v.s10.9be8f59d55e7 from=translated src=- shape=a0ed4f4d vocab=3bae9783
-/
lemma fderiv_Ψ_apply {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin d → ℤ) (p : P n) (v : P n) :
    fderiv ℝ (Ψ m V) p v = Ψ m (dir (v, (0 : Fin d → ℝ)) V) p := by
  rw [(hasFDerivAt_Ψ hV m p).fderiv]
  have hint : Integrable (fun θ => em m θ • dV V (p, θ)) (volume.restrict (cube d)) :=
    integrableOn_cube_of_continuous
      ((continuous_em m).smul ((continuous_dV hV.smooth).comp (continuous_const.prodMk continuous_id)))
  rw [ContinuousLinearMap.integral_apply hint v]
  simp only [Ψ, dir, dV, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, mul_comm]

/--
@isnad1 id=differen.1h5v.s8.03d15c0ea487 from=translated src=- shape=28d2e1cf vocab=dd0ed0c9
-/
lemma differentiable_Ψ {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin d → ℤ) : Differentiable ℝ (Ψ m V) := fun p => (hasFDerivAt_Ψ hV m p).differentiableAt

/--
@isnad1 id=contdiff.1h6v.s8.5aed95585cf4 from=translated src=- shape=6d700774 vocab=23f249d3
-/
lemma contDiff_Ψ_nat (R : ℝ) (m : Fin d → ℤ) : ∀ (i : ℕ) (V : P n × (Fin d → ℝ) → ℂ),
    IsWin R V → ContDiff ℝ i (Ψ m V) := by
  intro i
  induction i with
  | zero =>
    intro V hV
    exact contDiff_zero.mpr (differentiable_Ψ hV m).continuous
  | succ i ih =>
    intro V hV
    rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨differentiable_Ψ hV m, fun h => absurd h (by simp), fun v => ?_⟩
    have : (fun p => fderiv ℝ (Ψ m V) p v) = Ψ m (dir (v, (0 : Fin d → ℝ)) V) :=
      funext fun p => fderiv_Ψ_apply hV m p v
    rw [this]
    exact ih _ (hV.dir _)

/--
@isnad1 id=contdiff.1h5v.s8.89b6cc06f4b1 from=translated src=- shape=734eb515 vocab=f7d3d49c
-/
lemma contDiff_Ψ {R : ℝ} {V : P n × (Fin d → ℝ) → ℂ} (hV : IsWin R V) (m : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (Ψ m V) :=
  contDiff_infty.2 fun i => contDiff_Ψ_nat R m i V hV

private noncomputable def _root_.PMDK6A.DDX : (ℓ : ℕ) → (Fin ℓ → P n) → (P n × (Fin d → ℝ) → ℂ) → (P n × (Fin d → ℝ) → ℂ)
  | 0, _, V => V
  | ℓ + 1, u, V => DDX ℓ (Fin.init u) (dir (u (Fin.last ℓ), (0 : Fin d → ℝ)) V)

export _root_.PMDK6A (DDX)
/--
@isnad1 id=iswin.1h6v.s5.a717aff55951 from=translated src=- shape=ef365049 vocab=1bdd6025
-/
lemma IsWin.DDX {R : ℝ} : ∀ (ℓ : ℕ) (u : Fin ℓ → P n) {V : P n × (Fin d → ℝ) → ℂ},
    IsWin R V → IsWin R (DDX ℓ u V)
  | 0, _, _, hV => hV
  | ℓ + 1, u, _, hV => IsWin.DDX ℓ (Fin.init u) (hV.dir _)

/--
@isnad1 id=eq.1h8v.s10.1df1b425b0fd from=translated src=- shape=85a8120f vocab=2c799524
-/
lemma iteratedFDeriv_Ψ_apply {R : ℝ} (m : Fin d → ℤ) : ∀ (ℓ : ℕ) (V : P n × (Fin d → ℝ) → ℂ),
    IsWin R V → ∀ (p : P n) (u : Fin ℓ → P n),
      (iteratedFDeriv ℝ ℓ (Ψ m V) p) u = Ψ m (DDX ℓ u V) p := by
  intro ℓ
  induction ℓ with
  | zero => intro V hV p u; simp [DDX]
  | succ ℓ ih =>
    intro V hV p u
    rw [iteratedFDeriv_succ_apply_right]
    set L : (P n →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (u (Fin.last ℓ)) with hL
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ (Ψ m V) y) :=
      (contDiff_infty_iff_fderiv.1 (contDiff_Ψ hV m)).2
    have h1 : iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last ℓ))) p =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ m V) y) p) := by
      have : (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last ℓ))) = L ∘ (fun y => fderiv ℝ (Ψ m V) y) := by
        funext y; simp [hL]
      rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top)]
    have h2 : ((iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ m V) y) p) (Fin.init u)) (u (Fin.last ℓ)) =
        (iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last ℓ))) p) (Fin.init u) := by
      rw [h1]; simp [hL]
    rw [h2]
    have h3 : (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last ℓ))) = Ψ m (dir (u (Fin.last ℓ), (0 : Fin d → ℝ)) V) :=
      funext fun y => fderiv_Ψ_apply hV m y _
    rw [h3, ih _ (hV.dir _) p (Fin.init u)]
    rfl

/--
@isnad1 id=le.1h6v.s12.a8cc2062673a from=translated src=- shape=c982976f vocab=4658bf0b
-/
lemma norm_iteratedFDeriv_dir_le {V : P n × (Fin d → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (w : P n × (Fin d → ℝ)) (j : ℕ) (q : P n × (Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (dir w V) q‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) V q‖ := by
  set L : ((P n × (Fin d → ℝ)) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ w with hL
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ V y) := (contDiff_infty_iff_fderiv.1 hV).2
  have : dir w V = L ∘ (fun y => fderiv ℝ V y) := by funext y; simp [hL, dir]
  rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top),
    ← norm_iteratedFDeriv_fderiv]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ V) q)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) q‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) q‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) (fun f => ?_)
        rw [hL, ContinuousLinearMap.apply_apply, mul_comm]
        exact f.le_opNorm w

/--
@isnad1 id=le.1h8v.s11.7d7c8d7a8ec8 from=translated src=- shape=5fec3a58 vocab=75eb2791
-/
lemma norm_iteratedFDeriv_DDX_le {R : ℝ} : ∀ (ℓ : ℕ) (u : Fin ℓ → P n)
    {V : P n × (Fin d → ℝ) → ℂ}, IsWin R V → ∀ (j : ℕ) (q : P n × (Fin d → ℝ)),
    ‖iteratedFDeriv ℝ j (DDX ℓ u V) q‖ ≤ (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + ℓ) V q‖
  | 0, u, V, hV, j, q => by simp [DDX]
  | ℓ + 1, u, V, hV, j, q => by
    have ih := norm_iteratedFDeriv_DDX_le ℓ (Fin.init u) (hV.dir (u (Fin.last ℓ), (0 : Fin d → ℝ))) j q
    have h2 := norm_iteratedFDeriv_dir_le hV.smooth (u (Fin.last ℓ), (0 : Fin d → ℝ)) (j + ℓ) q
    have hnorm : ‖(u (Fin.last ℓ), (0 : Fin d → ℝ))‖ = ‖u (Fin.last ℓ)‖ := by
      simp [Prod.norm_def]
    rw [hnorm] at h2
    calc ‖iteratedFDeriv ℝ j (DDX (ℓ + 1) u V) q‖
        = ‖iteratedFDeriv ℝ j (DDX ℓ (Fin.init u) (dir (u (Fin.last ℓ), (0 : Fin d → ℝ)) V)) q‖ := rfl
      _ ≤ (∏ i, ‖Fin.init u i‖) * ‖iteratedFDeriv ℝ (j + ℓ) (dir (u (Fin.last ℓ), (0 : Fin d → ℝ)) V) q‖ := ih
      _ ≤ (∏ i, ‖Fin.init u i‖) * (‖u (Fin.last ℓ)‖ * ‖iteratedFDeriv ℝ (j + ℓ + 1) V q‖) :=
          mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + (ℓ + 1)) V q‖ := by
          have e : iteratedFDeriv ℝ (j + (ℓ + 1)) V q = iteratedFDeriv ℝ (j + ℓ + 1) V q := rfl
          rw [e, Fin.prod_univ_castSucc (fun i => ‖u i‖)]
          simp only [Fin.init]
          ring

/--
@isnad1 id=eq.0h3v.s7.2d99aff635a7 from=translated src=- shape=95bb939b vocab=29fd623f
-/
lemma norm_vT (i : Fin d) : ‖(vT i : P n × (Fin d → ℝ))‖ = 1 := by
  simp only [vT, Prod.norm_def, norm_zero]
  rw [max_eq_right (norm_nonneg _)]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i' => ?_
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  · have := norm_le_pi_norm (Pi.single i (1 : ℝ) : Fin d → ℝ) i
    simpa using this

/--
@isnad1 id=le.1h6v.s12.18a1e7edb164 from=translated src=- shape=0a0d28ae vocab=d23e1c0e
-/
lemma norm_iteratedFDeriv_dT2_le {V : P n × (Fin d → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (a : Fin d) (j : ℕ) (q : P n × (Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ j (dir (vT a) (dir (vT a) V)) q‖ ≤ ‖iteratedFDeriv ℝ (j + 2) V q‖ := by
  have hV' : ContDiff ℝ (⊤ : ℕ∞) (dir (vT a) V) :=
    ((contDiff_infty_iff_fderiv.1 hV).2).clm_apply contDiff_const
  calc _ ≤ ‖(vT a : P n × (Fin d → ℝ))‖ * ‖iteratedFDeriv ℝ (j + 1) (dir (vT a) V) q‖ :=
        norm_iteratedFDeriv_dir_le hV' _ j q
    _ ≤ ‖(vT a : P n × (Fin d → ℝ))‖ * (‖(vT a : P n × (Fin d → ℝ))‖ *
          ‖iteratedFDeriv ℝ (j + 1 + 1) V q‖) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dir_le hV _ (j + 1) q) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 2) V q‖ := by rw [norm_vT]; ring_nf

section Torus

attribute [local instance] instMeasureSpaceUnitAddCircle

/--
@isnad1 id=eq.0h0v.s4.1b16bfdc3f3f from=translated src=- shape=46cdbc00 vocab=97a85765
-/
theorem volume_unitAddCircle_eq : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := rfl

/--
@isnad1 id=isaddrig.0h0v.s4.e281ee50493d from=translated src=- shape=3905abf2 vocab=ae066c88
-/
scoped instance instIsAddRightInvariant_unitAddCircle : (volume : Measure UnitAddCircle).IsAddRightInvariant := by
  rw [volume_unitAddCircle_eq]; infer_instance

/--
@isnad1 id=sigmafin.0h0v.s3.7e6370fec4a9 from=translated src=- shape=4b718b57 vocab=be448478
-/
scoped instance instSigmaFinite_unitAddCircle : SigmaFinite (volume : Measure UnitAddCircle) := by
  rw [volume_unitAddCircle_eq]; infer_instance

/--
@isnad1 id=eq.1h4v.s7.8131cbd99ff3 from=translated src=- shape=7089945d vocab=867b9135
-/
theorem periodic_intCast (g : (Fin d → ℝ) → ℂ)
    (hper : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1) = g θ)
    (θ : Fin d → ℝ) (k : Fin d → ℤ) : g (θ + fun i => (k i : ℝ)) = g θ := by
  classical
  let P : AddSubgroup (Fin d → ℝ) :=
    { carrier := {v | ∀ θ, g (θ + v) = g θ}
      add_mem' := fun {a b} ha hb θ => by
        show g (θ + (a + b)) = g θ
        rw [← add_assoc, hb, ha]
      zero_mem' := fun θ => by show g (θ + 0) = g θ; rw [add_zero]
      neg_mem' := fun {a} ha θ => by
        show g (θ + -a) = g θ
        have h := ha (θ + -a)
        rw [neg_add_cancel_right] at h
        exact h.symm }
  have hsingle : ∀ (j : Fin d) (n : ℤ), (Pi.single j ((n : ℝ)) : Fin d → ℝ) ∈ P := by
    intro j n
    have h1 : (Pi.single j (1 : ℝ) : Fin d → ℝ) ∈ P := fun θ => hper θ j
    have : (Pi.single j ((n : ℝ)) : Fin d → ℝ) = n • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
      ext i
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this]
    exact P.zsmul_mem h1 n
  have hk : (fun i => (k i : ℝ)) ∈ P := by
    have : (fun i => (k i : ℝ)) = ∑ j : Fin d, (Pi.single j ((k j : ℝ)) : Fin d → ℝ) :=
      (Finset.univ_sum_single (fun i => (k i : ℝ))).symm
    rw [this]
    exact P.sum_mem fun j _ => hsingle j (k j)
  exact hk θ

def qT (θ : Fin d → ℝ) : UnitAddTorus (Fin d) := fun i => (θ i : UnitAddCircle)

noncomputable def secT (x : UnitAddTorus (Fin d)) : Fin d → ℝ := fun i => ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ))

/--
@isnad1 id=eq.0h2v.s4.79070ad21f3a from=translated src=- shape=60f8d03b vocab=c6781694
-/
lemma qT_secT (x : UnitAddTorus (Fin d)) : qT (secT x) = x := by
  funext i
  exact AddCircle.coe_equivIco

/--
@isnad1 id=eq.0h3v.s6.9b390d56c6a5 from=translated src=- shape=9756cd32 vocab=1daed576
-/
lemma qT_add (θ w : Fin d → ℝ) : qT (θ + w) = qT θ + qT w := by
  funext i; simp [qT]

/--
@isnad1 id=ex.0h2v.s6.7dbd5a3cd504 from=translated src=- shape=0520872e vocab=a187fa6c
-/
lemma secT_qT (θ : Fin d → ℝ) : ∃ k : Fin d → ℤ, secT (qT θ) = θ + fun i => (k i : ℝ) := by
  refine ⟨fun i => -⌊θ i⌋, funext fun i => ?_⟩
  show ((AddCircle.equivIco (1 : ℝ) 0 ((θ i : ℝ) : UnitAddCircle) : ℝ)) = θ i + ((-⌊θ i⌋ : ℤ) : ℝ)
  rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, Int.fract, Int.cast_neg, sub_eq_add_neg]

/--
@isnad1 id=eq.1h3v.s6.07c710d4f642 from=translated src=- shape=c5ebbbbd vocab=da65bc9e
-/
lemma comp_secT_qT (g : (Fin d → ℝ) → ℂ)
    (hper : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1) = g θ) (θ : Fin d → ℝ) :
    g (secT (qT θ)) = g θ := by
  obtain ⟨k, hk⟩ := secT_qT θ
  rw [hk]
  exact periodic_intCast g hper θ k

/--
@isnad1 id=eq.1h2v.s7.507089d8eae4 from=translated src=- shape=beb0ee1a vocab=438f5900
-/
lemma integral_cube_eq_torus (g : (Fin d → ℝ) → ℂ)
    (hper : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1) = g θ) :
    ∫ θ in cube d, g θ = ∫ x : UnitAddTorus (Fin d), g (secT x) := by
  refine Eq.trans ?_ (UnitAddTorus.integral_preimage (fun x => g (secT x)) (0 : Fin d → ℝ)).symm
  have hset : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)}
      =ᵐ[volume] cube d := by
    have h1 : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin d → ℝ) i) ((0 : Fin d → ℝ) i + 1)}
        = Set.pi Set.univ (fun i => Set.Ioc ((0 : Fin d → ℝ) i) ((1 : Fin d → ℝ) i)) := by
      ext x; simp
    have h2 : cube d = Set.pi Set.univ (fun i => Set.Ico ((0 : Fin d → ℝ) i) ((1 : Fin d → ℝ) i)) := by
      ext x; simp [cube]
    rw [h1, h2, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hset]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show g x = g (secT (qT x))
  exact (comp_secT_qT g hper x).symm

/--
@isnad1 id=eq.1h3v.s8.6b6a1993ff7c from=translated src=- shape=4beeb6bc vocab=2827faf6
-/
lemma integral_cube_translate (g : (Fin d → ℝ) → ℂ)
    (hper : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1) = g θ) (w : Fin d → ℝ) :
    ∫ θ in cube d, g (θ + w) = ∫ θ in cube d, g θ := by
  have hper' : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1 + w) = g (θ + w) := by
    intro θ j; rw [add_right_comm, hper]
  rw [integral_cube_eq_torus (fun θ => g (θ + w)) hper', integral_cube_eq_torus g hper]
  have key : ∀ x : UnitAddTorus (Fin d), g (secT x + w) = g (secT (x + qT w)) := by
    intro x
    have : x + qT w = qT (secT x + w) := by rw [qT_add, qT_secT]
    rw [this, comp_secT_qT g hper]
  simp_rw [key]
  exact integral_add_right_eq_self (fun x => g (secT x)) (qT w)

end Torus

/--
@isnad1 id=eq.0h4v.s6.9385d3551c8f from=translated src=- shape=3eab9520 vocab=01a19164
-/
lemma em_periodic (m : Fin d → ℤ) (θ : Fin d → ℝ) (j : Fin d) :
    em m (θ + Pi.single j 1) = em m θ := by
  unfold em
  have : (∑ i, (m i : ℝ) * (θ + (Pi.single j 1 : Fin d → ℝ)) i) = (∑ i, (m i : ℝ) * θ i) + (m j : ℝ) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [this]
  push_cast
  have h1 : -(2 * (Real.pi : ℂ) * Complex.I * ((m j : ℤ) : ℂ)) = ((-(m j) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [mul_add, neg_add, Complex.exp_add, h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/--
@isnad1 id=eq.0h5v.s7.0563a8b81d58 from=translated src=- shape=f4eb87ef vocab=e75a9da5
-/
lemma em_sub_smul (m : Fin d → ℤ) (θ : Fin d → ℝ) (j : Fin d) (t : ℝ) :
    em m (θ - t • Pi.single j 1) = em m θ * Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) := by
  unfold em
  have : (∑ i, (m i : ℝ) * (θ - t • (Pi.single j 1 : Fin d → ℝ)) i) = (∑ i, (m i : ℝ) * θ i) - (m j : ℝ) * t := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [this, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.2h4v.s9.4aabd3bc05e3 from=translated src=- shape=1ec5c4ef vocab=7fa1943f
-/
lemma integral_cube_fderiv_mul_em (g : (Fin d → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hper : ∀ (θ : Fin d → ℝ) (j : Fin d), g (θ + Pi.single j 1) = g θ)
    (m : Fin d → ℤ) (j : Fin d) :
    ∫ θ in cube d, fderiv ℝ g θ (Pi.single j 1) * em m θ =
      (2 * Real.pi * Complex.I * (m j : ℝ)) * ∫ θ in cube d, g θ * em m θ := by
  set v : Fin d → ℝ := Pi.single j 1 with hv

  set φ : ℝ → ℂ := fun t => ∫ θ in cube d, g (θ + t • v) * em m θ with hφ

  have hφ1 : ∀ t : ℝ, φ t = Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) *
      ∫ θ in cube d, g θ * em m θ := by
    intro t
    have hperF : ∀ (θ : Fin d → ℝ) (i : Fin d),
        (fun θ => g θ * em m (θ - t • v)) (θ + Pi.single i 1) = (fun θ => g θ * em m (θ - t • v)) θ := by
      intro θ i
      simp only
      rw [hper, show θ + Pi.single i 1 - t • v = (θ - t • v) + Pi.single i 1 by abel, em_periodic]
    have := integral_cube_translate (fun θ => g θ * em m (θ - t • v)) hperF (t • v)
    simp only [add_sub_cancel_right] at this
    rw [hφ]
    simp only
    rw [this]
    simp_rw [hv, em_sub_smul]
    rw [← integral_const_mul]
    congr 1; funext θ; ring

  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fun θ => fderiv ℝ g θ) := (contDiff_infty_iff_fderiv.1 hg).2.continuous
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (-1 : Fin d → ℝ) - 1) (b := (1 : Fin d → ℝ) + 1))).exists_bound_of_continuousOn
    hg'c.continuousOn
  have hmem : ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ θ ∈ cube d,
      θ + t • v ∈ Set.Icc ((-1 : Fin d → ℝ) - 1) ((1 : Fin d → ℝ) + 1) := by
    intro t ht θ hθ
    have ht' : |t| < 1 := by simpa using ht
    have hθ' := cube_subset_Icc hθ
    constructor
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, Pi.one_apply, smul_eq_mul, hv]
      have h1 : (0 : ℝ) ≤ θ i := hθ'.1 i
      by_cases hij : i = j
      · subst hij; simp; nlinarith [abs_lt.mp ht']
      · simp [hij]; linarith
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, hv]
      have h1 : θ i ≤ 1 := hθ'.2 i
      by_cases hij : i = j
      · subst hij; simp; nlinarith [abs_lt.mp ht']
      · simp [hij]; linarith
  have hderiv : ∀ (θ : Fin d → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (θ + s • v) * em m θ) (fderiv ℝ g (θ + t • v) v * em m θ) t := by
    intro θ t
    have hl : HasDerivAt (fun s : ℝ => θ + s • v) v t := by
      have := ((hasDerivAt_id t).smul_const v).const_add θ
      simpa using this
    have hG : HasFDerivAt g (fderiv ℝ g (θ + t • v)) (θ + t • v) :=
      (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact (hG.comp_hasDerivAt t hl).mul_const _
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (cube d))
    (F := fun (t : ℝ) (θ : Fin d → ℝ) => g (θ + t • v) * em m θ)
    (F' := fun (t : ℝ) (θ : Fin d → ℝ) => fderiv ℝ g (θ + t • v) v * em m θ) (x₀ := 0)
    (s := Metric.ball 0 1) (bound := fun _ => C * ‖v‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => ((hgc.comp (continuous_id.add continuous_const)).mul
      (continuous_em m)).aestronglyMeasurable)
    (integrableOn_cube_of_continuous ((hgc.comp (continuous_id.add continuous_const)).mul (continuous_em m)))
    (((hg'c.comp (continuous_id.add continuous_const)).clm_apply continuous_const).mul
      (continuous_em m)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_cube).mpr (ae_of_all _ fun θ hθ t ht => by
      rw [norm_mul, norm_em, mul_one]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC _ (hmem t ht θ hθ)) (norm_nonneg _))))
    (integrableOn_const volume_cube_lt_top.ne)
    (ae_of_all _ fun θ t _ => hderiv θ t)
  have hD2 : HasDerivAt φ (∫ θ in cube d, fderiv ℝ g (θ + (0 : ℝ) • v) v * em m θ) 0 := hD.2
  simp only [zero_smul, add_zero] at hD2

  have hD3 : HasDerivAt φ (Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * (0 : ℝ)) *
      (2 * Real.pi * Complex.I * (m j : ℝ)) * ∫ θ in cube d, g θ * em m θ) 0 := by
    have e : φ = fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) *
        ∫ θ in cube d, g θ * em m θ := funext hφ1
    rw [e]
    apply HasDerivAt.mul_const
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * (m j : ℝ) * (t : ℂ))
        (2 * Real.pi * Complex.I * (m j : ℝ) * 1) 0 := by
      have : HasDerivAt (fun t : ℝ => ((id t : ℝ) : ℂ)) ((1 : ℝ) : ℂ) 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
      simpa using this.const_mul (2 * Real.pi * Complex.I * (m j : ℝ))
    have := h1.cexp
    simpa using this
  have := hD2.unique hD3
  rw [this]
  simp

/--
@isnad1 id=eq.1h7v.s6.2302ebb9e2c8 from=translated src=- shape=f91da82d vocab=a8188a89
-/
lemma Ψ_dT {R : ℝ} {U : P n × (Fin d → ℝ) → ℂ} (hU : IsWin R U) (m : Fin d → ℤ)
    (j : Fin d) (p : P n) :
    Ψ m (dir (vT j) U) p = (2 * Real.pi * Complex.I * (m j : ℝ)) * Ψ m U p := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun θ : Fin d → ℝ => U (p, θ)) :=
    hU.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hgper : ∀ (θ : Fin d → ℝ) (i : Fin d), U (p, θ + Pi.single i 1) = U (p, θ) :=
    fun θ i => hU.per (p, θ) i
  have key := integral_cube_fderiv_mul_em (fun θ => U (p, θ)) hg hgper m j
  have hderiv : ∀ θ : Fin d → ℝ, fderiv ℝ (fun θ : Fin d → ℝ => U (p, θ)) θ (Pi.single j 1) =
      dir (vT j) U (p, θ) := by
    intro θ
    have hd : HasFDerivAt U (fderiv ℝ U (p, θ)) (p, θ) :=
      (hU.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun θ' : Fin d → ℝ => U (p, θ'))
        ((fderiv ℝ U (p, θ)).comp (ContinuousLinearMap.inr ℝ (P n) (Fin d → ℝ))) θ :=
      hd.comp θ (hasFDerivAt_prodMk_right p θ)
    rw [h2.fderiv]
    simp [dir, vT]
  simp_rw [hderiv] at key
  exact key

/--
@isnad1 id=eq.2h7v.s7.55b1e597b117 from=translated src=- shape=cd3b15f9 vocab=f0a734c7
-/
lemma norm_Ψ_eq {R : ℝ} {U : P n × (Fin d → ℝ) → ℂ} (hU : IsWin R U) (m : Fin d → ℤ)
    (j : Fin d) (hj : m j ≠ 0) (p : P n) :
    ‖Ψ m U p‖ = ‖Ψ m (dir (vT j) (dir (vT j) U)) p‖ * ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ := by
  rw [Ψ_dT (hU.dir _) m j p, Ψ_dT hU m j p]
  set C : ℂ := 2 * Real.pi * Complex.I * (m j : ℝ) with hCdef
  clear_value C
  have hn : ‖C‖ = 2 * Real.pi * |(m j : ℝ)| := by
    rw [hCdef, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [norm_mul, norm_mul, hn]
  have hpos : 0 < 2 * Real.pi * |(m j : ℝ)| := by
    have : (0 : ℝ) < |(m j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
    positivity
  field_simp

/--
@isnad1 id=le.1h6v.s6.4d2b1f83fd03 from=translated src=- shape=b250c866 vocab=924ae954
-/
lemma norm_Ψ_le_of_bound {U : P n × (Fin d → ℝ) → ℂ} (m : Fin d → ℤ) (p : P n)
    {C : ℝ} (hC : ∀ θ ∈ cube d, ‖U (p, θ)‖ ≤ C) : ‖Ψ m U p‖ ≤ C := by
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin d → ℝ))) (s := cube d)
    (f := fun θ => U (p, θ) * em m θ) (C := C) volume_cube_lt_top
    (fun θ hθ => by rw [norm_mul, norm_em, mul_one]; exact hC θ hθ)
  rwa [Measure.real, volume_cube, ENNReal.toReal_one, mul_one] at this

/--
@isnad1 id=le.4h9v.s11.36bfa83e8174 from=translated src=- shape=ea0c6322 vocab=78378720
-/
lemma decay {R : ℝ} (m : Fin d → ℤ) (p : P n) :
    ∀ (S : Finset (Fin d)), (∀ j ∈ S, m j ≠ 0) →
      ∀ (k : ℕ) (C : ℝ) (U : P n × (Fin d → ℝ) → ℂ), IsWin R U → 2 * S.card ≤ k →
        (∀ i : ℕ, i ≤ k → ∀ q, ‖iteratedFDeriv ℝ i U q‖ ≤ C) →
        ‖Ψ m U p‖ ≤ C * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ k C U hU _ hb
    rw [Finset.prod_empty, mul_one]
    exact norm_Ψ_le_of_bound m p fun θ _ => by
      have := hb 0 (Nat.zero_le k) (p, θ)
      rwa [norm_iteratedFDeriv_zero] at this
  | insert a S ha ih =>
    intro hm k C U hU hk hb
    have hma : m a ≠ 0 := hm a (Finset.mem_insert_self a S)
    have hmS : ∀ j ∈ S, m j ≠ 0 := fun j hj => hm j (Finset.mem_insert_of_mem hj)
    rw [Finset.card_insert_of_notMem ha] at hk
    set U' := dir (vT a) (dir (vT a) U) with hU'
    have hU'w : IsWin R U' := (hU.dir _).dir _
    have hb' : ∀ i : ℕ, i ≤ k - 2 → ∀ q, ‖iteratedFDeriv ℝ i U' q‖ ≤ C := fun i hi q =>
      (norm_iteratedFDeriv_dT2_le hU.smooth a i q).trans (hb (i + 2) (by omega) q)
    have := ih hmS (k - 2) C U' hU'w (by omega) hb'
    rw [norm_Ψ_eq hU m a hma p, Finset.prod_insert ha]
    have hpos : 0 ≤ ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ := by positivity
    calc ‖Ψ m U' p‖ * ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹
        ≤ (C * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹) * ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C * (((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹) := by ring

/--
@isnad1 id=eq.2h6v.s11.846b93deb930 from=translated src=- shape=24fc2090 vocab=02db3702
-/
lemma iteratedFDeriv_eq_zero_outside {R : ℝ} {W : P n × (Fin d → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) (q : P n × (Fin d → ℝ)) (hq : ∃ k, R < |q.1.1 k|) : iteratedFDeriv ℝ i W q = 0 := by
  have hev : W =ᶠ[nhds q] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_outside R).mem_nhds hq] with q' hq'
    exact hW.supp q' hq'
  have := (hev.iteratedFDeriv ℝ i).eq_of_nhds
  rw [this, iteratedFDeriv_fun_zero]
  rfl

/--
@isnad1 id=eq.1h5v.s6.d33b379fe179 from=translated src=- shape=dcf11f53 vocab=3e21666b
-/
lemma periodic_zsmul {X : Type*} [AddCommGroup X] (f : X → ℂ) (v : X) (h : ∀ q, f (q + v) = f q)
    (z : ℤ) (q : X) : f (q + z • v) = f q := by
  let Q : AddSubgroup X :=
    { carrier := {w | ∀ q, f (q + w) = f q}
      add_mem' := fun {a b} ha hb q => by
        show f (q + (a + b)) = f q
        rw [← add_assoc, hb, ha]
      zero_mem' := fun q => by show f (q + 0) = f q; rw [add_zero]
      neg_mem' := fun {a} ha q => by
        show f (q + -a) = f q
        have h' := ha (q + -a)
        rw [neg_add_cancel_right] at h'
        exact h'.symm }
  have hv : v ∈ Q := h
  exact (Q.zsmul_mem hv z) q

/--
@isnad1 id=eq.1h7v.s11.8f9e0c021b63 from=translated src=- shape=935d8f12 vocab=5789d028
-/
lemma iteratedFDeriv_periodic_θ {R : ℝ} {W : P n × (Fin d → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) (q : P n × (Fin d → ℝ)) (k : Fin d → ℤ) :
    iteratedFDeriv ℝ i W (q + (((0 : Fin (n + 1) → ℝ), (0 : ℝ)), fun j => (k j : ℝ))) = iteratedFDeriv ℝ i W q := by
  have hfun : (fun q' => W (q' + (((0 : Fin (n + 1) → ℝ), (0 : ℝ)), fun j => (k j : ℝ)))) = W := by
    funext q'
    have : q' + (((0 : Fin (n + 1) → ℝ), (0 : ℝ)), fun j => (k j : ℝ)) = (q'.1, q'.2 + fun j => (k j : ℝ)) := by
      ext <;> simp
    rw [this]
    exact periodic_intCast (fun θ => W (q'.1, θ)) (fun θ j => hW.per (q'.1, θ) j) q'.2 k
  rw [← iteratedFDeriv_comp_add_right i, hfun]

/--
@isnad1 id=eq.1h7v.s11.ec09a968969a from=translated src=- shape=ab42d7f1 vocab=39219e1d
-/
lemma iteratedFDeriv_periodic_t {R : ℝ} {W : P n × (Fin d → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) (q : P n × (Fin d → ℝ)) (z : ℤ) :
    iteratedFDeriv ℝ i W (q + z • (vt : P n × (Fin d → ℝ))) = iteratedFDeriv ℝ i W q := by
  have hfun : (fun q' => W (q' + z • (vt : P n × (Fin d → ℝ)))) = W := by
    funext q'
    exact periodic_zsmul W vt (fun q'' => by rw [add_vt, hW.pert]) z q'
  rw [← iteratedFDeriv_comp_add_right i, hfun]

/--
@isnad1 id=ex.1h5v.s10.1744c93f73b7 from=translated src=- shape=0eefdbce vocab=c066c1a8
-/
lemma exists_bound_iteratedFDeriv {R : ℝ} {W : P n × (Fin d → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q, ‖iteratedFDeriv ℝ i W q‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ i W) :=
    hW.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (((isCompact_Icc (a := fun _ : Fin (n + 1) => -R) (b := fun _ : Fin (n + 1) => R)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).prod
    (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1))).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun q => ?_⟩
  by_cases hq : ∃ k, R < |q.1.1 k|
  · rw [iteratedFDeriv_eq_zero_outside hW i q hq, norm_zero]; exact le_max_right _ _
  · push_neg at hq
    set k : Fin d → ℤ := fun j => ⌊q.2 j⌋ with hk
    set z : ℤ := ⌊q.1.2⌋ with hz
    set q' : P n × (Fin d → ℝ) := ((q.1.1, Int.fract q.1.2), fun j => Int.fract (q.2 j)) with hq'
    have hqq : q = q' + z • (vt : P n × (Fin d → ℝ)) + (((0 : Fin (n + 1) → ℝ), (0 : ℝ)), fun j => (k j : ℝ)) := by
      ext j
      · simp [hq', vt]
      · simp only [hq', hz, vt, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          mul_one, add_zero]
        rw [← Int.self_sub_floor q.1.2]; push_cast; ring
      · simp only [hq', hk, vt, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
          smul_zero, add_zero]
        rw [← Int.self_sub_floor (q.2 j)]; ring
    rw [hqq, iteratedFDeriv_periodic_θ hW i _ k, iteratedFDeriv_periodic_t hW i q' z]
    refine (hC q' (Set.mem_prod.mpr ⟨Set.mem_prod.mpr ⟨?_, ?_⟩, ?_⟩)).trans (le_max_left _ _)
    · simp only [hq', Set.mem_Icc]
      exact ⟨fun j => (abs_le.mp (hq j)).1, fun j => (abs_le.mp (hq j)).2⟩
    · simp only [hq', Set.mem_Icc]
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · simp only [hq', Set.mem_Icc]
      exact ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩

/--
@isnad1 id=ex.1h5v.s10.64a2f303bb19 from=translated src=- shape=a19e940c vocab=c066c1a8
-/
lemma exists_uniform_bound {R : ℝ} {W : P n × (Fin d → ℝ) → ℂ} (hW : IsWin R W) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ N → ∀ q, ‖iteratedFDeriv ℝ i W q‖ ≤ M := by
  choose C hC0 hC using fun i => exists_bound_iteratedFDeriv hW i
  refine ⟨∑ i ∈ Finset.range (N + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, fun i hi q => ?_⟩
  exact (hC i q).trans (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr (by omega)))

/--
@isnad1 id=eq.0h5v.s8.24accfa81858 from=translated src=- shape=8c3b97dd vocab=d4a698ff
-/
lemma insertNth_add_single_succAbove (j : Fin (d + 1)) (t : ℝ) (θ' : Fin d → ℝ) (i : Fin d) :
    (Fin.insertNth (α := fun _ => ℝ) j t (θ' + Pi.single i 1) : Fin (d + 1) → ℝ) =
      Fin.insertNth (α := fun _ => ℝ) j t θ' + Pi.single (j.succAbove i) 1 := by
  ext ℓ
  rcases Fin.eq_self_or_eq_succAbove j ℓ with rfl | ⟨i', rfl⟩
  · simp [Fin.insertNth_apply_same, Pi.single_apply, Fin.succAbove_ne]
  · simp only [Fin.insertNth_apply_succAbove, Pi.add_apply]
    by_cases h : i' = i
    · subst h; simp
    · have : j.succAbove i' ≠ j.succAbove i := fun e => h (Fin.succAbove_right_injective e)
      simp [Pi.single_apply, h, this]

/--
@isnad1 id=eq.0h4v.s8.3813ebffe3c5 from=translated src=- shape=cc21aa67 vocab=9e6a79d2
-/
lemma insertNth_add_one (j : Fin (d + 1)) (t : ℝ) (θ' : Fin d → ℝ) :
    (Fin.insertNth (α := fun _ => ℝ) j (t + 1) θ' : Fin (d + 1) → ℝ) =
      Fin.insertNth (α := fun _ => ℝ) j t θ' + Pi.single j 1 := by
  ext ℓ
  rcases Fin.eq_self_or_eq_succAbove j ℓ with rfl | ⟨i', rfl⟩
  · simp [Fin.insertNth_apply_same]
  · simp [Fin.insertNth_apply_succAbove, Pi.single_apply, Fin.succAbove_ne]

/--
@isnad1 id=contdiff.0h2v.s8.4d12c57e03f3 from=translated src=- shape=8c8ecd9d vocab=acb54d74
-/
lemma contDiff_insertNth (j : Fin (d + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin d → ℝ) => (Fin.insertNth (α := fun _ => ℝ) j q.1 q.2 : Fin (d + 1) → ℝ)) := by
  rw [contDiff_pi]
  intro ℓ
  rcases Fin.eq_self_or_eq_succAbove j ℓ with rfl | ⟨i', rfl⟩
  · simp only [Fin.insertNth_apply_same]; exact contDiff_fst
  · simp only [Fin.insertNth_apply_succAbove]
    exact (contDiff_apply ℝ ℝ i').comp contDiff_snd

end PMDK6A
open scoped _root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_insertNth_mul_cexp_le_prod.PMDK6A

/--
@isnad1 id=ex.4h6v.s11.d76bab145cfa from=translated src=- shape=713b75cf vocab=0ee56015
-/
theorem solution
    {n d : ℕ} (W : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin (n + 1) → ℝ) × (Fin (d + 1) → ℝ)) (j : Fin (d + 1)), W (p.1, p.2 + Pi.single j 1) = W p)
    (j : Fin (d + 1)) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m' : Fin d → ℤ,
      let g : (Fin (n + 1) → ℝ) × ℝ → ℂ := fun p =>
        ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
          W (p.1, Fin.insertNth j p.2 θ') *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ k, R < |p.1 k|) → g p = 0) ∧
        (∀ p : (Fin (n + 1) → ℝ) × ℝ, g (p.1, p.2 + 1) = g p) ∧
        ∀ i : ℕ, i ≤ N → ∀ p : (Fin (n + 1) → ℝ) × ℝ,
          ‖iteratedFDeriv ℝ i g p‖ ≤ M * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by
  classical

  set V₀ : PMDK6A.P n × (Fin d → ℝ) → ℂ := fun q => W (q.1.1, Fin.insertNth j q.1.2 q.2) with hV₀
  have hVw : PMDK6A.IsWin R V₀ :=
    { smooth := by
        rw [hV₀]
        refine hW.comp (contDiff_fst.fst.prodMk ?_)
        exact (PMDK6A.contDiff_insertNth j).comp (contDiff_fst.snd.prodMk contDiff_snd)
      supp := fun q hq => hsupp _ hq
      per := fun q i => by
        simp only [hV₀]
        rw [PMDK6A.insertNth_add_single_succAbove]
        exact hper (q.1.1, Fin.insertNth j q.1.2 q.2) (j.succAbove i)
      pert := fun q => by
        simp only [hV₀]
        rw [PMDK6A.insertNth_add_one]
        exact hper (q.1.1, Fin.insertNth j q.1.2 q.2) j }
  obtain ⟨M₀, hM₀, hbd⟩ := PMDK6A.exists_uniform_bound hVw (N + 2 * d)
  refine ⟨M₀, hM₀, fun m' => ?_⟩
  have hΨ : (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      ∫ θ' in Set.pi Set.univ (fun _ : Fin d => Set.Ico (0 : ℝ) 1),
        W (p.1, Fin.insertNth j p.2 θ') *
          Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m' j' : ℝ) * θ' j' : ℝ) : ℂ)))) =
      PMDK6A.Ψ m' V₀ := rfl
  simp only []
  rw [hΨ]
  refine ⟨PMDK6A.contDiff_Ψ hVw m', ?_, ?_, ?_⟩
  · intro p hp
    show (∫ θ in PMDK6A.cube d, V₀ (p, θ) * PMDK6A.em m' θ) = 0
    have : ∀ θ, V₀ (p, θ) * PMDK6A.em m' θ = 0 := fun θ => by rw [hVw.supp (p, θ) hp, zero_mul]
    simp_rw [this]
    exact integral_zero _ _
  · intro p
    show (∫ θ in PMDK6A.cube d, V₀ ((p.1, p.2 + 1), θ) * PMDK6A.em m' θ) =
      ∫ θ in PMDK6A.cube d, V₀ (p, θ) * PMDK6A.em m' θ
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    beta_reduce
    rw [show V₀ ((p.1, p.2 + 1), θ) = V₀ (p, θ) from hVw.pert (p, θ)]
  · intro i hi p
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin d), S = Finset.univ.filter (fun j' => m' j' ≠ 0) := ⟨_, rfl⟩
    have hSm : ∀ j' ∈ S, m' j' ≠ 0 := fun j' hj => by
      rw [hS] at hj; exact (Finset.mem_filter.mp hj).2
    have hScard : 2 * S.card ≤ 2 * d := by
      have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin d)) (fun j' => m' j' ≠ 0)
      rw [Finset.card_univ, Fintype.card_fin, ← hS] at h1
      omega
    have hprod : ∏ j' ∈ S, ((2 * Real.pi * |(m' j' : ℝ)|) ^ 2)⁻¹ ≤ ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := by
      rw [← Finset.prod_subset (Finset.subset_univ S) (f := fun j' => (1 + |(m' j' : ℝ)|)⁻¹ ^ 2)]
      · apply Finset.prod_le_prod (fun j' _ => by positivity)
        intro j' hj
        have hmj : (1 : ℝ) ≤ |(m' j' : ℝ)| := by
          have := hSm j' hj
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs this
        rw [inv_pow]
        apply inv_anti₀ (by positivity)
        have hπ := Real.pi_gt_three
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      · intro j' _ hj
        have : m' j' = 0 := by
          by_contra h; exact hj (hS ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j', h⟩)
        simp [this]
    have hT0 : 0 ≤ ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 := Finset.prod_nonneg fun j' _ => by positivity
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro u
    rw [PMDK6A.iteratedFDeriv_Ψ_apply m' i V₀ hVw p u]
    have hU : PMDK6A.IsWin R (PMDK6A.DDX i u V₀) := hVw.DDX i u
    have hUb : ∀ i' : ℕ, i' ≤ 2 * d → ∀ q, ‖iteratedFDeriv ℝ i' (PMDK6A.DDX i u V₀) q‖ ≤ (∏ i, ‖u i‖) * M₀ := by
      intro i' hi' q
      refine (PMDK6A.norm_iteratedFDeriv_DDX_le i u hVw i' q).trans ?_
      exact mul_le_mul_of_nonneg_left (hbd (i' + i) (by omega) q) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have hdec := PMDK6A.decay m' p S hSm (2 * d) ((∏ i, ‖u i‖) * M₀) (PMDK6A.DDX i u V₀) hU hScard hUb
    calc ‖PMDK6A.Ψ m' (PMDK6A.DDX i u V₀) p‖ ≤ (∏ i, ‖u i‖) * M₀ * ∏ j' ∈ S, ((2 * Real.pi * |(m' j' : ℝ)|) ^ 2)⁻¹ := hdec
      _ ≤ (∏ i, ‖u i‖) * M₀ * ∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = M₀ * (∏ j', (1 + |(m' j' : ℝ)|)⁻¹ ^ 2) * ∏ i, ‖u i‖ := by ring
