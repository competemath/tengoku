import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real Filter Set
open scoped Topology

noncomputable section

namespace GL2RealPoissonJumpTerm

section matrix2

variable {X : Type*}

/--
@isnad1 id=continuo.4h5v.s9.f1c2b8ff61ed from=translated src=- shape=553a7e07 vocab=ce0c76d1
-/
theorem continuous_matrix2 [TopologicalSpace X] {a b c d : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous fun x => Matrix.of.symm !![a x, b x; c x, d x] := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa

/--
@isnad1 id=continuo.4h6v.s9.c89d09f849a7 from=translated src=- shape=7e2bc046 vocab=63a3e9ef
-/
theorem continuousOn_matrix2 [TopologicalSpace X] {a b c d : X → ℝ} {s : Set X}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) (hc : ContinuousOn c s)
    (hd : ContinuousOn d s) :
    ContinuousOn (fun x => Matrix.of.symm !![a x, b x; c x, d x]) s := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa

/--
@isnad1 id=hasderiv.4h9v.s10.c2b036d2b6c0 from=translated src=- shape=da928ed5 vocab=29b768fc
-/
theorem hasDerivAt_matrix2 {a b c d : ℝ → ℝ} {a' b' c' d' x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) (hc : HasDerivAt c c' x)
    (hd : HasDerivAt d d' x) :
    HasDerivAt (fun x => Matrix.of.symm !![a x, b x; c x, d x])
      (Matrix.of.symm !![a', b'; c', d']) x := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa

/--
@isnad1 id=le.0h3v.s7.6458b4478ea8 from=translated src=- shape=fca4af93 vocab=5b1e3859
-/
theorem abs_apply_le_norm (M : Fin 2 → Fin 2 → ℝ) (i j : Fin 2) : |M i j| ≤ ‖M‖ :=
  (Real.norm_eq_abs _ ▸ norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)

end matrix2

section setup

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) (r : ℝ)

def F : (Fin 2 → Fin 2 → ℝ) → ℂ := fun M => Φ (M, p)

def e10 : Fin 2 → Fin 2 → ℝ := Matrix.of.symm !![0, 0; 1, 0]

def D (M : Fin 2 → Fin 2 → ℝ) : ℂ := fderiv ℝ (F Φ p) M e10

def Mp (θ : ℝ) (q : ℝ × ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
    -(r * q.1), r * (Real.cos θ + q.2)]

def Mm (θ : ℝ) (q : ℝ × ℝ) : Fin 2 → Fin 2 → ℝ :=
  Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
    r * q.1, r * (Real.cos θ - q.2)]

def I (θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) * (D Φ p (Mp r θ q) - D Φ p (Mm r θ q))

def J (θ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (((1 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
    (D Φ p (Mp r θ (q.1, Real.sin θ * q.2)) - D Φ p (Mm r θ (q.1, Real.sin θ * q.2)))

def A (u : ℝ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm !![r, 0; -(r * u), r]

def B (u : ℝ) : Fin 2 → Fin 2 → ℝ := Matrix.of.symm !![r, 0; r * u, r]

def J0 (q : ℝ × ℝ) : ℂ :=
  (((1 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) * (D Φ p (A r q.1) - D Φ p (B r q.1))

omit [NormedSpace ℝ P] in

/--
@isnad1 id=ex.1h2v.s8.4d24378628e2 from=translated src=- shape=3ddd3e6e vocab=da2baecc
-/
theorem exists_radius (hΦc : HasCompactSupport Φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (M : Fin 2 → Fin 2 → ℝ) (p' : P), Φ (M, p') ≠ 0 → ‖M‖ ≤ R := by
  obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.exists_norm_le
  refine ⟨max R 0, le_max_right _ _, fun M p' h => ?_⟩
  have hmem : (M, p') ∈ tsupport Φ := subset_tsupport _ h
  exact (norm_fst_le (M, p')).trans ((hR _ hmem).trans (le_max_left _ _))

/--
@isnad1 id=contdiff.1h3v.s9.9b6aadcdaabe from=translated src=- shape=8f59623d vocab=651355e6
-/
theorem contDiff_F (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) : ContDiff ℝ (⊤ : ℕ∞) (F Φ p) :=
  hΦs.comp (contDiff_prodMk_left p)

/--
@isnad1 id=hasfderi.1h4v.s9.050e6509cb21 from=translated src=- shape=7fb5e632 vocab=20058d9f
-/
theorem hasFDerivAt_F (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : Fin 2 → Fin 2 → ℝ) :
    HasFDerivAt (F Φ p) (fderiv ℝ (F Φ p) M) M :=
  ((contDiff_F Φ p hΦs).differentiable (by simp) M).hasFDerivAt

/--
@isnad1 id=continuo.1h3v.s8.2d1fdd8a3d0a from=translated src=- shape=bbf589d8 vocab=f38cbfe2
-/
theorem continuous_D (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) : Continuous (D Φ p) :=
  ((contDiff_F Φ p hΦs).continuous_fderiv (by simp)).clm_apply continuous_const

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

/--
@isnad1 id=eq.2h5v.s8.659dc01b7116 from=translated src=- shape=f6a927a6 vocab=81845e91
-/
theorem F_eq_zero {R : ℝ} (hR : ∀ (M : Fin 2 → Fin 2 → ℝ) (p' : P), Φ (M, p') ≠ 0 → ‖M‖ ≤ R)
    {M : Fin 2 → Fin 2 → ℝ} (hM : R < ‖M‖) : F Φ p M = 0 := by
  by_contra h
  exact absurd hM (not_lt.2 (hR M p h))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

/--
@isnad1 id=eq.2h5v.s10.1b5d43c88458 from=translated src=- shape=3b994e2a vocab=d923ee0e
-/
theorem fderiv_F_eq_zero {R : ℝ} (hR : ∀ (M : Fin 2 → Fin 2 → ℝ) (p' : P), Φ (M, p') ≠ 0 → ‖M‖ ≤ R)
    {M : Fin 2 → Fin 2 → ℝ} (hM : R < ‖M‖) : fderiv ℝ (F Φ p) M = 0 := by
  have h : F Φ p =ᶠ[𝓝 M] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hM] with M' hM'
    exact F_eq_zero Φ p hR hM'
  rw [h.fderiv_eq]
  simp

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/--
@isnad1 id=eq.2h5v.s8.fab3471d1cfb from=translated src=- shape=f6a927a6 vocab=ad27a7f7
-/
theorem D_eq_zero {R : ℝ} (hR : ∀ (M : Fin 2 → Fin 2 → ℝ) (p' : P), Φ (M, p') ≠ 0 → ‖M‖ ≤ R)
    {M : Fin 2 → Fin 2 → ℝ} (hM : R < ‖M‖) : D Φ p M = 0 := by
  simp [D, fderiv_F_eq_zero Φ p hR hM]

/--
@isnad1 id=ex.2h4v.s9.729ad5f27e1b from=translated src=- shape=213b10e7 vocab=8edb59c2
-/
theorem exists_bound_D (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) {R : ℝ}
    (hR : ∀ (M : Fin 2 → Fin 2 → ℝ) (p' : P), Φ (M, p') ≠ 0 → ‖M‖ ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M, ‖D Φ p M‖ ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin 2 → Fin 2 → ℝ) R).exists_bound_of_continuousOn
    (continuous_D Φ p hΦs).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun M => ?_⟩
  by_cases hM : ‖M‖ ≤ R
  · exact (hC M (mem_closedBall_zero_iff.2 hM)).trans (le_max_left _ _)
  · rw [D_eq_zero Φ p hR (not_le.1 hM), norm_zero]
    exact le_max_right _ _

/--
@isnad1 id=lt.3h4v.s7.fbf0de637d03 from=translated src=- shape=8a3a4e1d vocab=d6ddceda
-/
theorem lt_norm_Mp (hr : 0 < r) {R θ : ℝ} {q : ℝ × ℝ} (hq : 0 < q.1) (h : R < r * q.1) :
    R < ‖Mp r θ q‖ := by
  refine h.trans_le ?_
  have := abs_apply_le_norm (Mp r θ q) 1 0
  simpa [Mp, abs_of_pos hr, abs_of_pos hq] using this

/--
@isnad1 id=lt.3h4v.s7.4c76b1fb9858 from=translated src=- shape=8a3a4e1d vocab=f3c15259
-/
theorem lt_norm_Mm (hr : 0 < r) {R θ : ℝ} {q : ℝ × ℝ} (hq : 0 < q.1) (h : R < r * q.1) :
    R < ‖Mm r θ q‖ := by
  refine h.trans_le ?_
  have := abs_apply_le_norm (Mm r θ q) 1 0
  simpa [Mm, abs_of_pos hr, abs_of_pos hq] using this

/--
@isnad1 id=lt.2h3v.s7.30e64111a2e9 from=translated src=- shape=55fec39f vocab=108c35b5
-/
theorem lt_norm_A (hr : 0 < r) {R u : ℝ} (h : R < r * |u|) : R < ‖A r u‖ := by
  refine h.trans_le ?_
  have := abs_apply_le_norm (A r u) 1 0
  simpa [A, abs_mul, abs_of_pos hr] using this

/--
@isnad1 id=lt.2h3v.s7.15ceef40bf3a from=translated src=- shape=55fec39f vocab=12dd0b49
-/
theorem lt_norm_B (hr : 0 < r) {R u : ℝ} (h : R < r * |u|) : R < ‖B r u‖ := by
  refine h.trans_le ?_
  have := abs_apply_le_norm (B r u) 1 0
  simpa [B, abs_mul, abs_of_pos hr] using this

/--
@isnad1 id=eq.0h1v.s8.88819ba84050 from=translated src=- shape=494a08d9 vocab=a47e03b9
-/
theorem A_zero : A r 0 = Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A]

/--
@isnad1 id=eq.0h1v.s8.bfda8124366a from=translated src=- shape=494a08d9 vocab=3b0211c5
-/
theorem B_zero : B r 0 = Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B]

/--
@isnad1 id=eq.0h0v.s6.5ea4f136a166 from=translated src=- shape=a8232a1f vocab=201a0005
-/
theorem volume_restrict_eq_prod :
    (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) =
      ((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure ℝ) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/--
@isnad1 id=measurab.0h0v.s5.d98d33ce69d1 from=translated src=- shape=c0c6bfbd vocab=92ab4997
-/
theorem measurableSet_S : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :=
  measurableSet_Ioi.prod MeasurableSet.univ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/--
@isnad1 id=eq.1h5v.s7.a6da0df8a94e from=translated src=- shape=1df55693 vocab=8baea361
-/
theorem sin_mul_integral_I (θ : ℝ) (hθ : 0 < Real.sin θ) :
    (Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), I Φ p r θ q =
      ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), J Φ p r θ q := by
  set ν : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))
    with hν
  have hs0 : Real.sin θ ≠ 0 := hθ.ne'
  have hφ : MeasurableEmbedding (Prod.map (@id ℝ) fun w : ℝ => Real.sin θ * w) :=
    MeasurableEmbedding.id.prodMap (measurableEmbedding_mulLeft₀ hs0)
  have hmap : Measure.map (Prod.map (@id ℝ) fun w : ℝ => Real.sin θ * w) ν =
      ENNReal.ofReal |(Real.sin θ)⁻¹| • ν := by
    rw [hν, volume_restrict_eq_prod,
      ← Measure.map_prod_map ((volume : Measure ℝ).restrict (Ioi 0)) (volume : Measure ℝ)
        measurable_id (measurable_const_mul (Real.sin θ)),
      Measure.map_id, Real.map_volume_mul_left hs0, Measure.prod_smul_right]
  have h1 : ∫ q, I Φ p r θ (Prod.map (@id ℝ) (fun w : ℝ => Real.sin θ * w) q) ∂ν =
      (((Real.sin θ)⁻¹ : ℝ) : ℂ) * ∫ q, I Φ p r θ q ∂ν := by
    rw [← hφ.integral_map, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.2 hθ), Complex.real_smul]
  have h2 : ∀ q : ℝ × ℝ, I Φ p r θ (Prod.map (@id ℝ) (fun w : ℝ => Real.sin θ * w) q) =
      (((Real.sin θ ^ 2)⁻¹ : ℝ) : ℂ) * J Φ p r θ q := by
    intro q
    have hq : (Real.sin θ ^ 2 + (Real.sin θ * q.2) ^ 2)⁻¹ =
        (Real.sin θ ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹ := by
      rw [← mul_inv, mul_add, mul_one, mul_pow]
    rw [I, J]
    dsimp only [Prod.map, id]
    rw [hq]
    push_cast
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsC' : Complex.sin (θ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sin]; exact hsC
  calc (Real.sin θ : ℂ) * ∫ q, I Φ p r θ q ∂ν
        = (Real.sin θ : ℂ) ^ 2 * ((((Real.sin θ)⁻¹ : ℝ) : ℂ) * ∫ q, I Φ p r θ q ∂ν) := by
        push_cast; field_simp
    _ = (Real.sin θ : ℂ) ^ 2 * ((((Real.sin θ ^ 2)⁻¹ : ℝ) : ℂ) * ∫ q, J Φ p r θ q ∂ν) := by rw [h1]
    _ = ∫ q, J Φ p r θ q ∂ν := by push_cast; field_simp

/--
@isnad1 id=eq.3h4v.s9.dc90ee0d5fcf from=translated src=- shape=179b9aa5 vocab=6f664626
-/
theorem integral_Ioi_D_sub_D (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (hr : 0 < r) :
    ∫ u in Ioi (0 : ℝ), (D Φ p (A r u) - D Φ p (B r u)) =
      ((2 / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p) := by
  obtain ⟨R, hR0, hR⟩ := exists_radius Φ hΦc

  set f : ℝ → ℂ := fun u => (-(r : ℂ))⁻¹ * (F Φ p (A r u) + F Φ p (B r u)) with hf
  have hA : ∀ u, HasDerivAt (A r) (Matrix.of.symm !![0, 0; -r, 0]) u := fun u => by
    have h3 : HasDerivAt (fun x : ℝ => -(r * x)) (-r) u := by
      have h__af := ((hasDerivAt_id u).const_mul r).neg
      simp at h__af
      exact h__af
    have h__af := (hasDerivAt_matrix2 (hasDerivAt_const u r) (hasDerivAt_const u (0 : ℝ)) h3
      (hasDerivAt_const u r))
    simp [A] at h__af
    exact h__af
  have hB : ∀ u, HasDerivAt (B r) (Matrix.of.symm !![0, 0; r, 0]) u := fun u => by
    have h3 : HasDerivAt (fun x : ℝ => r * x) r u := by
      simpa using (hasDerivAt_id u).const_mul r
    have h__af := (hasDerivAt_matrix2 (hasDerivAt_const u r) (hasDerivAt_const u (0 : ℝ)) h3
      (hasDerivAt_const u r))
    simp [B] at h__af
    exact h__af
  have hAe : Matrix.of.symm !![(0 : ℝ), 0; -r, 0] = (-r) • e10 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10]
  have hBe : Matrix.of.symm !![(0 : ℝ), 0; r, 0] = r • e10 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10]
  have hderiv : ∀ u, HasDerivAt f (D Φ p (A r u) - D Φ p (B r u)) u := by
    intro u
    have h1 := (hasFDerivAt_F Φ p hΦs (A r u)).comp_hasDerivAt u (hA u)
    have h2 := (hasFDerivAt_F Φ p hΦs (B r u)).comp_hasDerivAt u (hB u)
    rw [hAe, ContinuousLinearMap.map_smul] at h1
    rw [hBe, ContinuousLinearMap.map_smul] at h2
    have h12 := (h1.add h2).const_mul (-(r : ℂ))⁻¹
    convert h12 using 1 <;> try rfl
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp only [Complex.real_smul, neg_smul, smul_eq_mul, D]
    field_simp
    ring

  have hcont : Continuous fun u => D Φ p (A r u) - D Φ p (B r u) := by
    have hD := continuous_D Φ p hΦs
    have hAc : Continuous (A r) := by
      unfold A; exact continuous_matrix2 continuous_const continuous_const (by fun_prop) continuous_const
    have hBc : Continuous (B r) := by
      unfold B; exact continuous_matrix2 continuous_const continuous_const (by fun_prop) continuous_const
    exact (hD.comp hAc).sub (hD.comp hBc)
  have hsupp : HasCompactSupport fun u => D Φ p (A r u) - D Φ p (B r u) := by
    refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-(R / r)) (R / r))) fun u hu => ?_
    have hu' : R / r < |u| := by
      simp only [mem_Icc, not_and_or, not_le] at hu
      rcases hu with hu | hu
      · exact (by linarith : R / r < -u).trans_le (neg_le_abs u)
      · exact hu.trans_le (le_abs_self u)
    have hRu : R < r * |u| := by rwa [div_lt_iff₀ hr, mul_comm] at hu'
    simp [D_eq_zero Φ p hR (lt_norm_A r hr hRu), D_eq_zero Φ p hR (lt_norm_B r hr hRu)]
  have hint : IntegrableOn (fun u => D Φ p (A r u) - D Φ p (B r u)) (Ioi 0) :=
    (hcont.integrable_of_hasCompactSupport hsupp).integrableOn

  have hlim : Tendsto f atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (R / r)] with u hu
    have hu0 : 0 < u := lt_of_le_of_lt (div_nonneg hR0 hr.le) hu
    have hRu : R < r * |u| := by rwa [abs_of_pos hu0, mul_comm, ← div_lt_iff₀ hr]
    simp [hf, F_eq_zero Φ p hR (lt_norm_A r hr hRu), F_eq_zero Φ p hR (lt_norm_B r hr hRu)]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hderiv u) hint hlim]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [hf, A_zero, B_zero, F]
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.3h4v.s9.4467b13fcec1 from=translated src=- shape=ee3472a4 vocab=76c221af
-/
theorem integral_J0 (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (hr : 0 < r) :
    ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), J0 Φ p r q =
      ((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p) := by
  rw [volume_restrict_eq_prod]
  have hJ0 : (J0 Φ p r) = fun q : ℝ × ℝ =>
      (D Φ p (A r q.1) - D Φ p (B r q.1)) * ((((1 + q.2 ^ 2)⁻¹ : ℝ) : ℂ)) := by
    funext q
    simp only [J0]
    ring
  rw [hJ0, integral_prod_mul (μ := (volume : Measure ℝ).restrict (Ioi 0)) (ν := (volume : Measure ℝ))
    (fun u : ℝ => D Φ p (A r u) - D Φ p (B r u)) (fun w : ℝ => (((1 + w ^ 2)⁻¹ : ℝ) : ℂ)),
    integral_complex_ofReal, integral_univ_inv_one_add_sq, integral_Ioi_D_sub_D Φ p r hΦs hΦc hr]
  push_cast
  ring

/--
@isnad1 id=tendsto.3h4v.s9.2c458dff670e from=translated src=- shape=de6caab1 vocab=08e49f0a
-/
theorem tendsto_integral_J (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (hr : 0 < r) :
    Tendsto (fun θ => ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), J Φ p r θ q) (𝓝[>] 0)
      (𝓝 (∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), J0 Φ p r q)) := by
  obtain ⟨R, hR0, hR⟩ := exists_radius Φ hΦc
  obtain ⟨K, hK0, hK⟩ := exists_bound_D Φ p hΦs hR
  have hD := continuous_D Φ p hΦs
  refine tendsto_integral_filter_of_dominated_convergence
    (fun q => indicator (Iic (R / r)) (fun _ => 2 * K) q.1 * (1 + q.2 ^ 2)⁻¹) ?_ ?_ ?_ ?_
  ·
    refine Eventually.of_forall fun θ => ContinuousOn.aestronglyMeasurable ?_ measurableSet_S
    have hden : ContinuousOn
        (fun q : ℝ × ℝ => (Real.sin θ ^ 2 + (Real.sin θ * q.2) ^ 2) / q.1) (Ioi (0 : ℝ) ×ˢ univ) :=
      ContinuousOn.div (by fun_prop) continuousOn_fst fun q hq => (ne_of_gt hq.1)
    have hMp : ContinuousOn (fun q : ℝ × ℝ => Mp r θ (q.1, Real.sin θ * q.2)) (Ioi (0 : ℝ) ×ˢ univ) := by
      unfold Mp
      exact continuousOn_matrix2 (by fun_prop) (continuousOn_const.mul hden) (by fun_prop) (by fun_prop)
    have hMm : ContinuousOn (fun q : ℝ × ℝ => Mm r θ (q.1, Real.sin θ * q.2)) (Ioi (0 : ℝ) ×ˢ univ) := by
      unfold Mm
      exact continuousOn_matrix2 (by fun_prop) (continuousOn_const.mul hden).neg (by fun_prop)
        (by fun_prop)
    have hw : Continuous fun q : ℝ × ℝ => (1 + q.2 ^ 2)⁻¹ :=
      (continuous_const.add (continuous_snd.pow 2)).inv₀ fun q =>
        (by positivity : (0 : ℝ) < 1 + q.2 ^ 2).ne'
    unfold J
    exact (Complex.continuous_ofReal.comp_continuousOn hw.continuousOn).mul
      ((hD.comp_continuousOn hMp).sub (hD.comp_continuousOn hMm))
  ·
    refine Eventually.of_forall fun θ => (ae_restrict_iff' measurableSet_S).2
      (Eventually.of_forall fun q hq => ?_)
    obtain ⟨u, w⟩ := q
    dsimp only
    have hu : 0 < u := hq.1
    have hw : 0 < 1 + w ^ 2 := by positivity
    have hnorm : ‖(((1 + w ^ 2)⁻¹ : ℝ) : ℂ)‖ = (1 + w ^ 2)⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hw.le)]
    by_cases hu' : u ≤ R / r
    · rw [J, norm_mul, hnorm, indicator_of_mem (show u ∈ Iic (R / r) from hu'), mul_comm]
      gcongr
      have hK1 := hK (Mp r θ (u, Real.sin θ * w))
      have hK2 := hK (Mm r θ (u, Real.sin θ * w))
      exact (norm_sub_le _ _).trans (by linarith)
    · have hlt : R < r * u := by
        rw [not_le, div_lt_iff₀ hr, mul_comm] at hu'
        exact hu'
      have h1 : D Φ p (Mp r θ (u, Real.sin θ * w)) = 0 :=
        D_eq_zero Φ p hR (lt_norm_Mp r hr (q := (u, Real.sin θ * w)) hu hlt)
      have h2 : D Φ p (Mm r θ (u, Real.sin θ * w)) = 0 :=
        D_eq_zero Φ p hR (lt_norm_Mm r hr (q := (u, Real.sin θ * w)) hu hlt)
      simp [J, h1, h2, indicator_of_notMem (show u ∉ Iic (R / r) from hu')]
  ·
    rw [volume_restrict_eq_prod]
    refine Integrable.mul_prod (f := fun u : ℝ => indicator (Iic (R / r)) (fun _ => 2 * K) u)
      (g := fun w : ℝ => (1 + w ^ 2)⁻¹) ?_ integrable_inv_one_add_sq
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iic]
    exact ne_top_of_le_ne_top (measure_Icc_lt_top (a := (0 : ℝ)) (b := R / r)).ne
      (measure_mono fun x hx => ⟨hx.2.le, hx.1⟩)
  ·
    refine Eventually.of_forall fun q => ?_
    have hb : Continuous fun θ : ℝ =>
        (Real.sin θ ^ 2 + (q.1, Real.sin θ * q.2).2 ^ 2) / (q.1, Real.sin θ * q.2).1 :=
      ((Real.continuous_sin.pow 2).add ((Real.continuous_sin.mul continuous_const).pow 2)).div_const _
    have h1 : Tendsto (fun θ => Mp r θ (q.1, Real.sin θ * q.2)) (𝓝[>] 0) (𝓝 (A r q.1)) := by
      have hc : Continuous fun θ => Mp r θ (q.1, Real.sin θ * q.2) := by
        unfold Mp
        exact continuous_matrix2 (by fun_prop) (continuous_const.mul hb) (by fun_prop) (by fun_prop)
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert this using 2
      simp [Mp, A]
    have h2 : Tendsto (fun θ => Mm r θ (q.1, Real.sin θ * q.2)) (𝓝[>] 0) (𝓝 (B r q.1)) := by
      have hc : Continuous fun θ => Mm r θ (q.1, Real.sin θ * q.2) := by
        unfold Mm
        exact continuous_matrix2 (by fun_prop) (continuous_const.mul hb).neg (by fun_prop)
          (by fun_prop)
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      convert this using 2
      simp [Mm, B]
    exact tendsto_const_nhds.mul
      ((hD.continuousAt.tendsto.comp h1).sub (hD.continuousAt.tendsto.comp h2))

/--
@isnad1 id=tendsto.3h4v.s10.5e0653533ae4 from=translated src=- shape=8acdb572 vocab=627a666a
-/
theorem main (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (hr : 0 < r) :
    Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), I Φ p r θ q)
      (𝓝[>] 0) (𝓝 (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p))) := by
  rw [← integral_J0 Φ p r hΦs hΦc hr]
  refine (tendsto_integral_J Φ p r hΦs hΦc hr).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with θ hθ
  exact (sin_mul_integral_I Φ p r θ (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)).symm

end setup

end GL2RealPoissonJumpTerm

end

/--
@isnad1 id=tendsto.3h4v.s12.769e25c1efe9 from=translated src=- shape=9d26ac4a vocab=7e209aa3
-/
theorem solution
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
          (fderiv ℝ (fun M => Φ (M, p))
              (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
                -(r * q.1), r * (Real.cos θ + q.2)])
              (Matrix.of.symm !![0, 0; 1, 0]) -
            fderiv ℝ (fun M => Φ (M, p))
              (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
                r * q.1, r * (Real.cos θ - q.2)])
              (Matrix.of.symm !![0, 0; 1, 0])))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p))) :=
  GL2RealPoissonJumpTerm.main Φ p r hΦs hΦc hr
