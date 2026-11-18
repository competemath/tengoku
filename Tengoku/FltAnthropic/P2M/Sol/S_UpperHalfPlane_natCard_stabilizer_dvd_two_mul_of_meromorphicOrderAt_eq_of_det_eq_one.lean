import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one

set_option autoImplicit false

noncomputable section

open _root_.Filter open _root_.UpperHalfPlane
open scoped MatrixGroups Topology

namespace UpperHalfPlane
export _root_.UpperHalfPlane (continuous_im ofComplex_apply_of_im_pos denom_ne_zero denom denom_ne_zero_of_im denom_cocycle coe_re ofComplex_apply im_pos coe_smul_of_det_pos isEmbedding_coe im num eventuallyEq_coe_comp_ofComplex im_ne_zero ofComplex coe_im)
namespace EllipticOrderGL
open _root_.UpperHalfPlane

/--
@isnad1 id=lt.1h1v.s9.ce0555f10f73 from=translated src=- shape=3de38c0a vocab=e296b66f
-/
theorem det_val_pos {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) : 0 < g.det.val := by
  rw [hg]; exact one_pos

/--
@isnad1 id=eq.1h1v.s8.c302084270ba from=translated src=- shape=ff4caa72 vocab=3101a4d3
-/
theorem val_det_eq_one {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) : g.val.det = 1 := by
  have := congrArg Units.val hg
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using this

/--
@isnad1 id=eq.1h2v.s9.6428e7dff42b from=translated src=- shape=2af1f51d vocab=83310b2a
-/
theorem coe_smul_eq {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = num g z / denom g z :=
  coe_smul_of_det_pos (det_val_pos hg) z

/--
@isnad1 id=eq.2h3v.s9.b586d3e7187d from=translated src=- shape=5252c76c vocab=e5aad060
-/
theorem denom_mul_of_smul_eq (γ δ : GL (Fin 2) ℝ) (hδ1 : Matrix.GeneralLinearGroup.det δ = 1)
    (τ : ℍ) (hδ : δ • τ = τ) :
    denom (γ * δ) τ = denom γ τ * denom δ τ := by
  have h := denom_cocycle γ δ τ.im_ne_zero
  have h2 : ((δ • τ : ℍ) : ℂ) = num δ τ / denom δ τ := coe_smul_eq hδ1 τ
  rw [← h2, hδ] at h
  exact h

/--
@isnad1 id=and.1h5v.s5.e8dbeb74050e from=translated src=- shape=2bf321ee vocab=49345d23
-/
theorem bottom_row_eq {c d c' d' : ℝ} (τ : ℍ)
    (h : (c : ℂ) * τ + d = (c' : ℂ) * τ + d') : c = c' ∧ d = d' := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] at him
  have hc : c = c' := mul_right_cancel₀ τ.im_pos.ne' him
  subst hc
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

def chi (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (τ : ℍ) :
    MulAction.stabilizer Γ τ →* ℂ where
  toFun γ := denom ((γ : Γ) : GL (Fin 2) ℝ) τ
  map_one' := by simp [denom]
  map_mul' γ δ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, denom_mul_of_smul_eq _ _ (hdet _ (δ : Γ).2) _ δ.2]

/--
@isnad1 id=eq.1h3v.s15.b44265230290 from=translated src=- shape=68ea6f66 vocab=c12a7401
-/
theorem chi_apply (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ : ℍ) (γ : MulAction.stabilizer Γ τ) :
    chi Γ hdet τ γ = denom ((γ : Γ) : GL (Fin 2) ℝ) τ := rfl

theorem eq_one_of_denom_eq_one (τ : ℍ) (γ : GL (Fin 2) ℝ) (hγ1 : Matrix.GeneralLinearGroup.det γ = 1)
    (hγ : γ • τ = τ) (h1 : denom γ τ = 1) : γ = 1 := by
  have hrow : γ 1 0 = 0 ∧ γ 1 1 = 1 := by
    have := bottom_row_eq (c := γ 1 0) (d := γ 1 1) (c' := 0) (d' := 1) τ
      (by rw [denom] at h1; push_cast; simpa using h1)
    exact this
  have hdet := val_det_eq_one hγ1
  rw [Matrix.det_fin_two] at hdet
  have h00 : γ 0 0 = 1 := by
    have : γ.val 1 0 = 0 := hrow.1
    have : γ.val 1 1 = 1 := hrow.2
    simp only [*, mul_one, mul_zero, sub_zero] at hdet
    exact hdet
  have hfix := congrArg (fun z : ℍ => (z : ℂ)) hγ
  simp only [coe_smul_eq hγ1, num, denom] at hfix
  rw [hrow.1, hrow.2, h00] at hfix
  simp only [Complex.ofReal_zero, zero_mul, Complex.ofReal_one, zero_add, div_one, one_mul] at hfix
  have h01 : ((γ 0 1 : ℝ) : ℂ) = 0 := by
    have h'' := add_left_cancel (hfix.trans (add_zero (τ : ℂ)).symm)
    exact h''
  have h01' : γ 0 1 = 0 := by exact_mod_cast h01
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hrow.1, hrow.2, h00, h01']

/--
@isnad1 id=injectiv.1h2v.s15.bcbfc7121a80 from=translated src=- shape=f5cad73c vocab=e067ecc6
-/
theorem chi_injective (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ : ℍ) : Function.Injective (chi Γ hdet τ) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [MonoidHom.mem_ker, chi_apply] at hγ
  have hfix : ((γ : Γ) : GL (Fin 2) ℝ) • τ = τ := γ.2
  exact Subtype.ext (Subtype.ext (eq_one_of_denom_eq_one τ _ (hdet _ (γ : Γ).2) hfix hγ))

/--
@isnad1 id=dvd.2h3v.s15.1fe3219baaf0 from=translated src=- shape=37fd6371 vocab=109cd6d2
-/
theorem card_dvd_of_forall_chi_zpow_eq_one (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (τ : ℍ) (n : ℤ)
    (h : ∀ γ : MulAction.stabilizer Γ τ, chi Γ hdet τ γ ^ (2 * n) = 1) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  classical
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, mul_zero]; exact dvd_zero _
  set k : ℕ := (2 * n).natAbs with hk
  have hk0 : 0 < k := Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero hn0)
  have hpow : ∀ γ : MulAction.stabilizer Γ τ, chi Γ hdet τ γ ^ k = 1 := by
    intro γ
    have h1 := h γ
    rcases Int.natAbs_eq (2 * n) with h2 | h2
    · rw [h2, zpow_natCast] at h1; exact h1
    · rw [h2, zpow_neg, zpow_natCast, inv_eq_one] at h1; exact h1

  haveI : Finite (MulAction.stabilizer Γ τ) := by
    refine Finite.of_injective
      (fun γ => (⟨chi Γ hdet τ γ, (Polynomial.mem_nthRootsFinset hk0 (1 : ℂ)).mpr (hpow γ)⟩ :
        ↥(Polynomial.nthRootsFinset k (1 : ℂ)))) ?_
    intro γ δ hγδ
    exact chi_injective Γ hdet τ (congrArg Subtype.val hγδ)
  haveI := isCyclic_of_injective_ringHom (chi Γ hdet τ) (chi_injective Γ hdet τ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := MulAction.stabilizer Γ τ)
  rw [← hg]
  have hdvd : orderOf g ∣ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply chi_injective Γ hdet τ
    rw [map_pow, map_one]
    exact hpow g
  rcases Int.natAbs_eq (2 * n) with h2 | h2
  · rw [h2]; exact Int.natCast_dvd_natCast.mpr hdvd
  · rw [h2]; exact (Int.natCast_dvd_natCast.mpr hdvd).neg_right

/--
@isnad1 id=eq.0h3v.s7.1b80689e58f8 from=translated src=- shape=2b361272 vocab=80e331cb
-/
theorem num_mul_denom_sub (g : GL (Fin 2) ℝ) (z w : ℂ) :
    num g z * denom g w - denom g z * num g w = (g.val.det : ℝ) * (z - w) := by
  simp only [num, denom, Matrix.det_fin_two]
  push_cast
  ring

def moeb (γ : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num γ z / denom γ z

/--
@isnad1 id=eq.1h2v.s9.c82f8fbdac87 from=translated src=- shape=6a730cb8 vocab=58f45e52
-/
theorem coe_smul_eq_moeb {γ : GL (Fin 2) ℝ} (hγ1 : Matrix.GeneralLinearGroup.det γ = 1) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = moeb γ z := coe_smul_eq hγ1 z

/--
@isnad1 id=eq.3h3v.s9.550e54cbfa17 from=translated src=- shape=77cfbcfa vocab=235ba8d3
-/
theorem moeb_sub {γ : GL (Fin 2) ℝ} (hγ1 : Matrix.GeneralLinearGroup.det γ = 1) (τ : ℍ) (hγ : γ • τ = τ)
    (z : ℂ) (hz : denom γ z ≠ 0) :
    moeb γ z - τ = (z - τ) / (denom γ z * denom γ τ) := by
  have hτ : (τ : ℂ) = moeb γ τ := by rw [← coe_smul_eq_moeb hγ1, hγ]
  conv_lhs => rw [hτ]
  simp only [moeb]
  rw [div_sub_div _ _ hz (denom_ne_zero _ τ), num_mul_denom_sub, val_det_eq_one hγ1]
  push_cast
  ring

/--
@isnad1 id=continuo.0h1v.s5.4df7fbb860cf from=translated src=- shape=cd1263fd vocab=101b6c81
-/
theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) :=
  (continuous_const.mul continuous_id).add continuous_const

/--
@isnad1 id=continuo.0h1v.s5.d017856929ea from=translated src=- shape=cd1263fd vocab=12e2065a
-/
theorem continuous_num (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => num g z) :=
  (continuous_const.mul continuous_id).add continuous_const

/--
@isnad1 id=continuo.0h2v.s5.aa546ff4fddf from=translated src=- shape=ea375387 vocab=8ac86956
-/
theorem continuousAt_moeb (γ : GL (Fin 2) ℝ) (τ : ℍ) : ContinuousAt (moeb γ) τ :=
  ContinuousAt.div (continuous_num γ).continuousAt (continuous_denom γ).continuousAt (denom_ne_zero _ τ)

/--
@isnad1 id=tendsto.0h1v.s6.5394e48ff7b1 from=translated src=- shape=3a7fe0da vocab=af7c69a3
-/
theorem tendsto_ofComplex (τ : ℍ) : Tendsto (fun z : ℂ => ofComplex z) (𝓝[≠] (τ : ℂ)) (𝓝[≠] τ) := by
  have h1 : Tendsto (fun z : ℂ => ofComplex z) (𝓝 (τ : ℂ)) (𝓝 τ) := by
    rw [isEmbedding_coe.isInducing.tendsto_nhds_iff]
    exact (tendsto_id.congr' (eventuallyEq_coe_comp_ofComplex τ.im_pos).symm)
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h1.mono_left nhdsWithin_le_nhds, ?_⟩
  have him : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)
  filter_upwards [him, self_mem_nhdsWithin] with z hz hne
  intro (habs : ofComplex z = τ)
  apply hne
  have := congrArg (fun w : ℍ => (w : ℂ)) habs
  rwa [ofComplex_apply_of_im_pos hz] at this

/--
@isnad1 id=eq.5h6v.s15.8b19aa73d417 from=translated src=- shape=a5549e91 vocab=2866d74e
-/
theorem chi_zpow_eq_one (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z) (n : ℤ)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g τ) (hg0 : g τ ≠ 0)
    (hfg : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (ofComplex z) = (z - τ) ^ n • g z)
    (γ : MulAction.stabilizer Γ τ) :
    chi Γ hdet τ γ ^ (2 * n) = 1 := by
  set γ₀ : GL (Fin 2) ℝ := ((γ : Γ) : GL (Fin 2) ℝ) with hγ₀
  have hγ₀1 : Matrix.GeneralLinearGroup.det γ₀ = 1 := hdet _ (γ : Γ).2
  have hfix : γ₀ • τ = τ := γ.2
  set d : ℂ → ℂ := fun z => denom γ₀ z with hd
  have hdτ : d τ ≠ 0 := denom_ne_zero _ τ
  have hmoebτ : moeb γ₀ τ = τ := by rw [← coe_smul_eq_moeb hγ₀1, hfix]

  have him : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

  have hmt : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (τ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuousAt_moeb γ₀ τ).tendsto
      rw [hmoebτ] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [him, self_mem_nhdsWithin] with z hz hne
      have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hz.ne'
      intro (habs : moeb γ₀ z = τ)
      have := moeb_sub hγ₀1 τ hfix z hdz
      rw [habs, sub_self, eq_comm, div_eq_zero_iff] at this
      rcases this with h | h
      · exact hne (sub_eq_zero.mp h)
      · exact mul_ne_zero hdz hdτ h

  have hinvC : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (γ₀ • ofComplex z) = F (ofComplex z) :=
    (tendsto_ofComplex τ).eventually (hF γ₀ (γ : Γ).2 hfix)

  have hkey : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      g z = (d z * d τ) ^ (-n) * g (moeb γ₀ z) := by
    filter_upwards [hfg, hmt.eventually hfg, him, hinvC, self_mem_nhdsWithin] with z hz hmz hzi hinv0 hne
    have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hzi.ne'
    have hzτ : (z : ℂ) - τ ≠ 0 := sub_ne_zero.mpr hne

    have hinv : F (ofComplex (moeb γ₀ z)) = F (ofComplex z) := by
      have h1 : ofComplex z = (⟨z, hzi⟩ : ℍ) := ofComplex_apply_of_im_pos hzi
      have h2 : moeb γ₀ z = ((γ₀ • (⟨z, hzi⟩ : ℍ) : ℍ) : ℂ) := by
        rw [coe_smul_eq_moeb hγ₀1]
      rw [h2, ofComplex_apply, ← h1]
      exact hinv0
    rw [hmz, hz, moeb_sub hγ₀1 τ hfix z hdz, smul_eq_mul, smul_eq_mul, div_zpow,
      div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), mul_assoc] at hinv
    have := mul_left_cancel₀ (zpow_ne_zero n hzτ) hinv
    rw [zpow_neg, eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), this, mul_comm]

  have hlim1 : Tendsto g (𝓝[≠] (τ : ℂ)) (𝓝 (g τ)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (d z * d τ) ^ (-n) * g (moeb γ₀ z)) (𝓝[≠] (τ : ℂ))
      (𝓝 ((d τ * d τ) ^ (-n) * g τ)) := by
    apply Tendsto.mul
    · have hc : ContinuousAt (fun z => (d z * d τ) ^ (-n)) τ := by
        apply ContinuousAt.zpow₀
        · exact ((continuous_denom _).mul continuous_const).continuousAt
        · exact Or.inl (mul_ne_zero hdτ hdτ)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hm : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝 (τ : ℂ)) := by
        have h := (continuousAt_moeb γ₀ τ).tendsto
        rw [hmoebτ] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact hg.continuousAt.tendsto.comp hm
  have heq := tendsto_nhds_unique (hlim1.congr' hkey) hlim2

  rw [eq_comm, mul_eq_right₀ hg0, zpow_neg, inv_eq_one] at heq
  rw [chi_apply, zpow_mul, zpow_two]
  exact heq

/--
@isnad1 id=dvd.3h4v.s12.e6033d9bebf6 from=translated src=- shape=88ed308b vocab=36cf611f
-/
theorem main (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z)
    (n : ℤ) (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  by_cases hmer : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  · obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp hn
    exact card_dvd_of_forall_chi_zpow_eq_one Γ hdet τ n
      (chi_zpow_eq_one Γ hdet F τ hF n g hg hg0 hfg)
  · rw [meromorphicOrderAt_of_not_meromorphicAt hmer] at hn
    have : n = 0 := by exact_mod_cast hn.symm
    rw [this, mul_zero]
    exact dvd_zero _

end UpperHalfPlane.EllipticOrderGL

end

open Filter _root_.UpperHalfPlane _root_.P2MW.S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq_of_det_eq_one.UpperHalfPlane in
open scoped MatrixGroups Topology in
/--
@isnad1 id=dvd.3h4v.s12.e6033d9bebf6 from=translated src=- shape=88ed308b vocab=36cf611f
-/
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (F : ℍ → ℂ) (τ : ℍ)
    (hF : ∀ γ ∈ Γ, γ • τ = τ → ∀ᶠ z in 𝓝[≠] τ, F (γ • z) = F z)
    (n : ℤ) (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n :=
  UpperHalfPlane.EllipticOrderGL.main Γ hdet F τ hF n hn
