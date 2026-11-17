import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_contDiffAt_of_mdifferentiable_im_cpow_mul_of_weight_of_central

set_option autoImplicit false

open Complex
open scoped Manifold Topology

noncomputable section

namespace AutomorphicForm

namespace MaassRegularity

def secM (ζ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![ζ.im, ζ.re; 0, 1]

def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

def descC (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (σ : ℂ) (ζ : ℂ) : ℂ :=
  (((ζ.im : ℝ) : ℂ) ^ σ) * F (secM ζ)

variable (p : Fin 2 → Fin 2 → ℝ)

def qf : ℝ := p 1 0 ^ 2 + p 1 1 ^ 2

def detf : ℝ := p 0 0 * p 1 1 - p 0 1 * p 1 0

def xf : ℝ := (p 0 0 * p 1 0 + p 0 1 * p 1 1) / qf p

def yf : ℝ := detf p / qf p

def zf : ℂ := (xf p : ℂ) + (yf p : ℂ) * Complex.I

def tf : ℝ := Real.sqrt (qf p)

def uf : ℂ := ((p 1 1 / tf p : ℝ) : ℂ) + ((-(p 1 0 / tf p) : ℝ) : ℂ) * Complex.I

variable {p}

/--
@isnad1 id=eq.0h1v.s5.d8df899e118d from=translated src=- shape=02bd95eb vocab=0765504e
-/
theorem detf_eq_det (m : Matrix (Fin 2) (Fin 2) ℝ) : detf (m : Fin 2 → Fin 2 → ℝ) = m.det := by
  rw [Matrix.det_fin_two]; rfl

/--
@isnad1 id=lt.1h1v.s5.812fe56503a0 from=translated src=- shape=fab1276c vocab=ab68d165
-/
theorem qf_pos (hp : 0 < detf p) : 0 < qf p := by
  unfold qf
  by_contra h
  have h0 : p 1 0 ^ 2 + p 1 1 ^ 2 = 0 := le_antisymm (not_lt.mp h) (by positivity)
  have hc : p 1 0 = 0 := by nlinarith [sq_nonneg (p 1 0), sq_nonneg (p 1 1)]
  have hd : p 1 1 = 0 := by nlinarith [sq_nonneg (p 1 0), sq_nonneg (p 1 1)]
  unfold detf at hp
  rw [hc, hd] at hp
  simp at hp

/--
@isnad1 id=lt.1h1v.s5.cbebe0e410ee from=translated src=- shape=fab1276c vocab=9aa431e6
-/
theorem tf_pos (hp : 0 < detf p) : 0 < tf p := Real.sqrt_pos.mpr (qf_pos hp)

/--
@isnad1 id=eq.1h1v.s5.5bbc5bdd44fd from=translated src=- shape=484694a6 vocab=14c5bcf8
-/
theorem tf_sq (hp : 0 < detf p) : tf p ^ 2 = qf p := Real.sq_sqrt (qf_pos hp).le

/--
@isnad1 id=lt.1h1v.s5.8d2536649397 from=translated src=- shape=fab1276c vocab=656f9c5c
-/
theorem yf_pos (hp : 0 < detf p) : 0 < yf p := div_pos hp (qf_pos hp)

/--
@isnad1 id=eq.0h1v.s4.8fc0d7c3cf90 from=translated src=- shape=6662fcc4 vocab=53d6fc23
-/
theorem zf_re : (zf p).re = xf p := by simp [zf]

/--
@isnad1 id=eq.0h1v.s4.ac316c6b63fb from=translated src=- shape=6662fcc4 vocab=796ce0c6
-/
theorem zf_im : (zf p).im = yf p := by simp [zf]

/--
@isnad1 id=eq.1h1v.s6.251a8e135e81 from=translated src=- shape=49fc0128 vocab=35e5b566
-/
theorem uf_re (hp : 0 < detf p) : (uf p).re = p 1 1 / tf p := by
  simp [uf]

/--
@isnad1 id=eq.1h1v.s6.35a90ba04f39 from=translated src=- shape=81a09fb7 vocab=85bb7957
-/
theorem uf_im (hp : 0 < detf p) : (uf p).im = -(p 1 0 / tf p) := by
  simp [uf]

/--
@isnad1 id=eq.1h1v.s5.e57410cab5e4 from=translated src=- shape=e6c5f1ae vocab=8f95f225
-/
theorem norm_uf (hp : 0 < detf p) : ‖uf p‖ = 1 := by
  have ht := tf_pos hp
  have hq := tf_sq hp
  rw [Complex.norm_eq_sqrt_sq_add_sq, uf_re hp, uf_im hp]
  rw [Real.sqrt_eq_one]
  field_simp
  unfold qf at hq
  nlinarith [hq]

/--
@isnad1 id=ne.1h1v.s5.a37330aac448 from=translated src=- shape=bda7bea9 vocab=5c8af5aa
-/
theorem uf_ne_zero (hp : 0 < detf p) : uf p ≠ 0 := by
  intro h
  have := norm_uf hp
  rw [h, norm_zero] at this
  exact zero_ne_one this

/--
@isnad1 id=eq.1h1v.s5.2fae5e8ae9f1 from=translated src=- shape=3c930d00 vocab=87c0eefb
-/
theorem exp_arg_uf (hp : 0 < detf p) : Complex.exp ((Complex.arg (uf p) : ℂ) * Complex.I) = uf p := by
  have h := Complex.norm_mul_exp_arg_mul_I (uf p)
  rw [norm_uf hp] at h
  simpa using h

/--
@isnad1 id=eq.1h1v.s6.2319f7c05fb1 from=translated src=- shape=65703556 vocab=33c614aa
-/
theorem cos_arg_uf (hp : 0 < detf p) : Real.cos (Complex.arg (uf p)) = p 1 1 / tf p := by
  rw [Complex.cos_arg (uf_ne_zero hp), norm_uf hp, div_one, uf_re hp]

/--
@isnad1 id=eq.1h1v.s6.b4b762ce4730 from=translated src=- shape=271940b4 vocab=5239a21e
-/
theorem sin_arg_uf (hp : 0 < detf p) : Real.sin (Complex.arg (uf p)) = -(p 1 0 / tf p) := by
  rw [Complex.sin_arg, norm_uf hp, div_one, uf_im hp]

/--
@isnad1 id=eq.1h1v.s8.9896d8155374 from=translated src=- shape=322a2493 vocab=fd4b2cd6
-/
theorem iwasawa (hp : 0 < detf p) :
    Matrix.of p = tf p • (secM (zf p) * rot (Complex.arg (uf p))) := by
  have ht := tf_pos hp
  have ht0 : tf p ≠ 0 := ht.ne'
  have hq0 : qf p ≠ 0 := (qf_pos hp).ne'
  have hq : tf p ^ 2 = qf p := tf_sq hp
  ext i j
  simp only [secM, rot, zf_re, zf_im, cos_arg_uf hp, sin_arg_uf hp, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, smul_eq_mul, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [xf, yf, detf] <;> field_simp <;> unfold qf at hq ⊢
  · nlinarith [hq]
  · nlinarith [hq]

/--
@isnad1 id=eq.0h1v.s5.60984015d004 from=translated src=- shape=548109e9 vocab=e1868f37
-/
theorem det_rot (θ : ℝ) : (rot θ).det = 1 := by
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    rw [← sq, ← sq]; exact Real.cos_sq_add_sin_sq θ
  simp [rot, Matrix.det_fin_two]
  linarith

/--
@isnad1 id=eq.0h2v.s6.5f8418cea3fb from=translated src=- shape=40f41c35 vocab=6120b9e5
-/
theorem det_secM_mul_rot (ζ : ℂ) (θ : ℝ) : (secM ζ * rot θ).det = ζ.im := by
  rw [Matrix.det_mul, det_rot, mul_one]
  simp [secM, Matrix.det_fin_two]

/--
@isnad1 id=eq.0h1v.s4.6e4576b77552 from=translated src=- shape=69d0c22f vocab=45d0f0fd
-/
theorem det_secM (ζ : ℂ) : (secM ζ).det = ζ.im := by
  simp [secM, Matrix.det_fin_two]

def G (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ) (p : Fin 2 → Fin 2 → ℝ) : ℂ :=
  (((tf p : ℝ) : ℂ) ^ c₀) * ((uf p) ^ k * ((((yf p : ℝ) : ℂ) ^ (-σ)) * descC F σ (zf p)))

/--
@isnad1 id=eq.3h5v.s8.385358d8148b from=translated src=- shape=ab34a10b vocab=0147fbe9
-/
theorem F_eq_G (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * rot θ) = Complex.exp (Complex.I * k * θ) * F m)
    (hc : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ t : ℝ, 0 < t →
      F (t • m) = ((t : ℂ) ^ c₀) * F m)
    (hp : 0 < detf p) : F p = G F k c₀ σ p := by
  have ht := tf_pos hp
  have hy := yf_pos hp
  set s : Matrix (Fin 2) (Fin 2) ℝ := secM (zf p) with hs
  set θ : ℝ := Complex.arg (uf p) with hθ
  have hsdet : 0 < s.det := by rw [hs, det_secM, zf_im]; exact hy
  have hsrdet : 0 < (s * rot θ).det := by rw [hs, det_secM_mul_rot, zf_im]; exact hy

  have h1 : F p = F (tf p • (s * rot θ)) := by
    have := iwasawa hp
    rw [← this]
    rfl

  have h2 : F (tf p • (s * rot θ)) = ((tf p : ℂ) ^ c₀) * F (s * rot θ) := hc _ hsrdet _ ht

  have h3 : F (s * rot θ) = Complex.exp (Complex.I * k * θ) * F s := hk _ hsdet θ

  have h4 : Complex.exp (Complex.I * k * θ) = (uf p) ^ k := by
    rw [show Complex.I * k * θ = (k : ℂ) * ((θ : ℂ) * Complex.I) by ring, Complex.exp_int_mul,
      hθ, exp_arg_uf hp]

  have hyC : ((yf p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h5 : F s = ((yf p : ℝ) : ℂ) ^ (-σ) * descC F σ (zf p) := by
    have hpow : ((yf p : ℝ) : ℂ) ^ (-σ) * ((yf p : ℝ) : ℂ) ^ σ = 1 := by
      rw [Complex.cpow_neg, inv_mul_cancel₀]
      rw [Complex.cpow_def]
      simp [hyC, Complex.exp_ne_zero]
    unfold descC
    rw [zf_im, ← hs, ← mul_assoc, hpow, one_mul]
  rw [h1, h2, h3, h4, h5]
  rfl

section Smooth

variable (N : WithTop ℕ∞)

/--
@isnad1 id=contdiff.0h3v.s8.19083267bd61 from=translated src=- shape=7f2ffb05 vocab=e7557333
-/
theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ N (fun p : Fin 2 → Fin 2 → ℝ => p i j) :=
  contDiff_apply_apply ℝ ℝ i j

/--
@isnad1 id=contdiff.0h1v.s7.eecea0f42f25 from=translated src=- shape=630b9339 vocab=155134db
-/
theorem contDiff_qf : ContDiff ℝ N (qf : (Fin 2 → Fin 2 → ℝ) → ℝ) := by
  unfold qf
  exact ((contDiff_entry N 1 0).pow 2).add ((contDiff_entry N 1 1).pow 2)

/--
@isnad1 id=contdiff.0h1v.s7.1973067cf98c from=translated src=- shape=630b9339 vocab=52f1cd06
-/
theorem contDiff_detf : ContDiff ℝ N (detf : (Fin 2 → Fin 2 → ℝ) → ℝ) := by
  unfold detf
  exact ((contDiff_entry N 0 0).mul (contDiff_entry N 1 1)).sub
    ((contDiff_entry N 0 1).mul (contDiff_entry N 1 0))

/--
@isnad1 id=contdiff.1h2v.s8.e9ce7358bd19 from=translated src=- shape=d6ca75ed vocab=a47aa876
-/
theorem contDiffAt_xf (hp : 0 < detf p) : ContDiffAt ℝ N (xf : (Fin 2 → Fin 2 → ℝ) → ℝ) p := by
  unfold xf
  refine ContDiffAt.div ?_ (contDiff_qf N).contDiffAt (qf_pos hp).ne'
  exact (((contDiff_entry N 0 0).mul (contDiff_entry N 1 0)).add
    ((contDiff_entry N 0 1).mul (contDiff_entry N 1 1))).contDiffAt

/--
@isnad1 id=contdiff.1h2v.s8.1975831c992c from=translated src=- shape=d6ca75ed vocab=83c58d22
-/
theorem contDiffAt_yf (hp : 0 < detf p) : ContDiffAt ℝ N (yf : (Fin 2 → Fin 2 → ℝ) → ℝ) p := by
  unfold yf
  exact (contDiff_detf N).contDiffAt.div (contDiff_qf N).contDiffAt (qf_pos hp).ne'

/--
@isnad1 id=contdiff.0h1v.s5.0378ca16b747 from=translated src=- shape=67032c59 vocab=ad596e3f
-/
theorem contDiff_ofReal' : ContDiff ℝ N (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

/--
@isnad1 id=contdiff.1h2v.s8.def4d91bc5d1 from=translated src=- shape=c4f153f8 vocab=e5b4cb31
-/
theorem contDiffAt_zf (hp : 0 < detf p) : ContDiffAt ℝ N (zf : (Fin 2 → Fin 2 → ℝ) → ℂ) p := by
  unfold zf
  exact (((contDiff_ofReal' N).contDiffAt.comp p (contDiffAt_xf N hp))).add
    ((((contDiff_ofReal' N).contDiffAt.comp p (contDiffAt_yf N hp))).mul contDiffAt_const)

/--
@isnad1 id=contdiff.1h2v.s8.c54f0e2f5f50 from=translated src=- shape=d6ca75ed vocab=3b572638
-/
theorem contDiffAt_tf (hp : 0 < detf p) : ContDiffAt ℝ N (tf : (Fin 2 → Fin 2 → ℝ) → ℝ) p := by
  unfold tf
  exact (Real.contDiffAt_sqrt (qf_pos hp).ne').comp p (contDiff_qf N).contDiffAt

/--
@isnad1 id=contdiff.1h3v.s5.ec4224fd9bd0 from=translated src=- shape=283b67e0 vocab=75ed462d
-/
theorem contDiffAt_cpow_const_real (c : ℂ) {ζ : ℂ} (hζ : ζ ∈ Complex.slitPlane) :
    ContDiffAt ℝ N (fun ζ : ℂ => ζ ^ c) ζ := by
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => ζ ^ c) Complex.slitPlane := fun w hw =>
    (Complex.hasStrictDerivAt_cpow_const (c := c) hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have hC : ContDiffOn ℂ N (fun ζ : ℂ => ζ ^ c) Complex.slitPlane := hd.contDiffOn Complex.isOpen_slitPlane
  exact (hC.contDiffAt (Complex.isOpen_slitPlane.mem_nhds hζ)).restrict_scalars ℝ

/--
@isnad1 id=contdiff.1h3v.s5.c40be7928036 from=translated src=- shape=2135afaa vocab=54bb07e9
-/
theorem contDiffAt_zpow_real (k : ℤ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    ContDiffAt ℝ N (fun ζ : ℂ => ζ ^ k) ζ := by
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => ζ ^ k) ({0}ᶜ : Set ℂ) :=
    differentiableOn_zpow k _ (Or.inl (by simp))
  have hC : ContDiffOn ℂ N (fun ζ : ℂ => ζ ^ k) ({0}ᶜ : Set ℂ) := hd.contDiffOn isOpen_compl_singleton
  exact (hC.contDiffAt (isOpen_compl_singleton.mem_nhds hζ)).restrict_scalars ℝ

/--
@isnad1 id=contdiff.1h3v.s8.6b315499e089 from=translated src=- shape=23cc7f70 vocab=c33e8ecb
-/
theorem contDiffAt_tf_cpow (c₀ : ℂ) (hp : 0 < detf p) :
    ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => ((tf p : ℝ) : ℂ) ^ c₀) p := by
  have hslit : ((tf p : ℝ) : ℂ) ∈ Complex.slitPlane := by
    simp [Complex.slitPlane, tf_pos hp]
  have h1 : ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => ((tf p : ℝ) : ℂ)) p :=
    (contDiff_ofReal' N).contDiffAt.comp p (contDiffAt_tf N hp)
  exact (contDiffAt_cpow_const_real N c₀ hslit).comp p h1

/--
@isnad1 id=contdiff.1h3v.s8.550b4daffba6 from=translated src=- shape=23cc7f70 vocab=1f72ffc0
-/
theorem contDiffAt_yf_cpow (c : ℂ) (hp : 0 < detf p) :
    ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => ((yf p : ℝ) : ℂ) ^ c) p := by
  have hslit : ((yf p : ℝ) : ℂ) ∈ Complex.slitPlane := by
    simp [Complex.slitPlane, yf_pos hp]
  have h1 : ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => ((yf p : ℝ) : ℂ)) p :=
    (contDiff_ofReal' N).contDiffAt.comp p (contDiffAt_yf N hp)
  exact (contDiffAt_cpow_const_real N c hslit).comp p h1

/--
@isnad1 id=contdiff.1h2v.s8.511923be455b from=translated src=- shape=c4f153f8 vocab=5018601e
-/
theorem contDiffAt_uf (hp : 0 < detf p) : ContDiffAt ℝ N (uf : (Fin 2 → Fin 2 → ℝ) → ℂ) p := by
  unfold uf
  have ht0 : tf p ≠ 0 := (tf_pos hp).ne'
  have h1 : ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => p 1 1 / tf p) p :=
    (contDiff_entry N 1 1).contDiffAt.div (contDiffAt_tf N hp) ht0
  have h2 : ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => -(p 1 0 / tf p)) p :=
    ((contDiff_entry N 1 0).contDiffAt.div (contDiffAt_tf N hp) ht0).neg
  exact ((contDiff_ofReal' N).contDiffAt.comp p h1).add
    (((contDiff_ofReal' N).contDiffAt.comp p h2).mul contDiffAt_const)

/--
@isnad1 id=contdiff.1h3v.s8.be8c39f33298 from=translated src=- shape=4124074c vocab=76c87b5a
-/
theorem contDiffAt_uf_zpow (k : ℤ) (hp : 0 < detf p) :
    ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => (uf p) ^ k) p :=
  (contDiffAt_zpow_real N k (uf_ne_zero hp)).comp p (contDiffAt_uf N hp)

/--
@isnad1 id=contdiff.2h4v.s8.56c3f15e2f42 from=translated src=- shape=9fbbf13b vocab=4509b0a6
-/
theorem contDiffAt_descC (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (σ : ℂ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)))
    {ζ : ℂ} (hζ : 0 < ζ.im) : ContDiffAt ℝ N (descC F σ) ζ := by

  have hd : DifferentiableOn ℂ (descC F σ) {ζ : ℂ | 0 < ζ.im} := by
    intro w hw
    have hz := hhol ⟨w, hw⟩
    rw [UpperHalfPlane.mdifferentiableAt_iff] at hz
    have hev : ((fun z : UpperHalfPlane =>
          (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) ∘
            UpperHalfPlane.ofComplex) =ᶠ[𝓝 w] descC F σ := by
      filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hw] with ζ' hζ'
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hζ']
      rfl
    have hz' : DifferentiableAt ℂ (descC F σ) w := (hev.differentiableAt_iff).mp hz
    exact hz'.differentiableWithinAt
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  have hC : ContDiffOn ℂ N (descC F σ) {ζ : ℂ | 0 < ζ.im} := hd.contDiffOn hopen
  exact (hC.contDiffAt (hopen.mem_nhds hζ)).restrict_scalars ℝ

/--
@isnad1 id=contdiff.2h6v.s9.e7ac5192b11c from=translated src=- shape=4c9e7f87 vocab=01eb982e
-/
theorem contDiffAt_G (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)))
    (hp : 0 < detf p) : ContDiffAt ℝ N (G F k c₀ σ) p := by
  unfold G
  have hz : 0 < (zf p).im := by rw [zf_im]; exact yf_pos hp
  have hΨ : ContDiffAt ℝ N (fun p : Fin 2 → Fin 2 → ℝ => descC F σ (zf p)) p :=
    (contDiffAt_descC N F σ hhol hz).comp p (contDiffAt_zf N hp)
  exact (contDiffAt_tf_cpow N c₀ hp).mul
    ((contDiffAt_uf_zpow N k hp).mul ((contDiffAt_yf_cpow N (-σ) hp).mul hΨ))

end Smooth

/--
@isnad1 id=contdiff.4h5v.s10.255e1753ba5e from=translated src=- shape=6bf345d3 vocab=0af1c30f
-/
theorem main (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (hc : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ t : ℝ, 0 < t →
      F (t • m) = ((t : ℂ) ^ c₀) * F m)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)))
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) :
    ContDiffAt ℝ (⊤ : ℕ∞) F m := by
  have hm' : 0 < detf (m : Fin 2 → Fin 2 → ℝ) := by rwa [detf_eq_det]

  have hopen : IsOpen {p : Fin 2 → Fin 2 → ℝ | 0 < detf p} :=
    (contDiff_detf 0).continuous.isOpen_preimage _ isOpen_Ioi
  have hev : F =ᶠ[𝓝 (m : Fin 2 → Fin 2 → ℝ)] G F k c₀ σ := by
    filter_upwards [hopen.mem_nhds hm'] with p hp
    exact F_eq_G F k c₀ σ hk hc hp
  exact (contDiffAt_G _ F k c₀ σ hhol hm').congr_of_eventuallyEq hev

end MaassRegularity

end AutomorphicForm

end

/--
@isnad1 id=contdiff.4h5v.s10.255e1753ba5e from=translated src=- shape=6bf345d3 vocab=0af1c30f
-/
theorem solution
    (F : (Fin 2 → Fin 2 → ℝ) → ℂ) (k : ℤ) (c₀ σ : ℂ)
    (hk : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ θ : ℝ,
      F (m * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]) =
        Complex.exp (Complex.I * k * θ) * F m)
    (hc : ∀ m : Matrix (Fin 2) (Fin 2) ℝ, 0 < m.det → ∀ t : ℝ, 0 < t →
      F (t • m) = ((t : ℂ) ^ c₀) * F m)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * F (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)))
    (m : Matrix (Fin 2) (Fin 2) ℝ) (hm : 0 < m.det) :
    ContDiffAt ℝ (⊤ : ℕ∞) F m :=
  AutomorphicForm.MaassRegularity.main F k c₀ σ hk hc hhol m hm
