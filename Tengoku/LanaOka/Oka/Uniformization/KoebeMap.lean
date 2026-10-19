/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Complex.CoveringMap
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Topology.Covering.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Koebe's square-root map

For `t` in the unit disc `𝔻`, `mob t z = (z + t) / (1 + conj t z)` is an automorphism of `𝔻` with
inverse `mob (-t)`. For `b ∈ 𝔻` the **Koebe map**
`koebe b = mob (-b²) ∘ (· ^ 2) ∘ mob b` on `𝔻` (and `2` outside `𝔻`, so that no point outside
`𝔻` lands in `𝔻`) is a 2-sheeted covering `𝔻 ∖ {-b} → 𝔻 ∖ {-b²}`
(`isCoveringMapOn_koebe`), and it is a Blaschke product:
`koebe b z = z (z - c) / (1 - conj c z)` with `c = -2b / (1 + |b|²)` (`koebe_eq_blaschke`).

If `|b|² = r` the Blaschke form gives `|koebe b z| < r` as soon as `|z| < koebeRadius r`, where
`koebeRadius r > r` for `0 < r < 1` (`norm_koebe_lt`, `lt_koebeRadius`). This is the estimate that
drives the Koebe–Fisher–Hubbard–Wittner iteration (`Oka/Uniformization/KoebeIteration.lean`):
applied to a domain `U ⊆ 𝔻` whose boundary point closest to `0` is `a = -b²` with `|a| = r`, the
covering `koebe b ⁻¹' U → U` has a domain containing the disc of radius `koebeRadius r`.
-/

open Complex Metric Set Filter Topology

open scoped ComplexConjugate

namespace Uniformization

/-! ### Disc automorphisms -/

/-- The disc automorphism `z ↦ (z + t) / (1 + conj t z)`. -/
noncomputable def mob (t z : ℂ) : ℂ := (z + t) / (1 + conj t * z)

theorem normSq_one_add_conj_mul_sub (t z : ℂ) :
    normSq (1 + conj t * z) - normSq (z + t) = (1 - normSq t) * (1 - normSq z) := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

theorem normSq_lt_one {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : normSq z < 1 := by
  rw [mem_ball_zero_iff] at hz
  rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]

theorem one_add_conj_mul_ne_zero {t z : ℂ} (ht : t ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    1 + conj t * z ≠ 0 := by
  have h := normSq_one_add_conj_mul_sub t z
  have h1 := normSq_lt_one ht
  have h2 := normSq_lt_one hz
  intro h0
  rw [h0, map_zero] at h
  nlinarith [normSq_nonneg (z + t)]

theorem mob_mem_ball {t z : ℂ} (ht : t ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob t z ∈ ball (0 : ℂ) 1 := by
  have h := normSq_one_add_conj_mul_sub t z
  have h1 := normSq_lt_one ht
  have h2 := normSq_lt_one hz
  have hd := one_add_conj_mul_ne_zero ht hz
  have hpos : 0 < normSq (1 + conj t * z) := normSq_pos.mpr hd
  rw [mem_ball_zero_iff, mob, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have : normSq (z + t) < normSq (1 + conj t * z) := by nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this

theorem mob_neg_mob {t z : ℂ} (ht : t ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob (-t) (mob t z) = z := by
  have hd := one_add_conj_mul_ne_zero ht hz
  have hc : conj t * t = normSq t := by rw [mul_comm, mul_conj]
  have h1 : 1 - conj t * t ≠ 0 := by
    have := normSq_lt_one ht
    rw [hc]; exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
  have hd' : 1 + z * conj t ≠ 0 := by rwa [mul_comm]
  unfold mob
  rw [map_neg]
  have hden : 1 + -conj t * ((z + t) / (1 + conj t * z)) = (1 - conj t * t) / (1 + conj t * z) := by
    field_simp; ring
  have hnum : (z + t) / (1 + conj t * z) + -t = z * (1 - conj t * t) / (1 + conj t * z) := by
    field_simp; ring
  rw [hden, hnum, div_div_div_cancel_right₀ hd, mul_div_assoc, div_self h1, mul_one]

theorem mob_mob_neg {t z : ℂ} (ht : t ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob t (mob (-t) z) = z := by
  have := mob_neg_mob (t := -t) (by simpa using ht) hz
  simpa using this

@[simp] theorem mob_zero (t : ℂ) : mob t 0 = t := by simp [mob]

theorem mob_neg_self (t : ℂ) : mob t (-t) = 0 := by simp [mob]

theorem continuousOn_mob {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) : ContinuousOn (mob t) (ball 0 1) :=
  (continuousOn_id.add continuousOn_const).div (continuousOn_const.add
    (continuousOn_const.mul continuousOn_id)) fun _ hz ↦ one_add_conj_mul_ne_zero ht hz

theorem differentiableOn_mob {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (mob t) (ball 0 1) :=
  (differentiableOn_id.add (differentiableOn_const _)).div ((differentiableOn_const _).add
    ((differentiableOn_const _).mul differentiableOn_id)) fun _ hz ↦ one_add_conj_mul_ne_zero ht hz

theorem mob_injOn {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) : InjOn (mob t) (ball 0 1) := by
  intro z hz w hw h
  rw [← mob_neg_mob ht hz, h, mob_neg_mob ht hw]

/-- A homeomorphism between two subsets of `ℂ` given by two mutually inverse maps. -/
@[simps]
def homeomorphOfInvOn {A B : Set ℂ} (φ ψ : ℂ → ℂ) (hφ : MapsTo φ A B) (hψ : MapsTo ψ B A)
    (h₁ : ∀ z ∈ A, ψ (φ z) = z) (h₂ : ∀ w ∈ B, φ (ψ w) = w) (hφc : ContinuousOn φ A)
    (hψc : ContinuousOn ψ B) : A ≃ₜ B where
  toFun z := ⟨φ z, hφ z.2⟩
  invFun w := ⟨ψ w, hψ w.2⟩
  left_inv z := Subtype.ext (h₁ z z.2)
  right_inv w := Subtype.ext (h₂ w w.2)
  continuous_toFun := hφc.mapsToRestrict hφ
  continuous_invFun := hψc.mapsToRestrict hψ

/-! ### The Koebe map -/

/-- The **Koebe map** `mob (-b²) ∘ (· ^ 2) ∘ mob b` on the unit disc, extended by the constant `2`
outside the disc (so that the preimage of any subset of the disc lies in the disc). -/
noncomputable def koebe (b z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball (0 : ℂ) 1 then mob (-b ^ 2) (mob b z ^ 2) else 2

theorem koebe_of_mem {b z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    koebe b z = mob (-b ^ 2) (mob b z ^ 2) := by
  simp [koebe, hz]

theorem koebe_of_notMem {b z : ℂ} (hz : z ∉ ball (0 : ℂ) 1) : koebe b z = 2 := by
  simp [koebe, hz]

theorem two_notMem_ball : (2 : ℂ) ∉ ball (0 : ℂ) 1 := by
  simp

theorem sq_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ^ 2 ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at hw ⊢
  rw [norm_pow]; nlinarith [norm_nonneg w]

theorem neg_sq_mem_ball {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) : -b ^ 2 ∈ ball (0 : ℂ) 1 := by
  simpa using sq_mem_ball hb

theorem koebe_mem_ball {b z : ℂ} (hb : b ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    koebe b z ∈ ball (0 : ℂ) 1 := by
  rw [koebe_of_mem hz]
  exact mob_mem_ball (neg_sq_mem_ball hb) (sq_mem_ball (mob_mem_ball hb hz))

theorem mem_ball_of_koebe_mem {b z : ℂ} (hz : koebe b z ∈ ball (0 : ℂ) 1) :
    z ∈ ball (0 : ℂ) 1 := by
  by_contra h
  rw [koebe_of_notMem h] at hz
  exact two_notMem_ball hz

/-- The Koebe map sends the point `-b` to the critical value `-b²`, and it is the only
point of the disc mapping there. -/
theorem koebe_eq_crit_iff {b z : ℂ} (hb : b ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    koebe b z = -b ^ 2 ↔ z = -b := by
  rw [koebe_of_mem hz]
  constructor
  · intro h
    have h1 : mob b z ^ 2 = 0 := by
      apply mob_injOn (neg_sq_mem_ball hb) (sq_mem_ball (mob_mem_ball hb hz))
        (mem_ball_self one_pos)
      rw [h, mob_zero]
    have h2 : mob b z = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    have h3 := mob_neg_mob hb hz
    rw [h2, mob_zero] at h3
    exact h3.symm
  · rintro rfl
    rw [mob_neg_self]; simp

theorem preimage_koebe_ball_diff {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) :
    koebe b ⁻¹' (ball 0 1 \ {-b ^ 2}) = ball 0 1 \ {-b} := by
  ext z
  simp only [mem_preimage, Set.mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hz := mem_ball_of_koebe_mem h1
    exact ⟨hz, fun h ↦ h2 ((koebe_eq_crit_iff hb hz).mpr h)⟩
  · rintro ⟨hz, h2⟩
    exact ⟨koebe_mem_ball hb hz, fun h ↦ h2 ((koebe_eq_crit_iff hb hz).mp h)⟩

/-- `mob t` maps `𝔻 ∖ {-t}` onto `𝔻 ∖ {0}`. -/
theorem mapsTo_mob_diff {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    MapsTo (mob t) (ball 0 1 \ {-t}) (ball 0 1 \ {0}) := by
  rintro z ⟨hz, hzt⟩
  refine ⟨mob_mem_ball ht hz, fun h ↦ hzt ?_⟩
  have := mob_neg_mob ht hz
  rw [show mob t z = 0 from h, mob_zero] at this
  exact this.symm

theorem mapsTo_mob_diff' {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    MapsTo (mob (-t)) (ball 0 1 \ {0}) (ball 0 1 \ {-t}) := by
  rintro z ⟨hz, hz0⟩
  refine ⟨mob_mem_ball (by simpa using ht) hz, fun h ↦ hz0 ?_⟩
  have := mob_mob_neg ht hz
  rw [show mob (-t) z = -t from h, mob_neg_self] at this
  exact this.symm

theorem mapsTo_mob_diff_zero {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    MapsTo (mob t) (ball 0 1 \ {0}) (ball 0 1 \ {t}) := by
  have := mapsTo_mob_diff' (t := -t) (by simpa using ht)
  simpa using this

theorem mapsTo_mob_diff_zero' {t : ℂ} (ht : t ∈ ball (0 : ℂ) 1) :
    MapsTo (mob (-t)) (ball 0 1 \ {t}) (ball 0 1 \ {0}) := by
  have := mapsTo_mob_diff (t := -t) (by simpa using ht)
  simpa using this

theorem preimage_sq_ball_diff :
    (fun w : ℂ ↦ w ^ 2) ⁻¹' (ball 0 1 \ {0}) = ball 0 1 \ {0} := by
  ext w
  simp only [mem_preimage, Set.mem_sdiff, mem_ball_zero_iff, mem_singleton_iff, norm_pow,
    pow_eq_zero_iff two_ne_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h; push Not at h; nlinarith
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith [norm_nonneg w], h2⟩

/-- **The Koebe map is a covering** `𝔻 ∖ {-b} → 𝔻 ∖ {-b²}`. -/
theorem isCoveringMapOn_koebe {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) :
    IsCoveringMapOn (koebe b) (ball 0 1 \ {-b ^ 2}) := by
  set a := -b ^ 2 with ha
  have haD : a ∈ ball (0 : ℂ) 1 := neg_sq_mem_ball hb
  set P : Set ℂ := ball 0 1 \ {0}
  have hsq : IsCoveringMapOn (fun w : ℂ ↦ w ^ 2) P :=
    (isCoveringMapOn_npow 2 (by norm_num)).mono fun w hw ↦ hw.2
  have hsq' := hsq.isCoveringMap_restrictPreimage
  have hpre := preimage_koebe_ball_diff hb
  -- the two homeomorphisms
  let e₁ : (koebe b ⁻¹' (ball 0 1 \ {a})) ≃ₜ ((fun w : ℂ ↦ w ^ 2) ⁻¹' P) :=
    (Homeomorph.setCongr hpre).trans <| (homeomorphOfInvOn (mob b) (mob (-b))
      (mapsTo_mob_diff hb) (mapsTo_mob_diff' hb) (fun z hz ↦ mob_neg_mob hb hz.1)
      (fun w hw ↦ mob_mob_neg hb hw.1) ((continuousOn_mob hb).mono sdiff_subset)
      ((continuousOn_mob (by simpa using hb)).mono sdiff_subset)).trans
      (Homeomorph.setCongr preimage_sq_ball_diff.symm)
  let e₂ : P ≃ₜ (ball 0 1 \ {a} : Set ℂ) :=
    homeomorphOfInvOn (mob a) (mob (-a)) (mapsTo_mob_diff_zero haD)
      (mapsTo_mob_diff_zero' haD) (fun z hz ↦ mob_neg_mob haD hz.1)
      (fun w hw ↦ mob_mob_neg haD hw.1) ((continuousOn_mob haD).mono sdiff_subset)
      ((continuousOn_mob (by simpa using haD)).mono sdiff_subset)
  have heq : (ball 0 1 \ {a}).restrictPreimage (koebe b) =
      e₂ ∘ P.restrictPreimage (fun w : ℂ ↦ w ^ 2) ∘ e₁ := by
    funext z
    apply Subtype.ext
    have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 \ {-b} := hpre ▸ z.2
    change koebe b (z : ℂ) = mob a (mob b (z : ℂ) ^ 2)
    rw [koebe_of_mem hz.1]
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ (isOpen_ball.sdiff isClosed_singleton)
    (hpre ▸ isOpen_ball.sdiff isClosed_singleton) ?_
  rw [heq]
  exact (hsq'.comp_homeomorph e₁).homeomorph_comp e₂

theorem differentiableOn_koebe {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (koebe b) (ball 0 1) := by
  have h : DifferentiableOn ℂ (fun z ↦ mob (-b ^ 2) (mob b z ^ 2)) (ball 0 1) :=
    (differentiableOn_mob (neg_sq_mem_ball hb)).comp ((differentiableOn_mob hb).pow 2)
      fun z hz ↦ sq_mem_ball (mob_mem_ball hb hz)
  exact h.congr fun z hz ↦ koebe_of_mem hz

@[simp] theorem koebe_zero (b : ℂ) : koebe b 0 = 0 := by
  rw [koebe_of_mem (mem_ball_self one_pos)]
  simp [mob]

/-! ### The Blaschke form and the modulus estimate -/

/-- The second zero of the Koebe map. -/
noncomputable def koebeZero (b : ℂ) : ℂ := -2 * b / (1 + normSq b)

/-- The Koebe map is the Blaschke product `z (z - c) / (1 - conj c z)` with `c = koebeZero b`. -/
theorem koebe_eq_blaschke {b z : ℂ} (hb : b ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    koebe b z = z * (z - koebeZero b) / (1 - conj (koebeZero b) * z) := by
  rw [koebe_of_mem hz]
  have hd := one_add_conj_mul_ne_zero hb hz
  have hn1 : (1 + normSq b : ℂ) ≠ 0 := by
    have := normSq_nonneg b; exact_mod_cast (by linarith : (1 + normSq b : ℝ) ≠ 0)
  have hn2 : (1 - normSq b : ℂ) ≠ 0 := by
    have := normSq_lt_one hb; exact_mod_cast (by linarith : (1 - normSq b : ℝ) ≠ 0)
  have hc : conj b * b = normSq b := by rw [mul_comm, mul_conj]
  have hconj : conj (koebeZero b) = -2 * conj b / (1 + normSq b) := by
    simp [koebeZero, map_div₀, conj_ofReal, map_ofNat]
  have hD : 1 - conj (koebeZero b) * z = (1 + normSq b + 2 * conj b * z) / (1 + normSq b) := by
    rw [hconj]; field_simp; ring
  have hD' : (1 + normSq b + 2 * conj b * z : ℂ) ≠ 0 := by
    -- `1 - conj c z ≠ 0` since `|c| < 1`, `|z| < 1`
    have hcball : -koebeZero b ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_neg, koebeZero, norm_div, norm_mul]
      have h1 : ‖(1 + normSq b : ℂ)‖ = 1 + normSq b := by
        rw [show (1 + normSq b : ℂ) = ((1 + normSq b : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_of_nonneg (by linarith [normSq_nonneg b])]
      rw [h1, div_lt_one (by linarith [normSq_nonneg b])]
      have hnb : normSq b = ‖b‖ ^ 2 := normSq_eq_norm_sq b
      rw [hnb]; simp only [norm_neg, RCLike.norm_ofNat]
      nlinarith [sq_nonneg (‖b‖ - 1), norm_nonneg b, normSq_lt_one hb, hnb]
    have := one_add_conj_mul_ne_zero hcball hz
    rw [map_neg, neg_mul, ← sub_eq_add_neg, hD] at this
    intro h; rw [h, zero_div] at this; exact this rfl
  rw [hD]
  unfold mob
  rw [map_neg, map_pow]
  set A := 1 + conj b * z
  have hden : 1 + -conj b ^ 2 * ((z + b) / A) ^ 2 =
      (1 - conj b * b) * (1 + conj b * b + 2 * conj b * z) / A ^ 2 := by
    field_simp; ring
  have hnum : ((z + b) / A) ^ 2 + -b ^ 2 =
      z * (1 - conj b * b) * (z * (1 + conj b * b) + 2 * b) / A ^ 2 := by
    field_simp; ring
  rw [hnum, hden, koebeZero, ← hc]
  rw [← hc] at hn1 hn2 hD'
  field_simp
  ring

/-- `γ(r) = 2 √r / (1 + r)`: the modulus of `koebeZero b` when `|b|² = r`. -/
noncomputable def koebeGamma (r : ℝ) : ℝ := 2 * Real.sqrt r / (1 + r)

/-- The radius `h(r)` of the disc about `0` on which the Koebe map with critical value of modulus
`r` stays in the disc of radius `r`: the positive root of `s² + γ(r)(1 - r) s - r`. -/
noncomputable def koebeRadius (r : ℝ) : ℝ :=
  (-(koebeGamma r * (1 - r)) + Real.sqrt ((koebeGamma r * (1 - r)) ^ 2 + 4 * r)) / 2

theorem norm_koebeZero (b : ℂ) : ‖koebeZero b‖ = koebeGamma (‖b‖ ^ 2) := by
  have h1 : (1 + normSq b : ℂ) = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [normSq_eq_norm_sq]; push_cast; ring
  rw [koebeZero, h1, norm_div, norm_mul, Complex.norm_of_nonneg (by positivity), koebeGamma,
    Real.sqrt_sq (norm_nonneg b)]
  simp

theorem koebeGamma_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ koebeGamma r := by
  unfold koebeGamma; positivity

theorem koebeGamma_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : koebeGamma r < 1 := by
  unfold koebeGamma
  rw [div_lt_one (by linarith)]
  have hs := Real.sq_sqrt hr0
  have hs1 : Real.sqrt r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hr0 hr1
  nlinarith [Real.sqrt_nonneg r]

/-- `|z - c| (1 + |c| |z|) ≤ (|z| + |c|) |1 - conj c z|` in the disc: the pseudo-hyperbolic triangle
inequality. -/
theorem norm_sub_mul_le {c z : ℂ} (hc : c ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖z - c‖ * (1 + ‖c‖ * ‖z‖) ≤ (‖z‖ + ‖c‖) * ‖1 - conj c * z‖ := by
  have hid := normSq_one_add_conj_mul_sub (-c) z
  rw [map_neg, neg_mul, ← sub_eq_add_neg, ← sub_eq_add_neg, normSq_neg] at hid
  simp only [normSq_eq_norm_sq] at hid
  have hc1 : ‖c‖ < 1 := mem_ball_zero_iff.mp hc
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have htri : ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le z c
  set X := ‖z - c‖
  set Y := ‖1 - conj c * z‖
  set s := ‖z‖
  set γ := ‖c‖
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hγ : 0 ≤ γ := norm_nonneg _
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  have hXs : X ^ 2 ≤ (s + γ) ^ 2 := pow_le_pow_left₀ hX htri 2
  have hpos : 0 ≤ (1 - γ ^ 2) * (1 - s ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
  have hY2 : Y ^ 2 = X ^ 2 + (1 - γ ^ 2) * (1 - s ^ 2) := by linarith
  rw [mul_pow, mul_pow, hY2]
  nlinarith [mul_le_mul_of_nonneg_right hXs hpos]

/-- The positive root of `s² + β s - r` bounds the region where the quadratic is negative. -/
theorem quadratic_neg {s r β : ℝ} (hr : 0 ≤ r) (hβ : 0 ≤ β) (hs0 : 0 ≤ s)
    (hs : s < (-β + Real.sqrt (β ^ 2 + 4 * r)) / 2) : s ^ 2 + β * s - r < 0 := by
  have hD : 0 ≤ β ^ 2 + 4 * r := by positivity
  have hS := Real.sq_sqrt hD
  have hS0 := Real.sqrt_nonneg (β ^ 2 + 4 * r)
  nlinarith [mul_pos (by linarith : 0 < (-β + Real.sqrt (β ^ 2 + 4 * r)) / 2 - s)
    (by linarith : 0 < s + (β + Real.sqrt (β ^ 2 + 4 * r)) / 2)]

/-- Conversely, where the quadratic is negative we are below the positive root. -/
theorem lt_of_quadratic_neg {s r β : ℝ} (hr : 0 ≤ r) (hβ : 0 ≤ β) (hs0 : 0 ≤ s)
    (hs : s ^ 2 + β * s - r < 0) : s < (-β + Real.sqrt (β ^ 2 + 4 * r)) / 2 := by
  have hD : 0 ≤ β ^ 2 + 4 * r := by positivity
  have hS := Real.sq_sqrt hD
  have hS0 := Real.sqrt_nonneg (β ^ 2 + 4 * r)
  by_contra h
  push Not at h
  nlinarith [mul_nonneg (by linarith : 0 ≤ s - (-β + Real.sqrt (β ^ 2 + 4 * r)) / 2)
    (by linarith : 0 ≤ s + (β + Real.sqrt (β ^ 2 + 4 * r)) / 2)]

theorem lt_koebeRadius {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : r < koebeRadius r := by
  have hγ := koebeGamma_lt_one hr0.le hr1
  have hγ0 := koebeGamma_nonneg hr0.le
  refine lt_of_quadratic_neg hr0.le (by nlinarith) hr0.le ?_
  nlinarith [mul_pos hr0 (mul_pos (by linarith : 0 < 1 - r) (by linarith : 0 < 1 - koebeGamma r))]

theorem koebeRadius_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : koebeRadius r < 1 := by
  have hγ0 := koebeGamma_nonneg hr0
  set β := koebeGamma r * (1 - r)
  have hβ : 0 ≤ β := mul_nonneg hγ0 (by linarith)
  have hD : 0 ≤ β ^ 2 + 4 * r := by positivity
  have hS := Real.sq_sqrt hD
  have hS0 := Real.sqrt_nonneg (β ^ 2 + 4 * r)
  unfold koebeRadius
  by_contra h
  push Not at h
  nlinarith

theorem continuousOn_koebeRadius : ContinuousOn koebeRadius (Ici 0) := by
  have hγ : ContinuousOn koebeGamma (Ici 0) := by
    unfold koebeGamma
    exact (continuousOn_const.mul Real.continuous_sqrt.continuousOn).div
      (continuousOn_const.add continuousOn_id) fun r hr ↦ by
        have : (0 : ℝ) ≤ r := hr; positivity
  unfold koebeRadius
  have hβ : ContinuousOn (fun r ↦ koebeGamma r * (1 - r)) (Ici 0) :=
    hγ.mul (continuousOn_const.sub continuousOn_id)
  exact ((hβ.neg).add (Real.continuous_sqrt.comp_continuousOn
    ((hβ.pow 2).add (continuousOn_const.mul continuousOn_id)))).div_const 2

/-- **The Koebe estimate.** If `|z| < h(|b|²)` then `z ∈ 𝔻` and `|koebe b z| < |b|²`. -/
theorem norm_koebe_lt {b z : ℂ} (hb : b ∈ ball (0 : ℂ) 1)
    (hz : ‖z‖ < koebeRadius (‖b‖ ^ 2)) : z ∈ ball (0 : ℂ) 1 ∧ ‖koebe b z‖ < ‖b‖ ^ 2 := by
  set r := ‖b‖ ^ 2 with hr
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; nlinarith [norm_nonneg b]
  have hzD : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans (koebeRadius_lt_one hr0 hr1))
  refine ⟨hzD, ?_⟩
  set c := koebeZero b
  have hcγ : ‖c‖ = koebeGamma r := norm_koebeZero b
  have hγ1 := koebeGamma_lt_one hr0 hr1
  have hcD : c ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hcγ ▸ hγ1)
  have hden : 1 - conj c * z ≠ 0 := by
    have := one_add_conj_mul_ne_zero (t := -c) (by simpa using hcD) hzD
    rwa [map_neg, neg_mul, ← sub_eq_add_neg] at this
  rw [koebe_eq_blaschke hb hzD, norm_div, norm_mul]
  have hineq := norm_sub_mul_le hcD hzD
  rw [hcγ] at hineq
  set s := ‖z‖
  set γ := koebeGamma r
  have hs0 : 0 ≤ s := norm_nonneg z
  have hγ0 : 0 ≤ γ := koebeGamma_nonneg hr0
  have hq := quadratic_neg hr0 (mul_nonneg hγ0 (by linarith)) hs0 hz
  have hYpos : 0 < ‖1 - conj c * z‖ := norm_pos_iff.mpr hden
  rw [div_lt_iff₀ hYpos]
  have h1 : 0 < 1 + γ * s := by positivity
  -- `s ‖z - c‖ (1 + γ s) ≤ s (s + γ) Y < r (1 + γ s) Y`
  have h2 : s * ‖z - c‖ * (1 + γ * s) ≤ s * (s + γ) * ‖1 - conj c * z‖ := by
    have := mul_le_mul_of_nonneg_left hineq hs0
    nlinarith [this]
  have h3 : s * (s + γ) < r * (1 + γ * s) := by nlinarith [hq]
  have h4 : s * (s + γ) * ‖1 - conj c * z‖ < r * (1 + γ * s) * ‖1 - conj c * z‖ :=
    mul_lt_mul_of_pos_right h3 hYpos
  have h5 : s * ‖z - c‖ * (1 + γ * s) < r * ‖1 - conj c * z‖ * (1 + γ * s) := by nlinarith
  exact lt_of_mul_lt_mul_right h5 h1.le

end Uniformization
