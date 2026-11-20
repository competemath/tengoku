import Tengoku.Hellingerrepolean4.Hellinger.PaperSpecs
import Tengoku.Seed.Analysis.Convex.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Analysis.Calculus.Deriv.Inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The biased Hellinger-to-information implication, using the actual binary
entropy curve. Its convexity is proved from explicit derivatives. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set

namespace Hellinger.EntropyTransfer

def halfLog (v : ℝ) : ℝ := 1 / 2 * Real.log ((1 + v) / (1 - v))

/--
@isnad1 id=hasderiv.1h1v.s6.910646b15850 from=translated src=- shape=dfaf4561 vocab=c2bb1455
-/
theorem halfLog_hasDerivAt {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt halfLog (1 / (1 - v ^ 2)) v := by
  change HasDerivAt (fun x : ℝ => 1 / 2 * Real.log ((1 + x) / (1 - x))) _ _
  simpa using
    Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range 0 hv.1 hv.2

/--
@isnad1 id=lt.1h1v.s4.4face04ac328 from=translated src=- shape=ab40fd09 vocab=c6397172
-/
theorem halfLog_gt_self {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) 1) : v < halfLog v := by
  have h := Real.sum_range_le_log_div hv.1.le hv.2 2
  norm_num [Finset.sum_range_succ] at h
  change v < 1 / 2 * Real.log ((1 + v) / (1 - v))
  nlinarith [pow_pos hv.1 3]

/--
@isnad1 id=continuo.0h0v.s3.c4c196def8ce from=translated src=- shape=e3d48bcb vocab=90a7fee3
-/
theorem root_continuous : Continuous root :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

/--
@isnad1 id=mem.1h1v.s5.f9f21a8cc003 from=translated src=- shape=727b7c20 vocab=c491f6ee
-/
theorem root_interior {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : root z ∈ Ioo (0 : ℝ) 1 := by
  have hs : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  constructor
  · exact Real.sqrt_pos.mpr hs
  · change Real.sqrt (1 - z ^ 2) < 1
    exact (Real.sqrt_lt' zero_lt_one).mpr (by nlinarith [hz.1])

/--
@isnad1 id=eq.1h1v.s6.7c2ab99a46f9 from=translated src=- shape=ef6ad3ac vocab=29a71ac4
-/
theorem root_sq {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : root z ^ 2 = 1 - z ^ 2 :=
  Real.sq_sqrt (by nlinarith [hz.1, hz.2])

/--
@isnad1 id=hasderiv.1h1v.s6.13a07ece7a76 from=translated src=- shape=23dd8561 vocab=dcea668c
-/
theorem root_hasDerivAt {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt root (-z / root z) z := by
  have hp : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have h := ((hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2)).sqrt hp.ne'
  convert h using 1
  · rfl
  · dsimp
    unfold root
    field_simp
    ring

/-- Natural-log version of the entropy curve.-/
def entropyCurve (z : ℝ) : ℝ := Real.binEntropy ((1 - root z) / 2)

def entropyCurveDeriv (z : ℝ) : ℝ := z * halfLog (root z) / root z

/--
@isnad1 id=continuo.0h0v.s3.826e2202ea48 from=translated src=- shape=e3d48bcb vocab=28a328a8
-/
theorem entropyCurve_continuous : Continuous entropyCurve :=
  Real.binEntropy_continuous.comp ((continuous_const.sub root_continuous).div_const 2)

/--
@isnad1 id=hasderiv.1h1v.s5.00a3b5b4307d from=translated src=- shape=c0b471d9 vocab=c977aa56
-/
theorem entropyCurve_hasDerivAt {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt entropyCurve (entropyCurveDeriv z) z := by
  have hv := root_interior hz
  let p := (1 - root z) / 2
  have hp : p ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [p]; linarith [hv.2], by dsimp [p]; linarith [hv.1]⟩
  have hd := (Real.hasDerivAt_binEntropy hp.1.ne' hp.2.ne).comp z
    (((root_hasDerivAt hz).const_sub 1).div_const 2)
  have hlog : Real.log (1 - p) - Real.log p = 2 * halfLog (root z) := by
    have h₁ : 1 - p = (1 + root z) / 2 := by dsimp [p]; ring
    rw [h₁]
    dsimp only [p, halfLog]
    rw [Real.log_div (by linarith [hv.1]) (by norm_num),
      Real.log_div (by linarith [hv.2]) (by norm_num),
      Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
    ring
  apply hd.congr_deriv
  rw [hlog]
  dsimp [entropyCurveDeriv]
  ring

/--
@isnad1 id=hasderiv.1h1v.s6.df5c9e7edeed from=translated src=- shape=0da3852a vocab=1f72d2fb
-/
theorem entropyCurveDeriv_hasDerivAt {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt entropyCurveDeriv
      ((halfLog (root z) - root z) / root z ^ 3) z := by
  have hv := root_interior hz
  have hr := root_hasDerivAt hz
  have hL := (halfLog_hasDerivAt (show root z ∈ Ioo (-1 : ℝ) 1 from
    ⟨by linarith [hv.1], hv.2⟩)).comp z hr
  have h := ((hasDerivAt_id z).mul hL).div hr hv.1.ne'
  apply h.congr_deriv
  have hs := root_sq (show z ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hz.1], hz.2.le⟩)
  have hz0 : z ≠ 0 := hz.1.ne'
  have hv0 : root z ≠ 0 := hv.1.ne'
  have hden : 1 - root z ^ 2 = z ^ 2 := by linarith
  dsimp
  rw [hden]
  field_simp
  linear_combination halfLog (root z) * hs

/--
@isnad1 id=strictco.0h0v.s4.de6a8e49f80b from=translated src=- shape=2b2e5daa vocab=15ffff51
-/
theorem entropyCurve_strictConvex : StrictConvexOn ℝ (Icc (0 : ℝ) 1) entropyCurve := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 1) entropyCurve_continuous.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  have he : deriv entropyCurve =ᶠ[nhds z] entropyCurveDeriv := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with x hx
    exact (entropyCurve_hasDerivAt hx).deriv
  change 0 < deriv (deriv entropyCurve) z
  rw [he.deriv_eq, (entropyCurveDeriv_hasDerivAt hz).deriv]
  exact div_pos (sub_pos.mpr (halfLog_gt_self (root_interior hz)))
    (pow_pos (root_interior hz).1 3)

/--
@isnad1 id=strictmo.0h0v.s4.552e2556cbf3 from=translated src=- shape=6c3888e7 vocab=1739468a
-/
theorem entropyCurve_strictMono : StrictMonoOn entropyCurve (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) entropyCurve_continuous.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [(entropyCurve_hasDerivAt hz).deriv]
  exact div_pos (mul_pos hz.1 ((root_interior hz).1.trans (halfLog_gt_self (root_interior hz))))
    (root_interior hz).1

/--
@isnad1 id=lt.0h0v.s4.0b427c4055e0 from=translated src=- shape=cf0a9d99 vocab=8079cfe6
-/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

def entropyCurveBits (z : ℝ) : ℝ := entropyCurve z / Real.log 2

/--
@isnad1 id=strictmo.0h0v.s4.6e6f4627a1bb from=translated src=- shape=6c3888e7 vocab=aa7eeba1
-/
theorem entropyCurveBits_strictMono : StrictMonoOn entropyCurveBits (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  exact div_lt_div_of_pos_right (entropyCurve_strictMono hx hy hxy) log_two_pos

/--
@isnad1 id=convexon.0h0v.s4.35c91f13b827 from=translated src=- shape=2b2e5daa vocab=97d3a0c5
-/
theorem entropyCurveBits_convex : ConvexOn ℝ (Icc (0 : ℝ) 1) entropyCurveBits := by
  change ConvexOn ℝ (Icc (0 : ℝ) 1) (fun z => entropyCurve z / Real.log 2)
  simpa only [entropyCurveBits, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    entropyCurve_strictConvex.convexOn.smul (inv_nonneg.mpr log_two_pos.le)

/--
@isnad1 id=mem.1h1v.s5.f73599b71543 from=translated src=- shape=ef75474a vocab=78734cba
-/
theorem root_mem_Icc {t : ℝ} (_ht : t ∈ Icc (-1 : ℝ) 1) : root t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  change Real.sqrt (1 - t ^ 2) ≤ 1
  exact (Real.sqrt_le_left zero_le_one).mpr (by nlinarith [sq_nonneg t])

/--
@isnad1 id=eq.1h1v.s5.1962258842cc from=translated src=- shape=f1ca9f23 vocab=45805e56
-/
theorem root_root {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : root (root t) = |t| := by
  change Real.sqrt (1 - root t ^ 2) = |t|
  rw [root_sq ht, show 1 - (1 - t ^ 2) = t ^ 2 by ring, Real.sqrt_sq_eq_abs]

/--
@isnad1 id=eq.1h1v.s6.ec7a5b9f2c1d from=translated src=- shape=fc37b484 vocab=5b2be843
-/
theorem entropyCurve_root {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    entropyCurve (root t) = Real.binEntropy ((1 - t) / 2) := by
  unfold entropyCurve
  rw [root_root ht]
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
  · rw [abs_of_neg (lt_of_not_ge ht0)]
    convert Real.binEntropy_one_sub ((1 - t) / 2) using 1
    congr 1
    ring

/--
@isnad1 id=eq.1h1v.s6.8ea713c477e7 from=translated src=- shape=fc37b484 vocab=4a9ef2e6
-/
theorem entropyCurveBits_root {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    entropyCurveBits (root t) = PaperSpecs.binaryEntropyBits ((1 - t) / 2) := by
  rw [entropyCurveBits, entropyCurve_root ht]
  rfl

/--
@isnad1 id=eq.0h0v.s3.8734b4930da2 from=translated src=- shape=3c26ae4f vocab=2dfb7957
-/
@[simp] theorem entropyCurveBits_one : entropyCurveBits 1 = 1 := by
  simp only [entropyCurveBits, entropyCurve, root, one_pow, sub_self, Real.sqrt_zero, sub_zero]
  rw [one_div, Real.binEntropy_two_inv, div_self log_two_pos.ne']

/--
@isnad1 id=eq.0h0v.s3.073a5d4f6501 from=translated src=- shape=3c26ae4f vocab=2dfb7957
-/
@[simp] theorem entropyCurveBits_zero : entropyCurveBits 0 = 0 := by
  simp [entropyCurveBits, entropyCurve, root]

/-- A fixed increment of a convex function grows when shifted to the right.
The elementary two-point proof includes all interval endpoints.
@isnad1 id=le.4h3v.s6.b5ac4f79a0cb from=translated src=- shape=a3cda4b3 vocab=48261294
-/
theorem convex_increment_right {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Icc (0 : ℝ) 1) Φ)
    {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) :
    Φ a - Φ b ≤ Φ 1 - Φ (1 - a + b) := by
  by_cases hb1 : b = 1
  · have ha1 : a = 1 := by linarith
    simp [hb1, ha1]
  have hden : 0 < 1 - b := sub_pos.mpr (lt_of_le_of_ne (hba.trans ha) hb1)
  let u := (1 - a) / (1 - b)
  let v := (a - b) / (1 - b)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr ha) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hba) hden.le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
  have hp : b ∈ Icc (0 : ℝ) 1 := ⟨hb, hba.trans ha⟩
  have h₁ := hΦ.2 hp (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hu hv huv
  have h₂ := hΦ.2 hp (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hv hu (by linarith)
  have hea : u * b + v * 1 = a := by dsimp [u, v]; field_simp; ring
  have heb : v * b + u * 1 = 1 - a + b := by dsimp [u, v]; field_simp; ring
  simp only [smul_eq_mul, hea, heb] at h₁ h₂
  have he₁ : u * Φ b + v * Φ b = Φ b := by rw [← add_mul, huv, one_mul]
  have he₂ : v * Φ 1 + u * Φ 1 = Φ 1 := by rw [← add_mul, add_comm v u, huv, one_mul]
  linarith

open Hellinger.Fourier

/--
@isnad1 id=mem.1h4v.s5.9d7bcff9ae69 from=translated src=- shape=8433be3d vocab=29e29a41
-/
theorem mean_mem_Icc {Ω : Type*} [Fintype Ω] [Nonempty Ω] {u : Ω → ℝ} {a b : ℝ}
    (hu : ∀ x, u x ∈ Icc a b) : mean u ∈ Icc a b := by
  constructor
  · simpa only [mean_const] using mean_le_mean (fun _ : Ω => a) u (fun x => (hu x).1)
  · simpa only [mean_const] using mean_le_mean u (fun _ : Ω => b) (fun x => (hu x).2)

/--
@isnad1 id=le.2h5v.s6.5fcf29e41c9b from=translated src=- shape=66ad9dc7 vocab=80bc1fb2
-/
theorem convex_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] {Φ : ℝ → ℝ} {a b : ℝ}
    (hΦ : ConvexOn ℝ (Icc a b) Φ) (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc a b) :
    Φ (mean u) ≤ mean (fun x => Φ (u x)) := by
  have hw : (∑ _ : Ω, (Fintype.card Ω : ℝ)⁻¹) = 1 := by
    simp [Fintype.card_ne_zero]
  simpa only [smul_eq_mul, ← Finset.mul_sum, mean] using
    hΦ.map_sum_le (t := Finset.univ) (w := fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) (p := u)
      (fun _ _ => by positivity) hw (fun x _ => hu x)

/--
@isnad1 id=le.1h2v.s5.a7745f7ea78c from=translated src=- shape=18d959e8 vocab=54694640
-/
theorem mean_root_le_root_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1) :
    mean (fun x => root (u x)) ≤ root (mean u) := by
  have hw : (∑ _ : Ω, (Fintype.card Ω : ℝ)⁻¹) = 1 := by
    simp [Fintype.card_ne_zero]
  simpa only [smul_eq_mul, ← Finset.mul_sum, mean] using
    root_concave.le_map_sum (t := Finset.univ) (w := fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹)
      (p := u) (fun _ _ => by positivity) hw (fun x _ => hu x)

/-- The information upper bound before the Hellinger estimate is inserted.
The bias appears through `root (mean u)` and is retained throughout.
@isnad1 id=le.1h2v.s7.3ae419fa5b9e from=translated src=- shape=4d2462b9 vocab=591929ec
-/
theorem information_le_entropy_gap {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1) :
    PaperSpecs.binaryEntropyBits ((1 - mean u) / 2) -
      mean (fun x => PaperSpecs.binaryEntropyBits ((1 - u x) / 2)) ≤
        1 - entropyCurveBits (1 - objective u) := by
  have hmean := mean_mem_Icc hu
  have hroot (x : Ω) := root_mem_Icc (hu x)
  have hb := mean_mem_Icc hroot
  have ha := root_mem_Icc hmean
  have hba := mean_root_le_root_mean u hu
  have hj := convex_mean entropyCurveBits_convex (fun x => root (u x)) hroot
  have hinc := convex_increment_right entropyCurveBits_convex hb.1 hba ha.2
  rw [entropyCurveBits_one] at hinc
  have hrewrite : (fun x => entropyCurveBits (root (u x))) =
      (fun x => PaperSpecs.binaryEntropyBits ((1 - u x) / 2)) :=
    funext fun x => entropyCurveBits_root (hu x)
  rw [hrewrite] at hj
  rw [← entropyCurveBits_root hmean]
  unfold objective
  have he : 1 - (root (mean u) - mean (fun x => root (u x))) =
      1 - root (mean u) + mean (fun x => root (u x)) := by ring
  rw [he]
  linarith

/--
@isnad1 id=mem.1h2v.s6.a032534cbd64 from=translated src=- shape=ebec74c0 vocab=53d2ec49
-/
theorem objective_complement_mem_Icc {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1) : 1 - objective u ∈ Icc (0 : ℝ) 1 := by
  have ha := root_mem_Icc (mean_mem_Icc hu)
  have hb := mean_mem_Icc (fun x => root_mem_Icc (hu x))
  have hba := mean_root_le_root_mean u hu
  unfold objective
  constructor <;> linarith [ha.2, hb.1]

/--
@isnad1 id=le.3h3v.s7.d901a9ccc115 from=translated src=- shape=0c16a43a vocab=d846107a
-/
theorem information_of_hellinger {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) (hH : objective u ≤ 1 - root ρ) :
    PaperSpecs.binaryEntropyBits ((1 - mean u) / 2) -
      mean (fun x => PaperSpecs.binaryEntropyBits ((1 - u x) / 2)) ≤
        1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
  have hr : ρ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
  have hm := entropyCurveBits_strictMono.monotoneOn (root_mem_Icc hr)
    (objective_complement_mem_Icc u hu) (show root ρ ≤ 1 - objective u by linarith)
  rw [entropyCurveBits_root hr] at hm
  exact (information_le_entropy_gap u hu).trans (by linarith)

/--
@isnad1 id=lt.3h3v.s7.cd234200015b from=translated src=- shape=0c16a43a vocab=bce4f130
-/
theorem strict_information_of_strict_hellinger {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) (hH : objective u < 1 - root ρ) :
    PaperSpecs.binaryEntropyBits ((1 - mean u) / 2) -
      mean (fun x => PaperSpecs.binaryEntropyBits ((1 - u x) / 2)) <
        1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
  have hr : ρ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
  have hm := entropyCurveBits_strictMono (root_mem_Icc hr)
    (objective_complement_mem_Icc u hu) (show root ρ < 1 - objective u by linarith)
  rw [entropyCurveBits_root hr] at hm
  exact (information_le_entropy_gap u hu).trans_lt (by linarith)

/--
@isnad1 id=eq.4h3v.s7.fe55a59bac6b from=translated src=- shape=c8883cc6 vocab=d846107a
-/
theorem information_equality_implies_hellinger_equality
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (u : Ω → ℝ) (hu : ∀ x, u x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) (hH : objective u ≤ 1 - root ρ)
    (hI : PaperSpecs.binaryEntropyBits ((1 - mean u) / 2) -
      mean (fun x => PaperSpecs.binaryEntropyBits ((1 - u x) / 2)) =
        1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2)) :
    objective u = 1 - root ρ := by
  by_contra hne
  have hs := strict_information_of_strict_hellinger u hu ρ hρ (lt_of_le_of_ne hH hne)
  linarith

/--
@isnad1 id=mem.1h3v.s5.f85e6a752c9e from=translated src=- shape=da1f579e vocab=4fca7e19
-/
theorem boolean_mem_Icc {n : ℕ} {f : PaperSpecs.Cube n → ℝ}
    (hf : PaperSpecs.IsBoolean f) (x : PaperSpecs.Cube n) : f x ∈ Icc (-1 : ℝ) 1 := by
  rcases hf x with h | h <;> rw [h] <;> norm_num

/-- The complete specified biased Hellinger-to-CK implication.
@isnad1 id=ckbound.3h3v.s5.2fe5af0debb4 from=translated src=- shape=ea717ca3 vocab=6d6dde93
-/
theorem hellinger_implies_ck {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hH : PaperSpecs.HellingerBound f ρ hρ) : PaperSpecs.CKBound f ρ hρ := by
  have h := information_of_hellinger ((cubeBSC n ρ hρ).apply f)
    ((cubeBSC n ρ hρ).apply_mem_Icc f (boolean_mem_Icc hf)) ρ hρ hH
  simpa only [UniformChannel.mean_apply, PaperSpecs.CKBound, PaperSpecs.posteriorInformation] using h

/--
@isnad1 id=entropyt.0h0v.s0.39c9da0b05d0 from=translated src=- shape=45709ebd vocab=39c9da0b
-/
theorem entropyTransfer : PaperSpecs.EntropyTransfer := by
  intro n f hf ρ hρ hH
  exact hellinger_implies_ck f hf ρ hρ hH

/--
@isnad1 id=lt.3h3v.s7.8b0179422343 from=translated src=- shape=e1eae687 vocab=dbc92cb2
-/
theorem strict_hellinger_implies_strict_ck {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hH : objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) :
    PaperSpecs.posteriorInformation f ρ hρ < 1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
  have h := strict_information_of_strict_hellinger ((cubeBSC n ρ hρ).apply f)
    ((cubeBSC n ρ hρ).apply_mem_Icc f (boolean_mem_Icc hf)) ρ hρ hH
  simpa only [UniformChannel.mean_apply, PaperSpecs.posteriorInformation] using h

/--
@isnad1 id=eq.4h3v.s7.2e82c0ee8a5a from=translated src=- shape=93641e50 vocab=707d8906
-/
theorem ck_equality_implies_hellinger_equality {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (hf : PaperSpecs.IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hH : PaperSpecs.HellingerBound f ρ hρ)
    (hI : PaperSpecs.posteriorInformation f ρ hρ =
      1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2)) :
    objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ := by
  apply information_equality_implies_hellinger_equality ((cubeBSC n ρ hρ).apply f)
    ((cubeBSC n ρ hρ).apply_mem_Icc f (boolean_mem_Icc hf)) ρ hρ hH
  simpa only [UniformChannel.mean_apply, PaperSpecs.posteriorInformation] using hI

/--
@isnad1 id=eq.0h1v.s6.35da0d3a95ef from=translated src=- shape=1b8273c9 vocab=9f32847f
-/
theorem binaryEntropyBits_neg_bias (t : ℝ) :
    PaperSpecs.binaryEntropyBits ((1 - -t) / 2) = PaperSpecs.binaryEntropyBits ((1 - t) / 2) := by
  unfold PaperSpecs.binaryEntropyBits
  have h : (1 - -t) / 2 = 1 - (1 - t) / 2 := by ring
  rw [h, Real.binEntropy_one_sub]

/--
@isnad1 id=eq.1h3v.s5.fad58d1fcb44 from=translated src=- shape=beda8483 vocab=e7efd29e
-/
theorem posteriorInformation_neg {n : ℕ} (f : PaperSpecs.Cube n → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    PaperSpecs.posteriorInformation (fun x => -f x) ρ hρ =
      PaperSpecs.posteriorInformation f ρ hρ := by
  simp only [PaperSpecs.posteriorInformation, mean_neg, UniformChannel.apply_neg,
    binaryEntropyBits_neg_bias]

/--
@isnad1 id=eq.1h4v.s6.841b89281c55 from=translated src=- shape=eb12c99f vocab=df5bb684
-/
theorem signed_dictator_information (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    PaperSpecs.posteriorInformation
      (fun x => if negative then -boolSign (x i) else boolSign (x i)) ρ hρ =
        1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
  have hpos : PaperSpecs.posteriorInformation (fun x : PaperSpecs.Cube n => boolSign (x i)) ρ hρ =
      1 - PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
    have hchar : character n {i} = (fun x => boolSign (x i)) := by
      funext x
      simp [character]
    have hnoise (x : PaperSpecs.Cube n) :
        (cubeBSC n ρ hρ).apply (fun x => boolSign (x i)) x = ρ * boolSign (x i) := by
      simpa [hchar] using character_eigenfunction n {i} ρ hρ x
    have hm : mean (fun x : PaperSpecs.Cube n => boolSign (x i)) = 0 := by
      apply antipodal_mean_zero
      intro x
      exact boolSign_neg (x i)
    have hpoint (x : PaperSpecs.Cube n) :
        PaperSpecs.binaryEntropyBits ((1 - ρ * boolSign (x i)) / 2) =
          PaperSpecs.binaryEntropyBits ((1 - ρ) / 2) := by
      cases x i
      · simp [boolSign]
      · simpa [boolSign] using binaryEntropyBits_neg_bias ρ
    simp only [PaperSpecs.posteriorInformation, hm, sub_zero, hnoise, hpoint, mean_const]
    have hhalf : PaperSpecs.binaryEntropyBits (1 / 2) = 1 := by
      unfold PaperSpecs.binaryEntropyBits
      rw [one_div, Real.binEntropy_two_inv, div_self log_two_pos.ne']
    rw [hhalf]
  cases negative
  · exact hpos
  · simpa only [Bool.true_eq, ite_true, posteriorInformation_neg] using hpos

end Hellinger.EntropyTransfer
