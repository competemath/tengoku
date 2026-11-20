import Tengoku
import Tengoku.Shearertrianglefreeind.ShearerTriangleFreeInd.Analysis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-
## Definition of LambertW
-/
namespace Tengoku.Shearertrianglefreeind end Tengoku.Shearertrianglefreeind open Tengoku.Shearertrianglefreeind
open Real

variable {x y : ℝ}

noncomputable def _root_.Tengoku.Shearertrianglefreeind.xexp : ℝ → ℝ := fun x ↦ x * exp x

/--
@isnad1 id=eq.0h0v.s3.47012fcb6469 from=translated src=- shape=3c26ae4f vocab=ae2a0e16
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_zero : xexp 0 = 0 := zero_mul _

/--
@isnad1 id=lt.1h1v.s4.38cdea63e46f from=translated src=- shape=35bd48ee vocab=0faaf7ad
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_pos (hx : 0 < x) : 0 < xexp x := mul_pos hx (exp_pos _)

/--
@isnad1 id=lt.1h1v.s4.0c6c1e9d3820 from=translated src=- shape=5aedd577 vocab=0faaf7ad
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_neg (hx : x < 0) : xexp x < 0 := mul_neg_of_neg_of_pos hx (exp_pos _)

/--
@isnad1 id=hasderiv.0h1v.s5.9e3df1d38d88 from=translated src=- shape=29387167 vocab=162af097
-/
lemma _root_.Tengoku.Shearertrianglefreeind.hasDerivAt_xexp : HasDerivAt xexp ((1 + x) * exp x) x := by
  convert HasDerivAt.mul (hasDerivAt_id' x) (Real.hasDerivAt_exp x) using 1
  all_goals first | rfl | ring

/--
@isnad1 id=continuo.0h0v.s3.38317ecd469c from=translated src=- shape=e3d48bcb vocab=44bc8373
-/
lemma _root_.Tengoku.Shearertrianglefreeind.continuous_xexp : Continuous xexp := Continuous.mul continuous_id' continuous_exp

-- Stronger version of log_mul_self_monotoneOn
/--
@isnad1 id=strictmo.0h0v.s4.88f6068b9d13 from=translated src=- shape=1fdf3d14 vocab=57e3ebd0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.StrictMonoOn_xexp : StrictMonoOn xexp (Set.Ici (-1)) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _) (Continuous.continuousOn continuous_xexp)
    (fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_xexp)
    (fun _ hx ↦ mul_pos (by rw [interior_Ici] at hx; exact neg_lt_iff_pos_add'.mp hx) (exp_pos _))

/--
@isnad1 id=le.1h1v.s4.93654fc0af1a from=translated src=- shape=8aca16f3 vocab=6604a4ca
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_le (hx : -1 ≤ x) : xexp (-1) ≤ xexp x :=
  StrictMonoOn.monotoneOn StrictMonoOn_xexp Set.self_mem_Ici hx hx

/--
@isnad1 id=lt.1h1v.s4.e5399e241a14 from=translated src=- shape=8aca16f3 vocab=ebfd1b8c
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_lt (hx : -1 < x) : xexp (-1) < xexp x :=
  StrictMonoOn_xexp Set.self_mem_Ici (le_of_lt hx) hx

/--
@isnad1 id=lt.0h0v.s4.d23f828c094f from=translated src=- shape=00b7d787 vocab=ebfd1b8c
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_neg_one_neg : xexp (-1) < 0 := by
  rw [←xexp_zero]
  exact xexp_lt (neg_one_lt_zero)

/--
@isnad1 id=eq.1h1v.s4.6fdf6676469f from=translated src=- shape=0addd72b vocab=a629e252
-/
lemma _root_.Tengoku.Shearertrianglefreeind.log_xexp (hx : 0 < x) : log (xexp x) = x + log x := by
  rw [xexp, log_mul (ne_of_lt hx).symm (exp_ne_zero _) , log_exp, add_comm]

/--
@isnad1 id=le.0h1v.s3.414623f46916 from=translated src=- shape=e63234f4 vocab=56b71b69
-/
lemma _root_.Tengoku.Shearertrianglefreeind.self_le_xexp : x ≤ xexp x := by
  rw [←sub_nonneg, xexp, ←mul_sub_one]
  rcases lt_or_ge 0 x with (hx | hx)
  · exact le_of_lt (mul_pos hx (sub_pos.2 (one_lt_exp_iff.2 hx)))
  · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.2 (exp_le_one_iff.2 hx))

/--
@isnad1 id=ex.1h1v.s5.142d6359b08e from=translated src=- shape=70b35a4b vocab=6604a4ca
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_surjective (hx : xexp (-1) ≤ x) : ∃ y, -1 ≤ y ∧ xexp y = x :=
  IsPreconnected.intermediate_value₂ isPreconnected_Ici (Set.self_mem_Ici)
    (le_trans self_le_xexp hx) (Continuous.continuousOn continuous_xexp)
    (continuousOn_const (c := x)) hx self_le_xexp

/--
@isnad1 id=injon.0h0v.s4.db8ebb4e99f7 from=translated src=- shape=1fdf3d14 vocab=7521d972
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_InjOn : Set.InjOn xexp (Set.Ici (-1)) := StrictMonoOn.injOn StrictMonoOn_xexp

noncomputable def _root_.Tengoku.Shearertrianglefreeind.xexpOrderIso : Set.Ici (-1 : ℝ) ≃o Set.Ici (xexp (-1)) := by
  refine StrictMono.orderIsoOfSurjective (fun x ↦ ⟨xexp x, xexp_le x.2⟩) ?_ ?_
  · apply StrictMono.codRestrict
    exact (Set.strictMonoOn_iff_strictMono.mp StrictMonoOn_xexp)
  · intro x
    have ⟨y, hyb, hyx⟩ := xexp_surjective x.2
    use ⟨y, hyb⟩
    simp_all

/--
@isnad1 id=eq.1h1v.s8.03d5a74285f9 from=translated src=- shape=d2fd2e10 vocab=b54500e9
-/
lemma _root_.Tengoku.Shearertrianglefreeind.coe_xexpOrderIso_apply (hx : -1 ≤ x) : xexpOrderIso ⟨x, hx⟩ = xexp x :=
  rfl

/--
@isnad1 id=le.0h2v.s4.733cdaad59b4 from=translated src=- shape=ae14d82a vocab=55eab1db
-/
lemma _root_.Tengoku.Shearertrianglefreeind.coe_Ici {x : Set.Ici y} : y ≤ x := x.2

noncomputable def _root_.Tengoku.Shearertrianglefreeind.W : ℝ → ℝ := fun x ↦ if hx : xexp (-1) ≤ x then xexpOrderIso.symm ⟨x, hx⟩ else 0

/--
@isnad1 id=eq.1h1v.s8.7cf7aaaaa1bc from=translated src=- shape=756b7fdb vocab=f56b0bee
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_rw (hx : xexp (-1) ≤ x) : W x = xexpOrderIso.symm ⟨x, hx⟩ := dite_eq_left hx

/--
@isnad1 id=eqon.0h0v.s8.8fbf09b505f3 from=translated src=- shape=94b7f168 vocab=d6566338
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_EqOn : Set.EqOn (α := Set.Ici (xexp (-1))) (fun x ↦ W x.1) (fun x ↦ xexpOrderIso.symm x)
  Set.univ := by
  intro x _
  simp [W_rw x.2]

/--
@isnad1 id=le.1h1v.s4.44590b154aec from=translated src=- shape=01785d3f vocab=a886c881
-/
lemma _root_.Tengoku.Shearertrianglefreeind.neg_one_le_W (hx : xexp (-1) ≤ x) : -1 ≤ W x := by
  rw [W_rw hx]
  exact coe_Ici

/--
@isnad1 id=eq.0h1v.s8.f152de969b63 from=translated src=- shape=7ac4616a vocab=73c8bbf4
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_coe (a : Set.Ici (xexp (-1))) : W a.1 = xexpOrderIso.symm a := dite_eq_left a.2

/--
@isnad1 id=eq.1h1v.s4.94a1c6f805e2 from=translated src=- shape=328cf37e vocab=a886c881
-/
lemma _root_.Tengoku.Shearertrianglefreeind.xexp_W (hx : xexp (-1) ≤ x) : xexp (W x) = x := by
  rw [W_rw hx]
  exact congrArg Subtype.val (xexpOrderIso.apply_symm_apply ⟨x, hx⟩)

/--
@isnad1 id=strictmo.0h0v.s4.901f6f116335 from=translated src=- shape=b66f5bc5 vocab=f68cc944
-/
lemma _root_.Tengoku.Shearertrianglefreeind.StrictMonoOn_W : StrictMonoOn W (Set.Ici (xexp (-1))) := by
  intro _ hx _ hy hxy
  refine ((StrictMonoOn.congr ?_ W_EqOn.symm) (a := ⟨_, hx⟩) trivial (b := ⟨_, hy⟩) trivial hxy)
  exact strictMonoOn_univ.2 (OrderIso.strictMono (xexpOrderIso.symm))

/--
@isnad1 id=lt.2h2v.s5.8ce6f81fd996 from=translated src=- shape=47ad1919 vocab=d255c47b
-/
lemma _root_.Tengoku.Shearertrianglefreeind.StrictMonoOn_W' (hx : xexp (-1) ≤ x) (hxy : x < y) : W x < W y :=
  StrictMonoOn_W hx (Set.mem_Ici.2 (by linarith)) hxy

/--
@isnad1 id=injon.0h0v.s4.e5a0de8e9890 from=translated src=- shape=b66f5bc5 vocab=84327b08
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_InjOn : Set.InjOn W (Set.Ici (xexp (-1))) := StrictMonoOn.injOn StrictMonoOn_W

/--
@isnad1 id=eq.1h1v.s4.77706c82f1d4 from=translated src=- shape=6def40ba vocab=a886c881
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_xexp (hx : -1 ≤ x) : W (xexp x) = x :=
  xexp_InjOn (neg_one_le_W (xexp_le hx)) hx (xexp_W (xexp_le hx))

/--
@isnad1 id=eq.0h0v.s4.4ac76c062431 from=translated src=- shape=8534b258 vocab=37d94b2b
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_xexp_neg_one : W (xexp (-1)) = -1 := W_xexp le_rfl

/--
@isnad1 id=eq.0h0v.s3.7a74f0e939fb from=translated src=- shape=3c26ae4f vocab=6685de6d
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_zero : W 0 = 0 := by
  convert W_xexp (le_of_lt neg_one_lt_zero)
  exact xexp_zero.symm

/--
@isnad1 id=lt.1h1v.s4.60cf7da2d62c from=translated src=- shape=01785d3f vocab=8c7324a5
-/
lemma _root_.Tengoku.Shearertrianglefreeind.neg_one_lt_W (hx : xexp (-1) < x) : -1 < W x := by
  rw [←W_xexp_neg_one]
  apply StrictMonoOn_W' le_rfl hx

/--
@isnad1 id=lt.1h1v.s5.0872e078c517 from=translated src=- shape=c047bf2c vocab=6a03efd0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.one_add_W_pos (hx : xexp (-1) < x) : 0 < 1 + W x :=
  neg_lt_iff_pos_add'.mp (neg_one_lt_W hx)

/--
@isnad1 id=lt.1h1v.s5.a2dae709e8e4 from=translated src=- shape=0427f1bb vocab=6a03efd0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_add_one_pos (hx : xexp (-1) < x) : 0 < W x + 1 := by
  linarith [one_add_W_pos hx ]

/--
@isnad1 id=ne.1h1v.s5.cfabac9e92e5 from=translated src=- shape=c19e32a0 vocab=6a03efd0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_add_one_nonzero (hx : xexp (-1) < x) : W x + 1 ≠ 0 :=
  (ne_of_lt (W_add_one_pos hx)).symm

/--
@isnad1 id=lt.3h3v.s6.da6fee85368c from=translated src=- shape=e7976355 vocab=2e9dc81e
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_affine_combo_pos {a b : ℝ} (hx : xexp (-1) < x) (ha : 0 < a)
    (hb : a ≤ b) : 0 < a * W x + b := by
  convert Right.add_pos_of_pos_of_nonneg
    (mul_pos ha (W_add_one_pos hx)) (sub_nonneg_of_le hb) using 1
  all_goals first | rfl | ring

/--
@isnad1 id=lt.2h1v.s5.df398da770cf from=translated src=- shape=04208c25 vocab=d255c47b
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_neg_at_neg (hx : xexp (-1) ≤ x) (hx_neg : x < 0) : W x < 0 := by
  rw [←W_zero]
  exact StrictMonoOn_W' hx hx_neg

/--
@isnad1 id=lt.1h1v.s4.0301d0d1fda3 from=translated src=- shape=35bd48ee vocab=b3a8f51c
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_pos_at_pos (hx_pos : 0 < x) : 0 < W x  := by
  rw [←W_zero]
  exact StrictMonoOn_W' (le_of_lt xexp_neg_one_neg) hx_pos

/--
@isnad1 id=ne.2h1v.s5.e86efbd44176 from=translated src=- shape=04208c25 vocab=a886c881
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_nonzero_of_nonzero (hx : xexp (-1) ≤ x) (hx_nonzero : x ≠ 0) : W x ≠ 0 := by
  rcases lt_or_gt_of_ne hx_nonzero with (h | h)
  · exact (ne_of_gt (W_neg_at_neg hx h)).symm
  · exact (ne_of_lt (W_pos_at_pos h)).symm

/--
@isnad1 id=eq.1h1v.s5.940d2de34bb8 from=translated src=- shape=ae77f64f vocab=a9b7e601
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_eq_x_mul_exp_neg_W (hx : xexp (-1) ≤ x) : W x = x * exp (- W x) := by
  nth_rewrite 2 [←xexp_W hx]
  rw [xexp, mul_assoc, ←exp_add, ←sub_eq_add_neg, sub_self, exp_zero, mul_one]

/--
@isnad1 id=lt.3h2v.s5.55524e826cd3 from=translated src=- shape=2055a4a7 vocab=d4cd4061
-/
lemma _root_.Tengoku.Shearertrianglefreeind.lt_of_xexp_lt_xexp (hx : -1 ≤ x) (hy : -1 ≤ y) (hxy : xexp x < xexp y) :
    x < y := by
  have this := StrictMonoOn_W' (xexp_le hx) hxy
  rwa [W_xexp hx, W_xexp hy] at this

/--
@isnad1 id=eq.2h1v.s5.387e7280f306 from=translated src=- shape=173a3748 vocab=8dd98e21
-/
lemma _root_.Tengoku.Shearertrianglefreeind.exp_W (hx : xexp (-1) ≤ x) (hx₀ : x ≠ 0) : exp (W x) = x / W x := by
  nth_rw 2 [←xexp_W hx]; rw [xexp]
  field_simp [W_nonzero_of_nonzero hx hx₀]

/--
@isnad1 id=continuo.0h0v.s4.891cf7064121 from=translated src=- shape=b66f5bc5 vocab=c95c9744
-/
lemma _root_.Tengoku.Shearertrianglefreeind.continuousOn_W : ContinuousOn W (Set.Ici (xexp (-1))) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact xexpOrderIso.symm.continuous.subtype_val.congr (fun a ↦ (W_coe a).symm)

noncomputable section Calculations

variable {x y : ℝ}

def _root_.Tengoku.Shearertrianglefreeind.D : Set ℝ := Set.Ici (xexp (-1))
def _root_.Tengoku.Shearertrianglefreeind.Di : Set ℝ := Set.Ioi (xexp (-1))

/--
@isnad1 id=eq.0h0v.s3.198dfa76be5f from=translated src=- shape=93ea8593 vocab=31bb047e
-/
lemma _root_.Tengoku.Shearertrianglefreeind.D_interior : interior D = Di := interior_Ici
/--
@isnad1 id=eq.0h0v.s3.ed0e89c9b04c from=translated src=- shape=93ea8593 vocab=fdce8480
-/
lemma _root_.Tengoku.Shearertrianglefreeind.Di_interior : interior Di = Di := interior_Ioi

/--
@isnad1 id=le.0h0v.s2.9cb60e35bcc3 from=translated src=- shape=836e6cbb vocab=5dda400e
-/
lemma _root_.Tengoku.Shearertrianglefreeind.Di_sub_D : Di ⊆ D := Set.Ioi_subset_Ici_self

/--
@isnad1 id=isopen.0h0v.s3.9ce59acf1400 from=translated src=- shape=25b03439 vocab=7653861a
-/
lemma _root_.Tengoku.Shearertrianglefreeind.Di_open : IsOpen Di := isOpen_Ioi

/--
@isnad1 id=mem.1h1v.s4.ce6d28f2c5f8 from=translated src=- shape=0164e9a0 vocab=e9e4b741
-/
lemma _root_.Tengoku.Shearertrianglefreeind.nonneg_mem_domain_interior (hx : 0 ≤ x) : x ∈ Di :=
  lt_of_le_of_lt' hx xexp_neg_one_neg

/--
@isnad1 id=mem.0h0v.s3.d8c9d391121a from=translated src=- shape=d52416c9 vocab=313082cf
-/
lemma _root_.Tengoku.Shearertrianglefreeind.zero_mem_domain_interior : 0 ∈ Di :=
  nonneg_mem_domain_interior (le_refl _)

/--
@isnad1 id=mem.0h0v.s3.ae8e59905f3a from=translated src=- shape=d52416c9 vocab=ab92d0b2
-/
lemma _root_.Tengoku.Shearertrianglefreeind.two_mem_domain_interior : 2 ∈ Di :=
  nonneg_mem_domain_interior (zero_le_two)

/--
@isnad1 id=mem.0h0v.s3.c35b1e9ccaab from=translated src=- shape=d52416c9 vocab=19f77bc0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.zero_mem_domain : 0 ∈ D :=
  Di_sub_D zero_mem_domain_interior

/--
@isnad1 id=mem.0h0v.s3.b5f6b8a64469 from=translated src=- shape=d52416c9 vocab=ecf06991
-/
lemma _root_.Tengoku.Shearertrianglefreeind.two_mem_domain : 2 ∈ D :=
  Di_sub_D two_mem_domain_interior

/-
## The function P := W(x)/x makes things more convenient.
-/

noncomputable def _root_.Tengoku.Shearertrianglefreeind.P : ℝ → ℝ := fun x ↦ exp (- W x)

noncomputable def _root_.Tengoku.Shearertrianglefreeind.W' : ℝ → ℝ := fun x ↦ P x / (W x + 1)
noncomputable def _root_.Tengoku.Shearertrianglefreeind.W'' : ℝ → ℝ := fun x ↦ -(W' x)^2 * (W x + 2) / (W x + 1)

noncomputable def _root_.Tengoku.Shearertrianglefreeind.P' : ℝ → ℝ  := fun x ↦ (- W' x) * P x
noncomputable def _root_.Tengoku.Shearertrianglefreeind.P'' : ℝ → ℝ := fun x ↦ (W' x)^3 * (2 * W x + 3)

/--
@isnad1 id=eq.1h1v.s4.a3456953bd45 from=translated src=- shape=3cf4adb7 vocab=d10653f8
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W_eq_self_mul_P (hx : x ∈ D) : W x = x * P x := W_eq_x_mul_exp_neg_W hx

/--
@isnad1 id=continuo.0h0v.s3.cba990113c8b from=translated src=- shape=4ce37f0a vocab=5cecb043
-/
lemma _root_.Tengoku.Shearertrianglefreeind.continuousOn_P : ContinuousOn P D := by
  unfold P
  exact Continuous.comp_continuousOn' continuous_exp (ContinuousOn.neg (continuousOn_W))

/--
@isnad1 id=lt.0h1v.s3.f72b2a1f99a5 from=translated src=- shape=8a62b088 vocab=b6ec1338
-/
lemma _root_.Tengoku.Shearertrianglefreeind.P_pos : 0 < P x := exp_pos (-W x)

/--
@isnad1 id=lt.1h1v.s4.a4295f49d644 from=translated src=- shape=a0c3e177 vocab=5034cc85
-/
lemma _root_.Tengoku.Shearertrianglefreeind.W'_pos (hx : x ∈ Di) : 0 < W' x := div_pos P_pos (W_add_one_pos hx)

/--
@isnad1 id=lt.1h1v.s4.275410209ed4 from=translated src=- shape=73ba5747 vocab=fb8120b3
-/
lemma _root_.Tengoku.Shearertrianglefreeind.P'_neg (hx : x ∈ Di) : P' x < 0 :=
  mul_neg_of_neg_of_pos (neg_neg_iff_pos.mpr (W'_pos hx)) P_pos

/--
@isnad1 id=lt.1h1v.s4.121423e1ed3e from=translated src=- shape=a0c3e177 vocab=dd054ac3
-/
lemma _root_.Tengoku.Shearertrianglefreeind.P''_pos (hx : x ∈ Di) : 0 < P'' x :=
  mul_pos (pow_pos (W'_pos hx) 3) (W_affine_combo_pos hx (by norm_num) (by norm_num))

/-!
## Integral running average.
-/

def _root_.Tengoku.Shearertrianglefreeind.IntAverage (a b : ℝ) (g : ℝ → ℝ) : ℝ :=
  if b = a then g a
  else          (⨍ y in a..b, g y)

/--
@isnad1 id=eq.0h4v.s6.5a7fcb8f1bef from=translated src=- shape=c8234496 vocab=c386dcdd
-/
lemma _root_.Tengoku.Shearertrianglefreeind.image_affine_uIcc (a b c d : ℝ) :
    (a * · + b) '' Set.uIcc c d = Set.uIcc (a * c + b) (a * d + b) := by
  suffices (· + b) '' ((a * ·) '' Set.uIcc c d) = Set.uIcc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [Set.image_const_mul_uIcc, Set.image_add_const_uIcc]

/--
@isnad1 id=continuo.0h2v.s5.a516bf08a28a from=translated src=- shape=ae70768d vocab=f898d9d3
-/
lemma _root_.Tengoku.Shearertrianglefreeind.affine_continuous (a b : ℝ) : Continuous (a * · + b) :=
  Continuous.add (continuous_const_mul _) continuous_const

/--
@isnad1 id=le.3h3v.s5.220a3f4c8627 from=translated src=- shape=4cdc88e0 vocab=53de4ddc
-/
lemma _root_.Tengoku.Shearertrianglefreeind.uIcc_sub_connected {a b : ℝ} {U : Set ℝ} (hU : IsConnected U) (ha : a ∈ U) (hb : b ∈ U) :
    Set.uIcc a b ⊆ U :=
  Set.OrdConnected.uIcc_subset (IsPreconnected.ordConnected (IsConnected.isPreconnected hU)) ha hb

/--
@isnad1 id=lt.3h4v.s5.1ed44e3b7d4a from=translated src=- shape=0a8e53ab vocab=3bf8b669
-/
lemma _root_.Tengoku.Shearertrianglefreeind.lt_mem_uIcc {a b c d : ℝ} (ha : d < a) (hb : d < b) (hc : c ∈ Set.uIcc a b) :
    d < c := by
  rw [Set.uIcc_eq_union] at hc
  rcases hc with (hc | hc) <;> linarith [hc.1]

/- To do: This lemma contains duplicated code.-/

/-
  ## Definitions of the main functions.
-/

noncomputable def _root_.Tengoku.Shearertrianglefreeind.P_prim : ℝ → ℝ  := fun x ↦ (1 / 2) * (W x)^2 + W x
def _root_.Tengoku.Shearertrianglefreeind.nG : ℝ → ℝ                    := fun x ↦ P_prim x - P_prim 2

-- Main function `G` and its derivative.
def _root_.Tengoku.Shearertrianglefreeind.G : ℝ → ℝ := fun x ↦
  if x = 2 then rexp (-W 2)
  else          ((1 / 2) * (W x)^2 + W x - ((1 / 2) * (W 2)^2 + W 2)) / (x - 2)

def _root_.Tengoku.Shearertrianglefreeind.G' : ℝ → ℝ := fun x ↦
  if x = 2 then P' 2 / 2
  else          (P x * (x - 2) - nG x) / (x - 2)^2

def _root_.Tengoku.Shearertrianglefreeind.nG' : ℝ → ℝ := fun x ↦ P x * (x - 2) - nG x
def _root_.Tengoku.Shearertrianglefreeind.dnG' : ℝ → ℝ := fun x ↦ P' x * (x - 2)
def _root_.Tengoku.Shearertrianglefreeind.ddnG' : ℝ → ℝ := fun x ↦ P'' x * (x - 2) + P' x

/--
@isnad1 id=eq.0h0v.s4.f4d93cf01990 from=translated src=- shape=32c7c386 vocab=83377be9
-/
lemma _root_.Tengoku.Shearertrianglefreeind.ddnG'_at_two : ddnG' 2 = P' 2 := by rw [ddnG', sub_self, mul_zero, zero_add]

/--
@isnad1 id=eq.1h1v.s5.2d9c2c47b5e1 from=translated src=- shape=b7863326 vocab=5a5bf81b
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G_rw (hx : x ≠ 2) : G x = nG x / (x - 2) := ite_eq_right hx
/--
@isnad1 id=eq.0h0v.s4.d034e8279f29 from=translated src=- shape=32c7c386 vocab=203cb6a3
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G_two_rw : G 2 = P 2 := ite_eq_left rfl

/--
@isnad1 id=eq.1h1v.s5.2013e22db8c0 from=translated src=- shape=54ba6666 vocab=2b3d9537
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G'_rw (hx : x ≠ 2) : G' x = (P x - G x) / (x - 2) := by
  field_simp [(sub_ne_zero_of_ne hx)]
  rw [G', ite_eq_right hx, G_rw hx]
  field_simp [(sub_ne_zero_of_ne hx)]

/--
@isnad1 id=eq.1h1v.s5.a31aea186205 from=translated src=- shape=9635532a vocab=a6250a6d
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G'_rw' (hx : x ≠ 2) : G' x = nG' x / (x - 2)^2 := ite_eq_right hx

/--
@isnad1 id=eq.0h0v.s5.7ac9f7c97c20 from=translated src=- shape=b8c91e2f vocab=232c4864
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G'_two_rw : G' 2 = P' 2 / 2 := ite_eq_left rfl

/--
@isnad1 id=eq.0h1v.s5.248075f901f1 from=translated src=- shape=6dc3a863 vocab=765cb64c
-/
lemma _root_.Tengoku.Shearertrianglefreeind.G_diff_equation : G x + (x - 2) * G' x = P x := by
  by_cases hx : x = 2
  · rw [hx, sub_self, zero_mul, add_zero, G, ite_eq_left rfl]
    rfl
  · rw [G'_rw hx, mul_div_cancel₀ _ (sub_ne_zero_of_ne hx)]
    ring

def _root_.Tengoku.Shearertrianglefreeind.G_int : ℝ → ℝ := fun t ↦ IntAverage 2 t P

/--
@isnad1 id=lt.1h1v.s5.8569f83c78b7 from=translated src=- shape=82f338a3 vocab=36246dcb
-/
lemma _root_.Tengoku.Shearertrianglefreeind.pos_of_dist_two_lt_two {x : ℝ} (hx : dist x 2 < 2) : 0 < x := by
  rw [Real.dist_eq, abs_sub_lt_iff] at hx
  linarith

open Polynomial

/-
## G' is nonpositive
-/

/--
@isnad1 id=le.2h1v.s5.792a02163acb from=translated src=- shape=c0d63451 vocab=2141aaf0
-/
lemma _root_.Tengoku.Shearertrianglefreeind.dnG'_nonnegative (hx : x ∈ Di) (hx' : x ≤ 2) : dnG' x ≥ 0 :=
  mul_nonneg_of_nonpos_of_nonpos (le_of_lt (P'_neg hx)) (tsub_nonpos.2 hx')

/--
@isnad1 id=le.2h1v.s5.21231b5c6734 from=translated src=- shape=dcdc5816 vocab=dc1513dd
-/
lemma _root_.Tengoku.Shearertrianglefreeind.dnG'_nonpositive (hx : x ∈ Di) (hx' : 2 ≤ x) : dnG' x ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (le_of_lt (P'_neg hx)) (sub_nonneg_of_le hx')

/-
## The expression we want to show is positive.
-/

def _root_.Tengoku.Shearertrianglefreeind.goal : ℝ → ℝ := fun x ↦ rexp (-x * G' x - G x) + rexp ((x - x^2) * G' x - (x + 1) * G x)

/--
@isnad1 id=lt.0h1v.s3.05baf6941b0f from=translated src=- shape=8a62b088 vocab=31051ab5
-/
lemma _root_.Tengoku.Shearertrianglefreeind.goal_pos :  0 < goal x := by
  rw [goal]
  positivity

/--
@isnad1 id=eq.1h1v.s5.48030f0590d0 from=translated src=- shape=7bd27def vocab=7943fc28
-/
lemma _root_.Tengoku.Shearertrianglefreeind.goal_rewrite (hx : x ∈ D) : goal x = rexp (-x * G' x - G x) * (1 + P x) := by
  rw [goal, mul_add, mul_one, P, ←exp_add, W_eq_self_mul_P hx]
  congr 2
  rw [←G_diff_equation]
  ring

def _root_.Tengoku.Shearertrianglefreeind.bound : ℝ → ℝ := fun x ↦ -x * G' x - G x + (2 * P x)/ (P x + 2)

def _root_.Tengoku.Shearertrianglefreeind.term₁ : ℝ → ℝ := fun x ↦ 2 * nG x - ((x - 2) * P x * (4 + W x)) / (P x + 2)

def _root_.Tengoku.Shearertrianglefreeind.term₂ : ℝ → ℝ := fun x ↦ ((P' x) * (-4 + 2 * P x + W x * P x)) / (P x + 2)^2

/--
@isnad1 id=lt.2h1v.s5.8323f0a923a7 from=translated src=- shape=ced8f88a vocab=fa3d8564
-/
lemma _root_.Tengoku.Shearertrianglefreeind.bound_is_sufficient (hx : x ∈ D) (hB : 0 < bound x) : 1 < goal x := by
  rw [←log_lt_log_iff zero_lt_one goal_pos, log_one, goal_rewrite hx,
    log_mul (exp_ne_zero _) (by linarith [@P_pos x]), log_exp]
  refine lt_trans hB ?_
  rw [bound]
  gcongr
  exact Real.lt_log_one_add_of_pos P_pos

/--
@isnad1 id=eq.0h0v.s5.fe3596d50021 from=translated src=- shape=b8c91e2f vocab=aaca8c0e
-/
lemma _root_.Tengoku.Shearertrianglefreeind.bound_two : bound 2 = term₂ 2 / 2 := by
  rw [bound, term₂, G'_two_rw, G_two_rw, P', W', W_eq_self_mul_P two_mem_domain]
  have _ : P 2 + 2      ≠ 0 := (ne_of_lt (add_pos P_pos zero_lt_two)).symm
  have _ : 2 * P 2 + 1  ≠ 0 := (ne_of_lt (add_pos (by linarith [@P_pos 2]) zero_lt_one)).symm
  field_simp
  ring

/--
@isnad1 id=eq.2h1v.s6.fc7a9dc94025 from=translated src=- shape=200b49c1 vocab=9efeb280
-/
lemma _root_.Tengoku.Shearertrianglefreeind.bound_at_not_two (hxD : x ∈ D) (hx : x ≠ 2) : bound x = term₁ x / (x - 2)^2 := by
  have _ : P x + 2  ≠ 0     := (ne_of_lt (add_pos P_pos zero_lt_two)).symm
  rw [bound, term₁, G'_rw hx, G_rw hx, W_eq_self_mul_P hxD]
  field_simp [sub_ne_zero_of_ne hx]
  ring

end Calculations
-- Tengoku: root names of this library moved to Tengoku.Shearertrianglefreeind so they do not collide with other libraries (generated)
