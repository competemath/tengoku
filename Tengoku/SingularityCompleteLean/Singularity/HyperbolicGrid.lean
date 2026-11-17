import Tengoku.SingularityCompleteLean.Singularity.CayleyMetric
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Data.Int.Interval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A quantitative grid on hyperbolic balls

Scaling Euclidean coordinates by exp(R) makes every grid cell inside the
hyperbolic R-ball have hyperbolic diameter at most two. The grid has at most
49 exp(4R) cells. This deliberately coarse bound suffices for linear escape.
-/

noncomputable section
open Set
open scoped Classical UpperHalfPlane

namespace Singularity

/-- Euclidean coordinates of a point in the hyperbolic ball about i.
@isnad1 id=and.1h2v.s5.338dd4200436 from=translated src=- shape=cb4295fb vocab=b941a6d4
-/
theorem hyperbolic_ball_coordinates {z : ℍ} {R : ℝ}
    (hz : dist z UpperHalfPlane.I ≤ R) :
    Real.exp (-R) ≤ z.im ∧ z.im ≤ Real.exp R ∧ |z.re| ≤ Real.exp R := by
  have hy := UpperHalfPlane.im_le_im_mul_exp_dist z UpperHalfPlane.I
  have hl := UpperHalfPlane.im_div_exp_dist_le UpperHalfPlane.I z
  have hd := UpperHalfPlane.dist_coe_le z UpperHalfPlane.I
  simp only [UpperHalfPlane.I_im, one_mul] at hy hd
  simp only [UpperHalfPlane.I_im, one_div, ← Real.exp_neg, dist_comm UpperHalfPlane.I] at hl
  refine ⟨(Real.exp_le_exp.mpr (neg_le_neg hz)).trans hl,
    hy.trans (Real.exp_le_exp.mpr hz), ?_⟩
  have hr := Complex.abs_re_le_norm ((z : ℂ) - Complex.I)
  simp only [Complex.sub_re, UpperHalfPlane.coe_re, Complex.I_re, sub_zero] at hr
  rw [UpperHalfPlane.coe_I, dist_eq_norm] at hd
  exact (hr.trans hd).trans (by linarith [Real.exp_le_exp.mpr hz])

/-- Equal integer parts force distance at most one.
@isnad1 id=le.1h2v.s5.f322602fe720 from=translated src=- shape=acda7bba vocab=284ccfee
-/
theorem abs_sub_le_one_of_floor_eq {a b : ℝ} (h : ⌊a⌋ = ⌊b⌋) : |a - b| ≤ 1 := by
  have ha := Int.floor_le a
  have hb := Int.floor_le b
  have ha' := Int.lt_floor_add_one a
  have hb' := Int.lt_floor_add_one b
  rw [h] at ha ha'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Grid coordinates adapted to the radius R.-/
def hyperbolicGrid (R : ℝ) (z : ℍ) : ℤ × ℤ :=
  (⌊Real.exp R * z.re⌋, ⌊Real.exp R * z.im⌋)

/-- Equal cells in the radius-R ball have uniformly bounded hyperbolic diameter.
@isnad1 id=le.3h3v.s5.8bcf1072b082 from=translated src=- shape=0e787c67 vocab=e498cacf
-/
theorem hyperbolicGrid_diameter {R : ℝ} {z w : ℍ}
    (hz : dist z UpperHalfPlane.I ≤ R) (hw : dist w UpperHalfPlane.I ≤ R)
    (hcell : hyperbolicGrid R z = hyperbolicGrid R w) : dist z w ≤ 2 := by
  obtain ⟨hzlow, _, _⟩ := hyperbolic_ball_coordinates hz
  obtain ⟨hwlow, _, _⟩ := hyperbolic_ball_coordinates hw
  have coord {a b : ℝ} (h : ⌊Real.exp R * a⌋ = ⌊Real.exp R * b⌋) :
      |a - b| ≤ Real.exp (-R) := by
    have he := abs_sub_le_one_of_floor_eq h
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos R)] at he
    rw [Real.exp_neg, ← one_div]
    exact (le_div_iff₀ (Real.exp_pos R)).mpr (by simpa [mul_comm] using he)
  have hre := coord (congrArg Prod.fst hcell)
  have him := coord (congrArg Prod.snd hcell)
  have hnorm : dist (z : ℂ) (w : ℂ) ≤ 2 * Real.exp (-R) := by
    rw [dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im ((z : ℂ) - (w : ℂ))
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    linarith
  have hsqrt : Real.exp (-R) ≤ Real.sqrt (z.im * w.im) := by
    apply (Real.le_sqrt (Real.exp_pos _).le (mul_pos z.im_pos w.im_pos).le).mpr
    simpa only [pow_two] using mul_le_mul hzlow hwlow (Real.exp_pos _).le z.im_pos.le
  apply (UpperHalfPlane.dist_le_dist_coe_div_sqrt z w).trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (mul_pos z.im_pos w.im_pos))).mpr
  linarith

/-- A finite interval containing both coordinates of the radius-R grid.-/
def hyperbolicGridRange (R : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈Real.exp (2 * R)⌉ - 1) (⌈Real.exp (2 * R)⌉ + 1)

/-- The scaled coordinates have magnitude at most exp(2R).
@isnad1 id=mem.1h2v.s5.b0f9a88de5ef from=translated src=- shape=e581b575 vocab=c8d4c636
-/
theorem hyperbolicGrid_mem {R : ℝ} {z : ℍ} (hz : dist z UpperHalfPlane.I ≤ R) :
    hyperbolicGrid R z ∈ (hyperbolicGridRange R) ×ˢ (hyperbolicGridRange R) := by
  obtain ⟨_, him, hre⟩ := hyperbolic_ball_coordinates hz
  have he : Real.exp R * Real.exp R = Real.exp (2 * R) := by rw [← Real.exp_add]; congr 1; ring
  have bound {t : ℝ} (ht : |t| ≤ Real.exp R) :
      ⌊Real.exp R * t⌋ ∈ hyperbolicGridRange R := by
    have hmul : |Real.exp R * t| ≤ Real.exp (2 * R) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos R), ← he]
      exact mul_le_mul_of_nonneg_left ht (Real.exp_pos R).le
    have hceil := Int.le_ceil (Real.exp (2 * R))
    have hf := Int.floor_le (Real.exp R * t)
    have hf' := Int.lt_floor_add_one (Real.exp R * t)
    have hlo := (abs_le.mp hmul).1
    have hhi := (abs_le.mp hmul).2
    change _ ∈ Finset.Icc _ _
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast (show -(⌈Real.exp (2 * R)⌉ : ℝ) - 1 ≤ (⌊Real.exp R * t⌋ : ℝ) by linarith)
    · exact_mod_cast (show (⌊Real.exp R * t⌋ : ℝ) ≤ (⌈Real.exp (2 * R)⌉ : ℝ) + 1 by linarith)
  exact Finset.mem_product.mpr ⟨bound hre, bound (by simpa [abs_of_pos z.im_pos] using him)⟩

/-- The one-dimensional grid interval has at most 7 exp(2R) entries.
@isnad1 id=le.1h1v.s5.04bb0c152f2d from=translated src=- shape=f3b856aa vocab=7b93c8a5
-/
theorem hyperbolicGridRange_card {R : ℝ} (hR : 0 ≤ R) :
    ((hyperbolicGridRange R).card : ℝ) ≤ 7 * Real.exp (2 * R) := by
  have he : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
  have hc : (0 : ℤ) ≤ ⌈Real.exp (2 * R)⌉ := by
    exact_mod_cast (show (0 : ℝ) ≤ (⌈Real.exp (2 * R)⌉ : ℝ) from
      (Real.exp_pos _).le.trans (Int.le_ceil _))
  have hcard := Int.card_Icc_of_le (a := -⌈Real.exp (2 * R)⌉ - 1)
    (b := ⌈Real.exp (2 * R)⌉ + 1) (by omega)
  have hcard' : ((hyperbolicGridRange R).card : ℝ) = 2 * (⌈Real.exp (2 * R)⌉ : ℝ) + 3 := by
    change ((Finset.Icc (-⌈Real.exp (2 * R)⌉ - 1) (⌈Real.exp (2 * R)⌉ + 1)).card : ℝ) = _
    exact_mod_cast (show ((Finset.Icc (-⌈Real.exp (2 * R)⌉ - 1)
      (⌈Real.exp (2 * R)⌉ + 1)).card : ℤ) = 2 * ⌈Real.exp (2 * R)⌉ + 3 by omega)
  rw [hcard']
  linarith [Int.ceil_lt_add_one (Real.exp (2 * R))]

/-- The grid on a hyperbolic ball has exponentially many cells.
@isnad1 id=le.1h1v.s6.c5a607d37db4 from=translated src=- shape=ea01dccc vocab=e3438b5e
-/
theorem hyperbolicGrid_card {R : ℝ} (hR : 0 ≤ R) :
    (((hyperbolicGridRange R) ×ˢ (hyperbolicGridRange R)).card : ℝ) ≤
      49 * Real.exp (4 * R) := by
  rw [Finset.card_product, Nat.cast_mul]
  have h := hyperbolicGridRange_card hR
  have he : Real.exp (2 * R) * Real.exp (2 * R) = Real.exp (4 * R) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith [mul_le_mul h h (Nat.cast_nonneg (hyperbolicGridRange R).card) (by positivity)]

end Singularity
