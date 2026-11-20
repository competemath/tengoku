import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.NormalizeTrig
import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.EntireSinc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def trigExtension (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

/--
@isnad1 id=differen.0h3v.s6.91256cc6fb12 from=translated src=- shape=2db7516a vocab=08c64dc0
-/
theorem trigExtension_entire (k : ℕ) (R : ℝ) (P : CircleFunction) :
    Differentiable ℂ (trigExtension k R P) := by
  unfold trigExtension
  fun_prop

/--
@isnad1 id=eq.1h4v.s8.08804662d6a9 from=translated src=- shape=5c8ac5cf vocab=9366c9ae
-/
theorem trigExtension_real (k : ℕ) (R : ℝ) (P : CircleFunction)
    (hP : P∈bandSpace k) (x : ℝ) :
    trigExtension k R P x=P ((Real.pi*x/R:ℝ):FourierCircle) := by
  obtain ⟨c,hc⟩ := band_expansion hP
  have hcoeff (n : ℤ) (hn : n∈Finset.Icc (-(k:ℤ)) k) : coefficient P n=c n := by
    rw [hc,coefficient_finiteFourier,ite_eq_left hn]
  rw [hc]
  unfold trigExtension
  simp only [finiteFourier_apply]
  apply sum_congr rfl
  intro n hn
  rw [←hc,hcoeff n hn,character_coe]
  congr 2
  push_cast
  ring

private theorem norm_exponential_frequency (n : ℤ) (R : ℝ) (z : ℂ) :
    ‖Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖=
      Real.exp (-(Real.pi*n/R:ℝ)*z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private theorem frequency_abs_bound {k : ℕ} {n : ℤ}
    (hn : n∈Finset.Icc (-(k:ℤ)) k) {R : ℝ} (hR : 0<R) :
    |Real.pi*n/R|≤Real.pi*k/R := by
  have hb : |(n:ℝ)|≤(k:ℝ) := by
    have := abs_le.mpr (Finset.mem_Icc.mp hn)
    exact_mod_cast this
  rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos hR]
  gcongr

private theorem card_int_band (k : ℕ) :
    (Finset.Icc (-(k:ℤ)) k).card = 2*k+1 := by
  rw [Int.card_Icc]
  omega

/-- Exponential type and a coefficient bound uniform over every normalized witness.
@isnad1 id=le.1h4v.s7.7e3b004ab46a from=translated src=- shape=912fd9fa vocab=9bb9a1f0
-/
theorem trigExtension_bound (k : ℕ) (R : ℝ) (hR : 0<R) (P : CircleFunction)
    (z : ℂ) :
    ‖trigExtension k R P z‖≤(2*k+1:ℕ)*‖P‖*
      Real.exp ((Real.pi*k/R)*|z.im|) := by
  unfold trigExtension
  apply (norm_sum_le _ _).trans
  calc
    (∑n∈Finset.Icc (-(k:ℤ)) k,
      ‖coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖)
      ≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_exponential_frequency]
        apply mul_le_mul (norm_coefficient_le P n)
        · apply Real.exp_le_exp.mpr
          calc
            -(Real.pi*n/R)*z.im≤|-(Real.pi*n/R)*z.im| := le_abs_self _
            _=|Real.pi*n/R| * |z.im| := by simp [abs_mul]
            _≤_ := mul_le_mul_of_nonneg_right (frequency_abs_bound hn hR) (abs_nonneg _)
        · positivity
        · positivity
    _=(2*k+1:ℕ)*‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

noncomputable def trigDerivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*((Real.pi*n/R:ℂ)*Complex.I)*
      Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

/--
@isnad1 id=hasderiv.0h4v.s5.94f5341d482e from=translated src=- shape=e2a556dc vocab=756e889f
-/
theorem trigExtension_derivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) :
    HasDerivAt (trigExtension k R P) (trigDerivative k R P z) z := by
  unfold trigExtension trigDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using
    (((hasDerivAt_id z).const_mul (Real.pi*n/R:ℂ)).mul_const Complex.I).cexp.const_mul
      (coefficient P n)

/--
@isnad1 id=le.1h4v.s7.f071a4bab3f2 from=translated src=- shape=325e84ce vocab=5b89e927
-/
theorem trigDerivative_real_bound (k : ℕ) (R : ℝ) (hR : 0<R)
    (P : CircleFunction) (x : ℝ) :
    ‖trigDerivative k R P x‖≤((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R) := by
  unfold trigDerivative
  apply (norm_sum_le _ _).trans
  calc
    _≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*(Real.pi*k/R) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_mul,norm_exponential_frequency]
      simp only [Complex.ofReal_im,mul_zero,Real.exp_zero,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs]
      rw [show (Real.pi*n/R:ℂ) = ((Real.pi*n/R:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (norm_coefficient_le P n) (frequency_abs_bound hn hR)
        (abs_nonneg _) (norm_nonneg _)
    _=_ := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

/--
@isnad1 id=le.1h5v.s7.bcb0b13306ea from=translated src=- shape=cf6e3b47 vocab=84a1a2f0
-/
theorem trigExtension_real_lipschitz (k : ℕ) (R : ℝ) (hR : 0<R)
    (P : CircleFunction) (x y : ℝ) :
    ‖trigExtension k R P x-trigExtension k R P y‖≤
      ((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R)*|x-y| := by
  have hd (t : ℝ) : HasDerivAt (fun u:ℝ => trigExtension k R P u)
      (trigDerivative k R P t) t := (trigExtension_derivative k R P t).comp_ofReal
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t).hasDerivWithinAt)
      (fun t ht => trigDerivative_real_bound k R hR P t)
      (convex_univ : Convex ℝ (Set.univ:Set ℝ))
      (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using hb

end Erdos1152.V5
