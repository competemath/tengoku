import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PlateauWindow
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.Periodization
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.BernsteinOperations
import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PeriodizationCircle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set MeasureTheory
open scoped BigOperators
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- This real-axis error constant uses the uniform real bound `H`, not the
nonuniform complex growth prefactor of the entire interpolant.-/
def plateauPeriodError (α τ T H : ℝ) : ℝ :=
  (2*H*α*τ)*(2/(α*(T/2-τ)))^6 * ∑' k : ℤ, sixthLatticeWeight k

/--
@isnad1 id=le.3h4v.s5.5502076d35e6 from=translated src=- shape=4b588aca vocab=b29461dc
-/
theorem plateauPeriodError_nonneg {α τ T H : ℝ}
    (hα : 0 ≤ α) (hτ : 0 ≤ τ) (hH : 0 ≤ H) :
    0 ≤ plateauPeriodError α τ T H := by
  unfold plateauPeriodError
  exact mul_nonneg (by positivity) (tsum_nonneg sixthLatticeWeight_nonneg)

/--
@isnad1 id=le.7h7v.s8.0e5253a4fecb from=translated src=- shape=0b4379b8 vocab=36fdb766
-/
theorem windowed_translate_bound {f : ℂ → ℂ} {α τ T H : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H) (x : ℝ) (hx : |x| ≤ T/2)
    (k : ℤ) (hk : k ≠ 0) :
    ‖f ((x+T*(k:ℝ) : ℝ) : ℂ) * plateauWindow α τ ((x+T*(k:ℝ) : ℝ) : ℂ)‖ ≤
      ((2*H*α*τ)*(2/(α*(T/2-τ)))^6) * sixthLatticeWeight k := by
  have hT : 0 < T := by linarith
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hh : (0 : ℤ) < |k| := abs_pos.mpr hk
    exact_mod_cast (show (1 : ℤ) ≤ |k| by omega)
  have ht : T*|(k:ℝ)| ≤ |x+T*(k:ℝ)|+|x| := by
    have hh := abs_sub_le (x+T*(k:ℝ)) 0 x
    simpa [abs_mul, abs_of_pos hT] using hh
  have hdk : (T/2-τ)/2 * (1+|(k:ℝ)|) ≤ |x+T*(k:ℝ)|-τ := by
    nlinarith [mul_nonneg hτ (sub_nonneg.mpr hk1),
      mul_nonneg hT.le (sub_nonneg.mpr hk1)]
  have hout : τ < |x+T*(k:ℝ)| := by
    have hp : 0 < (T/2-τ)/2*(1+|(k:ℝ)|) := by positivity
    linarith
  have hr : (1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ)) ≤ 2/(α*(T/2-τ)) := by
    apply (div_le_div_iff₀ (mul_pos hα (sub_pos.mpr hout))
      (mul_pos hα (sub_pos.mpr hgap))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdk hα.le]
  have hr6 := pow_le_pow_left₀ (by positivity : 0 ≤
    (1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ))) hr 6
  rw [norm_mul]
  calc
    _ ≤ H*(2*α*τ/(α*(|x+T*(k:ℝ)|-τ))^6) :=
      mul_le_mul (hf _) (norm_plateauWindow_real_tail hα hτ hout) (norm_nonneg _) hH
    _ = ((2*H*α*τ)*((1+|(k:ℝ)|)/(α*(|x+T*(k:ℝ)|-τ)))^6)*
        sixthLatticeWeight k := by
      unfold sixthLatticeWeight
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr6 (by positivity)) (sixthLatticeWeight_nonneg k)

/-- Removing the zero translate from a summable periodization.
@isnad1 id=le.3h4v.s7.79c58ad5afc6 from=translated src=- shape=d827d83d vocab=6561cfad
-/
theorem periodize_error_of_real_majorant (g : ℂ → ℂ) (T x A : ℝ)
    (hA : 0 ≤ A)
    (hs : Summable fun k : ℤ => g ((x : ℂ)+((T*(k:ℝ) : ℝ) : ℂ)))
    (hb : ∀ k : ℤ, k ≠ 0 → ‖g ((x+T*(k:ℝ) : ℝ) : ℂ)‖ ≤ A*sixthLatticeWeight k) :
    ‖periodize g T x-g x‖ ≤ A*∑' k : ℤ, sixthLatticeWeight k := by
  let r : ℤ → ℂ := fun k => if k=0 then 0 else g ((x+T*(k:ℝ) : ℝ) : ℂ)
  have hbound : ∀ k : ℤ, ‖r k‖ ≤ A*sixthLatticeWeight k := by
    intro k
    by_cases hk : k=0
    · simp only [r,hk,ite_eq_left rfl,norm_zero]
      exact mul_nonneg hA (sixthLatticeWeight_nonneg 0)
    · simpa [r,hk] using hb k hk
  have hmaj := sixthLatticeWeight_summable.mul_left A
  have hn : Summable fun k : ℤ => ‖r k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmaj
  have hsum : periodize g T x-g x=∑' k : ℤ,r k := by
    have heq := hs.tsum_eq_add_tsum_ite 0
    simp only [Int.cast_zero,mul_zero,Complex.ofReal_zero,add_zero] at heq
    have hre : (fun k : ℤ => if k=0 then 0 else g ((x:ℂ)+((T*(k:ℝ):ℝ):ℂ)))=r := by
      funext k
      simp [r]
    rw [hre] at heq
    exact eq_sub_iff_add_eq.mpr (by simpa [periodize,add_comm] using heq.symm) |>.symm
  rw [hsum]
  calc
    _ ≤ ∑' k : ℤ,‖r k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℤ,A*sixthLatticeWeight k :=
      Summable.tsum_le_tsum hbound hn hmaj
    _ = _ := tsum_mul_left

/--
@isnad1 id=le.9h8v.s7.246a2731c723 from=translated src=- shape=5414663b vocab=fbcc9bc5
-/
theorem windowed_periodize_error {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|))
    (x : ℝ) (hx : |x| ≤ T/2) :
    ‖periodize (fun z => f z*plateauWindow α τ z) T x-
      f x*plateauWindow α τ x‖ ≤ plateauPeriodError α τ T H := by
  unfold plateauPeriodError
  apply periodize_error_of_real_majorant _ T x
    ((2*H*α*τ)*(2/(α*(T/2-τ)))^6) (by positivity)
  · exact periodize_summable _
      (C := K*(2*α*τ*((2/min 1 α)*(1+τ))^6)) (σ := σ+6*α)
      (by positivity) (by positivity) (show 0 < T by linarith)
      (mul_plateauWindow_decay hα hτ hK hg) (x : ℂ)
  · intro k hk
    simpa only [Complex.ofReal_add,Complex.ofReal_mul] using
      windowed_translate_bound hα hτ hgap hH hf x hx k hk

/--
@isnad1 id=le.9h8v.s7.608020e91e89 from=translated src=- shape=3f37db2d vocab=d1ce81de
-/
theorem windowed_periodize_center_bound {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|))
    (x : ℝ) (hx : |x| ≤ T/2) :
    ‖periodize (fun z => f z*plateauWindow α τ z) T x‖ ≤
      H*(2*Real.pi)+plateauPeriodError α τ T H := by
  have he := windowed_periodize_error hα hτ hgap hH hK hσ hf hg x hx
  have hz : ‖f x*plateauWindow α τ x‖ ≤ H*(2*Real.pi) := by
    rw [norm_mul]
    exact mul_le_mul (hf x) (norm_plateauWindow_real_le hα.le hτ x) (norm_nonneg _) hH
  exact (norm_le_norm_sub_add _ _).trans (by linarith)

/--
@isnad1 id=le.3h4v.s6.f4cb06199195 from=translated src=- shape=dbcc1fef vocab=3274acf0
-/
theorem periodic_real_bound_of_center {F : ℂ → ℂ} {T B : ℝ}
    (hT : 0 < T) (hp : Function.Periodic F (T : ℂ))
    (hb : ∀ x : ℝ, |x| ≤ T/2 → ‖F x‖ ≤ B) : ∀ x : ℝ, ‖F x‖ ≤ B := by
  intro x
  let k : ℤ := ⌊(x+T/2)/T⌋
  let y : ℝ := x-(k:ℝ)*T
  have hklo : (k:ℝ)*T ≤ x+T/2 :=
    (le_div_iff₀ hT).mp (Int.floor_le ((x+T/2)/T))
  have hkhi : x+T/2 < ((k:ℝ)+1)*T :=
    (div_lt_iff₀ hT).mp (Int.lt_floor_add_one ((x+T/2)/T))
  have hy : |y| ≤ T/2 := abs_le.mpr ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
  have he : F (y : ℂ)=F x := by
    dsimp [y]
    push_cast
    exact hp.sub_int_mul_eq k
  rw [← he]
  exact hb y hy

/--
@isnad1 id=le.8h8v.s7.9161cc1532a7 from=translated src=- shape=eb812e22 vocab=d1ce81de
-/
theorem windowed_periodize_bound {f : ℂ → ℂ} {α τ T H K σ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ H)
    (hg : ∀ z : ℂ, ‖f z‖ ≤ K*Real.exp (σ*|z.im|)) :
    ∀ x : ℝ, ‖periodize (fun z => f z*plateauWindow α τ z) T x‖ ≤
      H*(2*Real.pi)+plateauPeriodError α τ T H :=
  periodic_real_bound_of_center (by linarith) (periodize_periodic _ T)
    (windowed_periodize_center_bound hα hτ hgap hH hK hσ hf hg)

/-- Dividing the desired labels by the strictly positive plateau keeps the
input data in the unit ball after one uniform scaling.
@isnad1 id=le.3h3v.s6.521344a1b041 from=translated src=- shape=7fd9af6a vocab=3fd12985
-/
theorem window_division_data {ρ r d : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ r) (hd : |d| ≤ 1) :
    |ρ*d/r| ≤ 1 := by
  have hr0 : 0 < r := hρ.trans_le hr
  rw [abs_div, abs_mul, abs_of_pos hρ, abs_of_pos hr0]
  apply (div_le_iff₀ hr0).mpr
  nlinarith

/--
@isnad1 id=eq.3h4v.s7.c325a7cf9541 from=translated src=- shape=a3e8987d vocab=5aadd23d
-/
theorem plateauPeriodError_scaled {α β r H : ℝ} (hα : α ≠ 0)
    (hβ : 1-β ≠ 0) (hr : r ≠ 0) :
    plateauPeriodError α (β*r) (2*r) H =
      (128*H*β*(∑' k : ℤ,sixthLatticeWeight k)/(α^5*(1-β)^6))/r^5 := by
  unfold plateauPeriodError
  have hd : α*(2*r/2-β*r)=α*(1-β)*r := by ring
  rw [hd]
  field_simp
  ring

/-- A fixed fractional gap between the nodes and the period seam makes the
uniform real-axis error arbitrarily small.
@isnad1 id=ex.5h4v.s6.90564ebd9102 from=translated src=- shape=9a4d08cc vocab=d5338007
-/
theorem exists_large_plateauPeriodError {α β H q : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) (hβ1 : β < 1) (hH : 0 ≤ H) (hq : 0 < q) :
    ∃ R ≥ (1 : ℝ), ∀ r ≥ R, plateauPeriodError α (β*r) (2*r) H ≤ q := by
  let A := 128*H*β*(∑' k : ℤ,sixthLatticeWeight k)/(α^5*(1-β)^6)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (mul_nonneg (by positivity) (tsum_nonneg sixthLatticeWeight_nonneg))
      (by positivity)
  refine ⟨max 1 (A/q), le_max_left _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hAr : A ≤ q*r := by
    have hh : A/q ≤ r := (le_max_right _ _).trans hr
    exact (div_le_iff₀ hq).mp hh |>.trans_eq (mul_comm _ _)
  have hrpow : r ≤ r^5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hr1 4]
  rw [plateauPeriodError_scaled hα.ne' (by linarith : 1-β ≠ 0) hr0.ne']
  change A/r^5 ≤ q
  exact (div_le_iff₀ (by positivity : 0 < r^5)).mpr
    (hAr.trans (mul_le_mul_of_nonneg_left hrpow hq.le))

/--
@isnad1 id=ex.4h8v.s7.9dc2c155c7e0 from=translated src=- shape=7c3481a1 vocab=6f70d1b0
-/
theorem exists_window_data_interpolant {ι : Type*} {α τ ρ σ H : ℝ}
    (node : ι → ℝ) (hρ : 0 < ρ)
    (hwin : ∀ i, ρ ≤ plateauWindowReal α τ (node i))
    (hinterp : ∀ d : ι → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (node i)=(d i : ℂ))
    (d : ι → ℝ) (hd : ∀ i, |d i| ≤ 1) :
    ∃ f : ℂ → ℂ, IsBernsteinFunction σ (H/ρ) f ∧
      (∀ x : ℝ, (f x).im=0) ∧
      ∀ i, f (node i)*plateauWindow α τ (node i)=(d i : ℂ) := by
  obtain ⟨f,hf,hfi⟩ := hinterp (fun i => ρ*d i/plateauWindowReal α τ (node i))
    (fun i => window_division_data hρ (hwin i) (hd i))
  let f₀ := bernsteinRealification f
  have hf₀ : IsBernsteinFunction σ H f₀ := hf.realification
  obtain ⟨hent,hreal,K,hK,hgrowth⟩ := hf₀
  refine ⟨fun z => f₀ z/(ρ:ℂ), ⟨hent.div_const _, ?_, K/ρ, by positivity, ?_⟩, ?_, ?_⟩
  · intro x
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact div_le_div_of_nonneg_right (hreal x) hρ.le
  · intro z
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    exact (div_le_div_of_nonneg_right (hgrowth z) hρ.le).trans_eq (by ring)
  · intro x
    dsimp only
    have hr : f₀ x=((f x).re : ℂ) := bernsteinRealification_real _ _
    rw [hr, ← Complex.ofReal_div]
    simp
  · intro i
    dsimp only
    have hi : f₀ (node i)=(ρ*d i/plateauWindowReal α τ (node i) : ℝ) :=
      bernsteinRealification_real_value (hfi i)
    have hw : plateauWindowReal α τ (node i) ≠ 0 := ne_of_gt (hρ.trans_le (hwin i))
    rw [hi, plateauWindow_real, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    field_simp

/-- Bounded entire interpolation yields a uniformly bounded approximate
trigonometric interpolant. The error and norm are independent of the complex
growth prefactor selected by the original interpolant.
@isnad1 id=ex.13h11v.s9.bb09831f0d6e from=translated src=- shape=cfe00e84 vocab=848a1b26
-/
theorem entire_interpolation_gives_approx_trig {ι : Type*} [Fintype ι]
    (node : ι → ℝ) {α τ T H ρ σ q : ℝ} {m : ℕ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (hgap : τ < T/2)
    (hH : 0 ≤ H) (hρ : 0 < ρ) (hσ : 0 ≤ σ) (hq : 0 ≤ q)
    (hnodes : ∀ i, |node i| ≤ τ)
    (hwin : ∀ i, ρ ≤ plateauWindowReal α τ (node i))
    (hm : periodizationBandwidth (σ+6*α) T ≤ m)
    (herror : plateauPeriodError α τ T (H/ρ) ≤ q)
    (hinterp : ∀ d : ι → ℝ, (∀ i, |d i| ≤ 1) →
      ∃ f : ℂ → ℂ, IsBernsteinFunction σ H f ∧ ∀ i, f (node i)=(d i : ℂ))
    (d : ι → ℝ) (hd : ‖d‖ ≤ 1) :
    ∃ P : CircleFunction, P ∈ bandSpace m ∧
      (∀ u : FourierCircle, (P u).im=0) ∧
      ‖P‖ ≤ (H/ρ)*(2*Real.pi)+q ∧
      ∀ i, |(P ((2*Real.pi*node i/T : ℝ) : FourierCircle)).re-d i| ≤ q := by
  have hd' : ∀ i, |d i| ≤ 1 := by
    intro i
    have hh := norm_le_pi_norm d i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hd
  obtain ⟨f,hf,hfr,hfi⟩ := exists_window_data_interpolant node hρ hwin hinterp d hd'
  obtain ⟨hfd,hfb,K,hK,hfg⟩ := hf
  have hT : 0 < T := by linarith
  have hHp : 0 ≤ H/ρ := div_nonneg hH hρ.le
  let G : ℂ → ℂ := fun z => f z*plateauWindow α τ z
  let C : ℝ := K*(2*α*τ*((2/min 1 α)*(1+τ))^6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hGd : Differentiable ℂ G := hfd.mul (differentiable_plateauWindow α τ)
  have hGg : ∀ z : ℂ, ‖G z‖ ≤ C*Real.exp ((σ+6*α)*|z.im|)/(1+‖z‖)^6 :=
    mul_plateauWindow_decay hα hτ hK.le hfg
  have hGr : ∀ x : ℝ, (G x).im=0 := by
    intro x
    dsimp [G]
    rw [plateauWindow_real,Complex.mul_im,hfr]
    simp
  obtain ⟨P,hPb,hPe⟩ := periodize_circle_of_bandwidth_le G hGd hC
    (by positivity) hT hGg hm
  refine ⟨P,hPb,?_,?_,?_⟩
  · intro u
    obtain ⟨x,rfl⟩ := normalized_circle_surjective hT.ne' u
    rw [hPe]
    exact periodize_real G hGr hC (by positivity) hT hGg x
  · apply circle_norm_le_of_physical hT.ne' (by positivity)
    intro x
    rw [hPe]
    exact (windowed_periodize_bound hα hτ hgap hHp hK.le hσ hfb hfg x).trans
      (add_le_add_right herror _)
  · intro i
    have hi := windowed_periodize_error hα hτ hgap hHp hK.le hσ hfb hfg (node i)
      ((hnodes i).trans hgap.le)
    rw [hfi i] at hi
    have hci : ‖P ((2*Real.pi*node i/T : ℝ) : FourierCircle)-(d i : ℂ)‖ ≤ q := by
      rw [hPe]
      exact hi.trans herror
    simpa only [Complex.sub_re,Complex.ofReal_re] using
      (Complex.abs_re_le_norm (P ((2*Real.pi*node i/T : ℝ) : FourierCircle)-(d i : ℂ))).trans hci

end Erdos1133
