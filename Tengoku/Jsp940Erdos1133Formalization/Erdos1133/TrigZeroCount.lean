import Tengoku.Jsp940Erdos1133Formalization.Erdos1152.V5.NormalizeTrig
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Topology.Order.IntermediateValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Algebraic zero counting and exact node-factor division for finite Fourier bands.
The functions, bands and polynomial realization are the actual circle objects
from the JSP957 library; no zero-count or interpolation assertion is assumed. -/

noncomputable section
open scoped BigOperators ComplexConjugate Real
open Set Finset Polynomial
open Erdos1152.V5

namespace Erdos1133

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem character_ne_zero (j : ℤ) (x : FourierCircle) : character j x ≠ 0 := by
  have := character_norm j x
  intro h
  simp [h] at this

/-- A nonzero band-m circle function has at most 2m distinct zeros.-/
theorem band_zero_card_le {m : ℕ} {f : CircleFunction}
    (hf : f ∈ bandSpace m) (hf0 : f ≠ 0)
    (S : Finset FourierCircle) (hS : ∀ x ∈ S, f x = 0) :
    S.card ≤ 2 * m := by
  classical
  obtain ⟨p, hp, hpf⟩ := exists_polynomialCircle hf
  have hp0 : p ≠ 0 := by
    intro h
    apply hf0
    simpa [h] using hpf.symm
  have hroots : (S.image (fun x => character 1 x)).val ⊆ p.roots := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    apply (Polynomial.mem_roots hp0).mpr
    have he := hS x hx
    rw [← hpf, polynomialCircle_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (character_ne_zero _ _)
  have hcard := (Polynomial.card_le_degree_of_subset_roots hroots).trans hp
  simpa only [Finset.card_image_of_injective S character_one_injective] using hcard

/-- The ordinary monic polynomial having precisely the prescribed circle nodes.-/
def circleNodePolynomial (Γ : Finset FourierCircle) : ℂ[X] :=
  ∏ γ ∈ Γ, (Polynomial.X - Polynomial.C (character 1 γ))

/-- The centered Laurent node product; with 2N nodes it belongs to band N.
A constant phase makes this function real-valued.-/
def circleNodeProduct (N : ℕ) (Γ : Finset FourierCircle) : CircleFunction :=
  polynomialCircle N (circleNodePolynomial Γ)

@[simp] theorem circleNodeProduct_apply (N : ℕ) (Γ : Finset FourierCircle)
    (x : FourierCircle) :
    circleNodeProduct N Γ x =
      character (-(N : ℤ)) x * ∏ γ ∈ Γ, (character 1 x - character 1 γ) := by
  simp [circleNodeProduct, circleNodePolynomial, polynomialCircle_apply,
    Polynomial.eval_prod]

theorem circleNodePolynomial_monic (Γ : Finset FourierCircle) :
    (circleNodePolynomial Γ).Monic := by
  exact Polynomial.monic_prod_X_sub_C _ _

@[simp] theorem circleNodePolynomial_natDegree (Γ : Finset FourierCircle) :
    (circleNodePolynomial Γ).natDegree = Γ.card := by
  simp [circleNodePolynomial, Polynomial.natDegree_prod_of_monic,
    Polynomial.monic_X_sub_C]

theorem circleNodeProduct_band (N : ℕ) (Γ : Finset FourierCircle)
    (hΓ : Γ.card = 2 * N) : circleNodeProduct N Γ ∈ bandSpace N := by
  apply polynomialCircle_band
  simp [hΓ]

@[simp] theorem circleNodeProduct_eq_zero_iff (N : ℕ) (Γ : Finset FourierCircle)
    (x : FourierCircle) : circleNodeProduct N Γ x = 0 ↔ x ∈ Γ := by
  classical
  rw [circleNodeProduct_apply, mul_eq_zero]
  simp only [character_ne_zero, false_or, Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨γ, hγ, he⟩
    exact character_one_injective he ▸ hγ
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem circleNodePolynomial_dvd {m : ℕ} {f : CircleFunction}
    (p : ℂ[X]) (hpf : polynomialCircle m p = f)
    (Γ : Finset FourierCircle) (hfΓ : ∀ x ∈ Γ, f x = 0) :
    circleNodePolynomial Γ ∣ p := by
  classical
  unfold circleNodePolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact Polynomial.pairwise_coprime_X_sub_C character_one_injective hab
  · intro x hx
    apply Polynomial.dvd_iff_isRoot.mpr
    have he := hfΓ x hx
    rw [← hpf, polynomialCircle_apply] at he
    exact (mul_eq_zero.mp he).resolve_left (character_ne_zero _ _)

/-- Vanishing at 2N distinct circle nodes removes exactly N from each end of
the Fourier band. This is the algebraic sine-product division used in the
finite trigonometric interpolation obstruction.-/
theorem exists_band_node_quotient {m N : ℕ} (hNm : N ≤ m)
    {f : CircleFunction} (hf : f ∈ bandSpace m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (hfΓ : ∀ x ∈ Γ, f x = 0) :
    ∃ g : CircleFunction, g ∈ bandSpace (m - N) ∧
      f = circleNodeProduct N Γ * g := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, (bandSpace (m - N)).zero_mem, by simp [hf0]⟩
  obtain ⟨p, hp, hpf⟩ := exists_polynomialCircle hf
  obtain ⟨q, hpq⟩ := circleNodePolynomial_dvd p hpf Γ hfΓ
  have hp0 : p ≠ 0 := by
    intro h
    apply hf0
    simpa [h] using hpf.symm
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    simp [hpq, h]
  have hD0 := (circleNodePolynomial_monic Γ).ne_zero
  have hqd : q.natDegree ≤ 2 * (m - N) := by
    rw [hpq, Polynomial.natDegree_mul hD0 hq0,
      circleNodePolynomial_natDegree, hΓ] at hp
    omega
  refine ⟨polynomialCircle (m - N) q, polynomialCircle_band _ _ hqd, ?_⟩
  rw [← hpf, hpq]
  ext x
  simp only [circleNodeProduct, polynomialCircle_apply, ContinuousMap.mul_apply,
    Polynomial.eval_mul]
  rw [show character (-(N : ℤ)) x *
      (circleNodePolynomial Γ).eval (character 1 x) *
      (character (-((m - N : ℕ) : ℤ)) x * q.eval (character 1 x)) =
      (character (-(N : ℤ)) x * character (-((m - N : ℕ) : ℤ)) x) *
      ((circleNodePolynomial Γ).eval (character 1 x) * q.eval (character 1 x)) by ring,
    ← character_add]
  rw [show -(N : ℤ) + -((m - N : ℕ) : ℤ) = -(m : ℤ) by omega]

/-- Once the node product is rotated to the real axis, taking the real part
of its exact quotient preserves the factorization and the smaller band.-/
theorem exists_real_band_node_quotient {m N : ℕ} (hNm : N ≤ m)
    {f : CircleFunction} (hf : f ∈ bandSpace m)
    (hreal : ∀ x, (f x).im = 0)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (hfΓ : ∀ x ∈ Γ, f x = 0) (c : ℂ) (hc : c ≠ 0)
    (hphase : ∀ x, (c * circleNodeProduct N Γ x).im = 0) :
    ∃ g : CircleFunction, g ∈ bandSpace (m - N) ∧
      (∀ x, (g x).im = 0) ∧ f = (c • circleNodeProduct N Γ) * g := by
  obtain ⟨g₀, hg₀, he₀⟩ := exists_band_node_quotient hNm hf Γ hΓ hfΓ
  let g : CircleFunction := c⁻¹ • g₀
  have he : f = (c • circleNodeProduct N Γ) * g := by
    rw [he₀]
    ext x
    simp only [g, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
  have hoff : ∀ x ∉ Γ, (g x).im = 0 := by
    intro x hx
    have hP : c * circleNodeProduct N Γ x ≠ 0 :=
      mul_ne_zero hc (mt (circleNodeProduct_eq_zero_iff N Γ x).mp hx)
    have hPre : (c * circleNodeProduct N Γ x).re ≠ 0 := by
      intro hr
      apply hP
      exact Complex.ext hr (hphase x)
    have him := hreal x
    rw [he] at him
    change ((c * circleNodeProduct N Γ x) * g x).im = 0 at him
    rw [Complex.mul_im, hphase x, zero_mul, add_zero] at him
    exact (mul_eq_zero.mp him).resolve_left hPre
  refine ⟨realPartCircle g, realPart_band ((bandSpace (m - N)).smul_mem _ hg₀),
    by intro x; rfl, ?_⟩
  ext x
  by_cases hx : x ∈ Γ
  · simp only [hfΓ x hx, ContinuousMap.mul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, (circleNodeProduct_eq_zero_iff N Γ x).mpr hx, mul_zero, zero_mul]
  · have hgx : realPartCircle g x = g x := by
      apply Complex.ext
      · rfl
      · exact (hoff x hx).symm
    rw [he]
    simp only [ContinuousMap.mul_apply, hgx]

private theorem exists_zero_between_opposite (u : ℝ → ℝ) (hu : Continuous u)
    {a b : ℝ} (hab : a < b) (hsign : u a * u b < 0) :
    ∃ x ∈ Set.Ioo a b, u x = 0 := by
  rcases mul_neg_iff.mp hsign with h | h
  · exact intermediate_value_Ioo' hab.le hu.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le hu.continuousOn ⟨h.1, h.2⟩

/-- Consecutive strict sign changes of a real band-m function, in an arc of
length less than one period, number at most 2m.-/
theorem band_alternating_card_le {m k : ℕ} {f : CircleFunction}
    (hf : f ∈ bandSpace m) (hreal : ∀ x, (f x).im = 0)
    (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hspan : t (Fin.last k) - t 0 < 2 * Real.pi)
    (hsign : ∀ i : Fin k,
      (f (t i.castSucc : FourierCircle)).re * (f (t i.succ : FourierCircle)).re < 0) :
    k ≤ 2 * m := by
  classical
  by_cases hk : k = 0
  · omega
  have hu : Continuous (fun x : ℝ => (f (x : FourierCircle)).re) := by fun_prop
  have hz : ∀ i : Fin k, ∃ x ∈ Set.Ioo (t i.castSucc) (t i.succ),
      (f (x : FourierCircle)).re = 0 := by
    intro i
    exact exists_zero_between_opposite _ hu (ht (by simp)) (hsign i)
  choose z hzi hz0 using hz
  have hzmono : StrictMono z := by
    intro i j hij
    have htij : t i.succ ≤ t j.castSucc := ht.monotone (by simpa using hij)
    exact (hzi i).2.trans_le (htij.trans (hzi j).1.le)
  have hzarc (i : Fin k) : z i ∈ Set.Ico (t 0) (t 0 + 2 * Real.pi) := by
    constructor
    · exact (ht.monotone (Fin.zero_le _)).trans (hzi i).1.le
    · have hlast : t i.succ ≤ t (Fin.last k) := ht.monotone (Fin.le_last _)
      linarith [(hzi i).2]
  have hzinj : Function.Injective (fun i => (z i : FourierCircle)) := by
    intro i j he
    apply hzmono.injective
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (hzarc i) (hzarc j)).mp he
  have hf0 : f ≠ 0 := by
    intro he
    have h := hsign ⟨0, Nat.pos_of_ne_zero hk⟩
    simp [he] at h
  let S : Finset FourierCircle := Finset.univ.image (fun i => (z i : FourierCircle))
  have hS : ∀ x ∈ S, f x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply Complex.ext <;> simp [hz0 i, hreal]
  have hbound := band_zero_card_le hf hf0 S hS
  simpa [S, Finset.card_image_of_injective _ hzinj] using hbound

private theorem sub_mul_neg_of_abs_lt {a b : ℝ} (hab : |a| < |b|) :
    (a - b) * b < 0 := by
  by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg hb] at hab
    have hbpos := (abs_nonneg a).trans_lt hab
    exact mul_neg_of_neg_of_pos (sub_neg.mpr ((le_abs_self a).trans_lt hab)) hbpos
  · have hbneg : b < 0 := lt_of_not_ge hb
    rw [abs_of_neg hbneg] at hab
    have ha : b < a := by linarith [neg_abs_le a]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ha) hbneg

private theorem opposite_quotient_sign {a b p : ℝ} (hp : p ≠ 0)
    (hab : |a| < |b|) : ((a - b) / p) * (b / p) < 0 := by
  rw [div_mul_div_comm]
  exact div_neg_of_neg_of_pos (sub_mul_neg_of_abs_lt hab) (mul_self_pos.mpr hp)

private theorem opposite_preserves_alternation {u v a b : ℝ}
    (hua : u * a < 0) (hvb : v * b < 0) (hab : a * b < 0) : u * v < 0 := by
  rcases mul_neg_iff.mp hua with h | h <;>
    rcases mul_neg_iff.mp hvb with h' | h' <;>
    rcases mul_neg_iff.mp hab with h'' | h'' <;>
    nlinarith

/-- The precise finite oscillation obstruction. Values of phi divided by the
real node product alternate at k+1 peaks. An interpolant uniformly smaller at
those peaks therefore needs at least k/2 extra Fourier degrees.-/
theorem interpolant_peak_oscillations_le {m N k : ℕ} (hNm : N ≤ m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card = 2 * N)
    (φ H : CircleFunction) (hφ : φ ∈ bandSpace N) (hH : H ∈ bandSpace m)
    (hφreal : ∀ x, (φ x).im = 0) (hHreal : ∀ x, (H x).im = 0)
    (hsame : ∀ x ∈ Γ, H x = φ x)
    (c : ℂ) (hc : c ≠ 0)
    (hphase : ∀ x, (c * circleNodeProduct N Γ x).im = 0)
    (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hspan : t (Fin.last k) - t 0 < 2 * Real.pi)
    (htΓ : ∀ i, (t i : FourierCircle) ∉ Γ)
    (hsmall : ∀ i, |(H (t i : FourierCircle)).re| < |(φ (t i : FourierCircle)).re|)
    (hsign : ∀ i : Fin k,
      ((φ (t i.castSucc : FourierCircle)).re /
        (c * circleNodeProduct N Γ (t i.castSucc : FourierCircle)).re) *
      ((φ (t i.succ : FourierCircle)).re /
        (c * circleNodeProduct N Γ (t i.succ : FourierCircle)).re) < 0) :
    k ≤ 2 * (m - N) := by
  have hφm : φ ∈ bandSpace m := by
    apply spectrum_mono (s := Set.Icc (-(N : ℤ)) N)
      (t := Set.Icc (-(m : ℤ)) m) ?_ hφ
    intro j hj
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  obtain ⟨g, hg, hgreal, hfactor⟩ := exists_real_band_node_quotient hNm
    ((bandSpace m).sub_mem hH hφm)
    (by intro x; simp [hHreal, hφreal]) Γ hΓ
    (by intro x hx; simp [hsame x hx]) c hc hphase
  have hPre (i : Fin (k + 1)) :
      (c * circleNodeProduct N Γ (t i : FourierCircle)).re ≠ 0 := by
    intro he
    have hz : c * circleNodeProduct N Γ (t i : FourierCircle) = 0 :=
      Complex.ext he (hphase _)
    exact (mul_ne_zero hc (mt (circleNodeProduct_eq_zero_iff N Γ _).mp (htΓ i))) hz
  have hgvalue (i : Fin (k + 1)) :
      (g (t i : FourierCircle)).re =
        ((H (t i : FourierCircle)).re - (φ (t i : FourierCircle)).re) /
        (c * circleNodeProduct N Γ (t i : FourierCircle)).re := by
    have h := congrArg (fun F : CircleFunction => (F (t i : FourierCircle)).re) hfactor
    change (H (t i : FourierCircle) - φ (t i : FourierCircle)).re =
      ((c * circleNodeProduct N Γ (t i : FourierCircle)) * g (t i : FourierCircle)).re at h
    rw [Complex.sub_re, Complex.mul_re, hphase, zero_mul, sub_zero] at h
    apply (eq_div_iff (hPre i)).mpr
    nlinarith [h]
  apply band_alternating_card_le hg hgreal t ht hspan
  intro i
  rw [hgvalue i.castSucc, hgvalue i.succ]
  exact opposite_preserves_alternation
    (opposite_quotient_sign (hPre i.castSucc) (hsmall i.castSucc))
    (opposite_quotient_sign (hPre i.succ) (hsmall i.succ)) (hsign i)

end Erdos1133
