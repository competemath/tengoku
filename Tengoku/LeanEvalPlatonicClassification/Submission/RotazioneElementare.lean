import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.AngoloRiflessioni
import Tengoku.LeanEvalPlatonicClassification.Submission.OrdineTre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Se il periodo `m` del prodotto di due riflessioni è minimo, il
coefficiente angolare prodotto da `coseno_di_ordine` è coprimo con
`m`.-/
theorem coefficiente_angolare_coprimo {α β : E n}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hind : ∀ t : ℝ, β ≠ t • α)
    (m : ℕ) (hm : 2 ≤ m) (s : E n → E n)
    (hs : ∀ x, s x =
      (x - (2 * ⟪β, x⟫ : ℝ) • β) -
        (2 * ⟪α, x - (2 * ⟪β, x⟫ : ℝ) • β⟫ : ℝ) • α)
    (hord : ∀ x : E n, s^[m] x = x)
    (hmin : ∀ q : ℕ, (∀ x : E n, s^[q] x = x) → m ∣ q)
    {k : ℕ} (hklt : k < m)
    (hkcos : (⟪α, β⟫ : ℝ) = Real.cos (k * Real.pi / m) ∨
      (⟪α, β⟫ : ℝ) = -Real.cos (k * Real.pi / m)) :
    0 < k ∧ Nat.Coprime k m := by
  let c : ℝ := ⟪α, β⟫
  have hα_ne : α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hα
    norm_num at hα
  have hLI : LinearIndependent ℝ ![α, β] := by
    rw [LinearIndependent.pair_iff' hα_ne]
    intro a ha
    exact hind a ha.symm
  have hcoeff : ∀ a b : ℝ, a • α + b • β = 0 → a = 0 ∧ b = 0 := by
    exact LinearIndependent.pair_iff.mp hLI
  have hαα : (⟪α, α⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hα]
    norm_num
  have hββ : (⟪β, β⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hβ]
    norm_num
  have hβα : (⟪β, α⟫ : ℝ) = c := by
    dsimp only [c]
    exact (real_inner_comm β α).symm
  have hαβ : (⟪α, β⟫ : ℝ) = c := rfl
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := by omega
    rcases hkcos with hkcos | hkcos
    · have hc1 : (⟪α, β⟫ : ℝ) = 1 := by simpa [hkzero] using hkcos
      have hab : α = β :=
        (inner_eq_one_iff_of_norm_eq_one hα hβ).mp hc1
      exact hind 1 (by simpa using hab.symm)
    · have hcm1 : (⟪α, β⟫ : ℝ) = -1 := by simpa [hkzero] using hkcos
      have hab : α = -β :=
        (inner_eq_neg_one_iff_of_norm_eq_one hα hβ).mp hcm1
      exact hind (-1) (by rw [← neg_eq_iff_eq_neg] at hab; simpa using hab.symm)
  refine ⟨hkpos, ?_⟩
  by_cases hc : c = 0
  · have hs_two : ∀ x : E n, s^[2] x = x := by
      intro x
      rw [show s^[2] x = s (s x) by simp [Function.iterate_succ_apply']]
      rw [hs, hs]
      simp only [inner_sub_right, real_inner_smul_right, hαα, hββ,
        hβα, hαβ, hc, mul_zero, zero_smul, sub_zero]
      match_scalars <;> ring
    have hmdvd : m ∣ 2 := hmin 2 hs_two
    have hmle : m ≤ 2 := Nat.le_of_dvd (by omega) hmdvd
    have hmeq : m = 2 := by omega
    have hkeq : k = 1 := by omega
    simpa [hmeq, hkeq]
  · have hc_le : |c| ≤ 1 := by
      dsimp only [c]
      simpa [hα, hβ] using abs_real_inner_le_norm α β
    have hrad : 0 < 1 - c ^ 2 := by
      have hle : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc_le
      have hne : c ^ 2 ≠ 1 := by
        intro heq
        have heq' : c ^ 2 = (1 : ℝ) ^ 2 := by simpa using heq
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heq') with hc1 | hcm1
        · have hab : α = β :=
            (inner_eq_one_iff_of_norm_eq_one hα hβ).mp (by simpa [c] using hc1)
          exact hind 1 (by simpa using hab.symm)
        · have hab : α = -β :=
            (inner_eq_neg_one_iff_of_norm_eq_one hα hβ).mp (by simpa [c] using hcm1)
          exact hind (-1) (by rw [← neg_eq_iff_eq_neg] at hab; simpa using hab.symm)
      have hlt : c ^ 2 < 1 := lt_of_le_of_ne hle hne
      linarith
    let d0 : ℝ := Real.sqrt (1 - c ^ 2)
    have hd0pos : 0 < d0 := by
      dsimp only [d0]
      exact Real.sqrt_pos.2 hrad
    have hd0sq : d0 ^ 2 = 1 - c ^ 2 := by
      dsimp only [d0]
      exact Real.sq_sqrt hrad.le
    let T : ℝ × ℝ → ℝ × ℝ := fun p =>
      (((4 * c ^ 2 - 1) * p.1 + 2 * c * p.2),
        (-2 * c * p.1 - p.2))
    let v : ℕ → ℝ × ℝ := fun q => T^[q] (1, 0)
    let w : ℕ → ℝ × ℝ := fun q => T^[q] (0, 1)
    have hv_zero : v 0 = (1, 0) := by simp [v]
    have hw_zero : w 0 = (0, 1) := by simp [w]
    have hv_succ (q : ℕ) : v (q + 1) = T (v q) := by
      simp only [v, Function.iterate_succ_apply']
    have hw_succ (q : ℕ) : w (q + 1) = T (w q) := by
      simp only [w, Function.iterate_succ_apply']
    have hlin : ∀ a b : ℝ,
        s (a • α + b • β) =
          (((4 * c ^ 2 - 1) * a + 2 * c * b) : ℝ) • α +
          ((-2 * c * a - b : ℝ)) • β := by
      intro a b
      rw [hs (a • α + b • β)]
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right,
        hαα, hββ, hβα, hαβ]
      match_scalars <;> ring
    have hs_iter_pair : ∀ q : ℕ, ∀ a b : ℝ,
        s^[q] (a • α + b • β) =
          ((a * (v q).1 + b * (w q).1) : ℝ) • α +
          ((a * (v q).2 + b * (w q).2) : ℝ) • β := by
      intro q
      induction q with
      | zero =>
          intro a b
          simp [hv_zero, hw_zero]
      | succ q ih =>
          intro a b
          rw [Function.iterate_succ_apply', ih, hlin, hv_succ, hw_succ]
          dsimp only [T]
          match_scalars <;> ring
    have hdet : ∀ q : ℕ,
        (v q).1 * (w q).2 - (w q).1 * (v q).2 = 1 := by
      intro q
      induction q with
      | zero => simp [hv_zero, hw_zero]
      | succ q ih =>
          rw [hv_succ, hw_succ]
          dsimp only [T]
          nlinarith
    let lam : ℂ := ((2 * c ^ 2 - 1 : ℝ) : ℂ) +
      ((2 * c * d0 : ℝ) : ℂ) * Complex.I
    have hchar : lam ^ 2 - (((4 * c ^ 2 - 2 : ℝ) : ℂ) * lam) + 1 = 0 := by
      dsimp only [lam]
      have hd0sq' : (d0 : ℂ) ^ 2 = 1 - (c : ℂ) ^ 2 := by
        exact_mod_cast hd0sq
      push_cast
      ring_nf
      rw [Complex.I_sq, hd0sq']
      ring
    have hchar' : lam ^ 2 - (4 * (c : ℂ) ^ 2 - 2) * lam + 1 = 0 := by
      have hcast : (((4 * c ^ 2 - 2 : ℝ) : ℂ)) =
          4 * (c : ℂ) ^ 2 - 2 := by push_cast; ring
      rw [← hcast]
      exact hchar
    let z : ℕ → ℂ := fun q =>
      (lam + 1) * ((v q).1 : ℂ) + ((2 * c : ℝ) : ℂ) * ((v q).2 : ℂ)
    have hz_succ (q : ℕ) : z (q + 1) = lam * z q := by
      rw [show z (q + 1) =
          (lam + 1) * ((v (q + 1)).1 : ℂ) +
            ((2 * c : ℝ) : ℂ) * ((v (q + 1)).2 : ℂ) from rfl,
        hv_succ]
      change (lam + 1) *
          (((4 * c ^ 2 - 1) * (v q).1 + 2 * c * (v q).2 : ℝ) : ℂ) +
          ((2 * c : ℝ) : ℂ) *
            (((-2 * c * (v q).1 - (v q).2 : ℝ)) : ℂ) = lam * z q
      dsimp only [z]
      push_cast
      linear_combination (norm := ring) (-((v q).1 : ℂ)) * hchar'
    have hz_pow : ∀ q : ℕ, z q = lam ^ q * (lam + 1) := by
      intro q
      induction q with
      | zero => simp [z, hv_zero]
      | succ q ih =>
          rw [hz_succ, ih, pow_succ]
          ring
    let θ : ℝ := (k : ℝ) * Real.pi / (m : ℝ)
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hθpos : 0 < θ := by
      dsimp only [θ]
      positivity
    have hθlt : θ < Real.pi := by
      dsimp only [θ]
      rw [div_lt_iff₀ hmR]
      have hkR : (k : ℝ) < (m : ℝ) := by exact_mod_cast hklt
      nlinarith [Real.pi_pos]
    have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
    have hkcos' : c = Real.cos θ ∨ c = -Real.cos θ := by
      simpa only [c, θ] using hkcos
    have hc_sq_cos : c ^ 2 = Real.cos θ ^ 2 := by
      rcases hkcos' with hpos | hneg
      · rw [hpos]
      · rw [hneg]
        ring
    have hd0sin : d0 = Real.sin θ := by
      have hsq : d0 ^ 2 = Real.sin θ ^ 2 := by
        rw [hd0sq, hc_sq_cos]
        nlinarith [Real.sin_sq_add_cos_sq θ]
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
      · exact h
      · nlinarith
    have hlam :
        lam = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) ∨
        lam = Complex.exp (((-2 * θ : ℝ) : ℂ) * Complex.I) := by
      rcases hkcos' with hpos | hneg
      · left
        rw [Complex.exp_ofReal_mul_I]
        dsimp only [lam]
        rw [hpos, hd0sin, Real.cos_two_mul, Real.sin_two_mul]
        push_cast
        ring
      · right
        rw [Complex.exp_ofReal_mul_I]
        dsimp only [lam]
        rw [hneg, hd0sin, show (-2 : ℝ) * θ = -(2 * θ) by ring,
          Real.cos_neg, Real.sin_neg,
          Real.cos_two_mul, Real.sin_two_mul]
        push_cast
        ring
    rw [Nat.coprime_iff_gcd_eq_one]
    let d : ℕ := Nat.gcd k m
    have hdpos : 0 < d := by
      dsimp only [d]
      exact Nat.gcd_pos_of_pos_right k (by omega)
    by_contra hdne
    have hdgt : 1 < d := by omega
    obtain ⟨k0, hkfac⟩ := Nat.gcd_dvd_left k m
    obtain ⟨q, hqfac⟩ := Nat.gcd_dvd_right k m
    change k = d * k0 at hkfac
    change m = d * q at hqfac
    have hqpos : 0 < q := by
      by_contra hq0
      have : q = 0 := by omega
      rw [this, mul_zero] at hqfac
      omega
    have hqlt : q < m := by
      calc
        q < d * q := lt_mul_of_one_lt_left hqpos hdgt
        _ = m := hqfac.symm
    have hlamq : lam ^ q = 1 := by
      rcases hlam with hlam | hlam
      · rw [hlam, ← Complex.exp_nat_mul]
        apply Complex.exp_eq_one_iff.mpr
        refine ⟨(k0 : ℤ), ?_⟩
        dsimp only [θ]
        rw [hkfac, hqfac]
        push_cast
        have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
        have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
        field_simp [hqC, hdC]
      · rw [hlam, ← Complex.exp_nat_mul]
        apply Complex.exp_eq_one_iff.mpr
        refine ⟨-(k0 : ℤ), ?_⟩
        dsimp only [θ]
        rw [hkfac, hqfac]
        push_cast
        have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
        have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
        field_simp [hqC, hdC]
    have hzq : z q = lam + 1 := by
      rw [hz_pow, hlamq, one_mul]
    have hvq1 : (v q).1 = 1 := by
      have him := congrArg Complex.im hzq
      simp only [z, lam, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, zero_mul, mul_zero,
        add_zero, zero_add, one_mul] at him
      norm_num at him
      have hprod : 2 * c * d0 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hc) hd0pos.ne'
      exact mul_left_cancel₀ hprod (by simpa using him)
    have hvq2 : (v q).2 = 0 := by
      have hre := congrArg Complex.re hzq
      simp only [z, lam, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, zero_add] at hre
      norm_num at hre
      rw [hvq1] at hre
      have h2c : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc
      exact (mul_eq_zero.mp (by linarith : (2 * c) * (v q).2 = 0)).resolve_left h2c
    have hvq : v q = (1, 0) := by
      apply Prod.ext
      · exact hvq1
      · exact hvq2
    have hwq2 : (w q).2 = 1 := by
      have hd := hdet q
      rw [hvq1, hvq2] at hd
      linarith
    have hsq_pair : ∀ a b : ℝ,
        s^[q] (a • α + b • β) =
          ((a + b * (w q).1) : ℝ) • α + b • β := by
      intro a b
      simpa [hvq1, hvq2, hwq2] using hs_iter_pair q a b
    have hsq_iter_beta : ∀ r : ℕ,
        (s^[q])^[r] β = (((r : ℝ) * (w q).1) : ℝ) • α + β := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [Function.iterate_succ_apply', ih]
          have h := hsq_pair ((r : ℝ) * (w q).1) 1
          simpa only [one_smul, Nat.cast_add, Nat.cast_one] using h.trans (by
            match_scalars <;> ring)
    have hsqm_beta : (s^[q])^[m] β = β := by
      rw [← Function.iterate_mul]
      rw [Nat.mul_comm, Function.iterate_mul]
      exact (show Function.IsFixedPt (s^[m]) β from hord β).iterate q
    have hwq1 : (w q).1 = 0 := by
      have heq : (((m : ℝ) * (w q).1) : ℝ) • α + β = β := by
        exact (hsq_iter_beta m).symm.trans hsqm_beta
      have hzero : (((m : ℝ) * (w q).1) : ℝ) • α = 0 := by
        have := congrArg (fun y : E n => y - β) heq
        simpa using this
      have hscalar : (m : ℝ) * (w q).1 = 0 :=
        (smul_eq_zero.mp hzero).resolve_right hα_ne
      exact (mul_eq_zero.mp hscalar).resolve_left (by exact_mod_cast (by omega : m ≠ 0))
    have hadd : ∀ x y : E n, s (x + y) = s x + s y := by
      intro x y
      rw [hs, hs, hs]
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
      match_scalars <;> ring
    have hs_iter_add_fixed : ∀ r : ℕ, ∀ x u : E n, s u = u →
        s^[r] (x + u) = s^[r] x + u := by
      intro r
      induction r with
      | zero => intro x u hu; simp
      | succ r ih =>
          intro x u hu
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x u hu,
            hadd, hu]
    have hs_q_period : ∀ x : E n, s^[q] x = x := by
      intro x
      let a : ℝ := ((⟪α, x⟫ : ℝ) - c * (⟪β, x⟫ : ℝ)) / (1 - c ^ 2)
      let b : ℝ := ((⟪β, x⟫ : ℝ) - c * (⟪α, x⟫ : ℝ)) / (1 - c ^ 2)
      let u : E n := x - a • α - b • β
      have hden : 1 - c ^ 2 ≠ 0 := hrad.ne'
      have hαu : (⟪α, u⟫ : ℝ) = 0 := by
        dsimp only [u, a, b]
        simp only [inner_sub_right, real_inner_smul_right, hαα, hαβ]
        field_simp [hden]
        ring
      have hβu : (⟪β, u⟫ : ℝ) = 0 := by
        dsimp only [u, a, b]
        simp only [inner_sub_right, real_inner_smul_right, hββ, hβα]
        field_simp [hden]
        ring
      have hsu : s u = u := by
        rw [hs]
        simp [hαu, hβu]
      have hx : x = (a • α + b • β) + u := by
        dsimp only [u]
        abel
      rw [hx, hs_iter_add_fixed q (a • α + b • β) u hsu,
        hsq_pair, hwq1]
      simp
    have hmdvdq : m ∣ q := hmin q hs_q_period
    have hmleq : m ≤ q := Nat.le_of_dvd hqpos hmdvdq
    omega

/-- I segni di due normali unitari possono sempre essere scelti in modo
che il loro prodotto scalare sia non positivo.-/
theorem normali_orientabili (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (i : Fin n) (hi : (i : ℕ) + 1 < n)
    {αi pi αj pj : E n} (hαi : ‖αi‖ = 1) (hαj : ‖αj‖ = 1)
    (hri : ∀ x : E n, simpleReflection P hreg F i x = x - (2 * ⟪αi, x - pi⟫ : ℝ) • αi)
    (hrj : ∀ x : E n, simpleReflection P hreg F ⟨(i : ℕ) + 1, hi⟩ x =
      x - (2 * ⟪αj, x - pj⟫ : ℝ) • αj) :
    ∃ εi εj : ℝ, (εi = 1 ∨ εi = -1) ∧ (εj = 1 ∨ εj = -1) ∧
      ⟪εi • αi, εj • αj⟫ ≤ (0 : ℝ) := by
  by_cases h : (⟪αi, αj⟫ : ℝ) ≤ 0
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, by simpa using h⟩
  · refine ⟨1, -1, Or.inl rfl, Or.inr rfl, ?_⟩
    simp only [one_smul, neg_smul, one_smul, inner_neg_right]
    exact neg_nonpos.mpr (le_of_not_ge h)

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
