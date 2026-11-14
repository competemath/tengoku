import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCharacteristic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Span one of an arbitrary lattice support implies strict characteristic-function decay. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter

theorem pmf_unit_integral_eq_of_norm_one (p : PMF ℕ) (f : ℕ → ℂ)
    (hf : ∀ k, ‖f k‖ = 1) (hm : ‖∫ k, f k ∂p.toMeasure‖ = 1) :
    ∀ k ∈ p.support, f k = ∫ j, f j ∂p.toMeasure := by
  let m := ∫ k, f k ∂p.toMeasure
  have hfi : Integrable f p.toMeasure := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable f).aestronglyMeasurable
    exact Eventually.of_forall fun k => (hf k).le
  have hgi : Integrable (fun k => star m * f k) p.toMeasure := hfi.const_mul _
  have hgnorm (k : ℕ) : ‖star m * f k‖ = 1 := by
    rw [norm_mul, norm_star, hf, hm, one_mul]
  have hstar : star m * m = 1 := by
    change starRingEnd ℂ m * m = 1
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hm]
    norm_num
  have hnonneg (k : ℕ) : 0 ≤ 1 - (star m * f k).re := by
    have h := Complex.re_le_norm (star m * f k)
    rw [hgnorm] at h
    linarith
  have hzero : ∫ k, (1 - (star m * f k).re) ∂p.toMeasure = 0 := by
    change (∫ k, (1 - RCLike.re (star m * f k)) ∂p.toMeasure) = 0
    rw [integral_sub (integrable_const (1 : ℝ)) hgi.re, integral_re hgi,
      integral_const_mul]
    change (∫ _k, (1 : ℝ) ∂p.toMeasure) - (star m * m).re = 0
    rw [hstar]
    simp
  have hae : (fun k => 1 - (star m * f k).re) =ᵐ[p.toMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg ((integrable_const _).sub hgi.re)).mp hzero
  have hnull := (ae_iff.mp hae)
  have hdis := (p.toMeasure_apply_eq_zero_iff
    (Set.to_countable _).measurableSet).mp hnull
  intro k hk
  have hkzero : 1 - (star m * f k).re = 0 := by
    by_contra he
    exact Set.disjoint_left.mp hdis hk he
  have hg : star m * f k = 1 := by
    by_contra he
    have ht := complex_re_lt_norm (z := star m * f k)
      (by simpa only [hgnorm, Complex.ofReal_one] using he)
    rw [hgnorm] at ht
    linarith
  have hmnz : star m ≠ 0 := by
    intro he
    rw [he, zero_mul] at hstar
    exact zero_ne_one hstar
  exact mul_left_cancel₀ hmnz (hg.trans hstar.symm)

def HasLatticeSpanOne (s : Set ℕ) : Prop :=
  AddSubgroup.closure {d : ℤ | ∃ j ∈ s, ∃ k ∈ s, d = (j : ℤ) - k} = ⊤

theorem hasLatticeSpanOne_of_mem_zero_one {s : Set ℕ}
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) : HasLatticeSpanOne s := by
  apply top_unique
  intro z hz
  have hone : (1 : ℤ) ∈ AddSubgroup.closure
      {d : ℤ | ∃ j ∈ s, ∃ k ∈ s, d = (j : ℤ) - k} :=
    AddSubgroup.subset_closure ⟨1, h1, 0, h0, by norm_num⟩
  simpa only [smul_eq_mul, mul_one] using (AddSubgroup.zsmul_mem _ hone z)

def latticeExponentialKernel (t : ℝ) : AddSubgroup ℤ where
  carrier := {d | Complex.exp ((d : ℂ) * (t : ℂ) * Complex.I) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change Complex.exp (((a + b : ℤ) : ℂ) * (t : ℂ) * Complex.I) = 1
    rw [Int.cast_add, add_mul, add_mul, Complex.exp_add, ha, hb, one_mul]
  neg_mem' := by
    intro a ha
    change Complex.exp (((-a : ℤ) : ℂ) * (t : ℂ) * Complex.I) = 1
    rw [Int.cast_neg, neg_mul, neg_mul, Complex.exp_neg, ha, inv_one]

theorem pmf_charFun_norm_strict_of_span_one (p : PMF ℕ)
    (hspan : HasLatticeSpanOne p.support) {t : ℝ}
    (ht0 : 0 < |t|) (htpi : |t| ≤ Real.pi) :
    ‖charFun (p.toMeasure.map (fun k : ℕ => (k : ℝ))) t‖ < 1 := by
  have : IsProbabilityMeasure (p.toMeasure.map (fun k : ℕ => (k : ℝ))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply lt_of_le_of_ne (norm_charFun_le_one t)
  intro hm
  let f : ℕ → ℂ := fun k => Complex.exp ((t : ℂ) * (k : ℂ) * Complex.I)
  have hfnorm (k : ℕ) : ‖f k‖ = 1 := by
    dsimp [f]
    simp [Complex.norm_exp]
  have hm' : ‖∫ k, f k ∂p.toMeasure‖ = 1 := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)] at hm
    simpa only [f, Complex.ofReal_natCast] using hm
  have hphase := pmf_unit_integral_eq_of_norm_one p f hfnorm hm'
  have hclosure : AddSubgroup.closure
      {d : ℤ | ∃ j ∈ p.support, ∃ k ∈ p.support, d = (j : ℤ) - k} ≤
        latticeExponentialKernel t := by
    apply (AddSubgroup.closure_le _).mpr
    rintro d ⟨j, hj, k, hk, rfl⟩
    change Complex.exp ((((j : ℤ) - k : ℤ) : ℂ) * (t : ℂ) * Complex.I) = 1
    have he : (((j : ℤ) - k : ℤ) : ℂ) * (t : ℂ) * Complex.I =
        (t : ℂ) * (j : ℂ) * Complex.I - (t : ℂ) * (k : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_sub]
    change f j / f k = 1
    rw [(hphase j hj).trans (hphase k hk).symm]
    exact div_self (Complex.exp_ne_zero _)
  rw [hspan] at hclosure
  have h1 : (1 : ℤ) ∈ latticeExponentialKernel t := hclosure (by trivial)
  have he : Complex.exp ((t : ℂ) * Complex.I) = 1 := by
    change Complex.exp (((1 : ℤ) : ℂ) * (t : ℂ) * Complex.I) = 1 at h1
    simpa only [Int.cast_one, one_mul] using h1
  exact exp_mul_I_ne_one ht0 htpi he

end PiIrrationality
