import Tengoku.Piirrationalitymeasure.Formalization.ArcTransform
import Tengoku.Piirrationalitymeasure.Formalization.PhaseSignPattern

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A unique phase maximum from the transformed numerator's strict sign pattern. -/

namespace PiIrrationality

/--
@isnad1 id=continuo.0h2v.s4.1bc7a40cf321 from=translated src=- shape=7c0c7130 vocab=e0e464ad
-/
theorem arcClearedDerivative_continuous (p : ℝ × ℝ) (e : ℝ) :
    Continuous (arcClearedDerivative p.1 p.2 e) := by
  unfold arcClearedDerivative arcD arcH arcJ arcDderiv arcHderiv arcJderiv
  fun_prop

/--
@isnad1 id=lt.2h2v.s6.ae41b93b52d5 from=translated src=- shape=b55c7dc9 vocab=e52eec04
-/
theorem arcClearedDerivative_pos_zero {p : ℝ × ℝ} {e : ℝ}
    (ha : 0 < p.1) (he : (9 : ℝ) / 10 < e) :
    0 < arcClearedDerivative p.1 p.2 e 0 := by
  have h := mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) ha)
    (arcD_pos e 0)) (arcH_pos (lambda := 0) he (by norm_num) (by norm_num)))
      (arcJ_pos (lambda := 0) he (by norm_num) (by norm_num))
  simpa only [arcClearedDerivative, sub_zero, mul_one, mul_zero, zero_mul, sub_zero,
    add_zero] using h

/--
@isnad1 id=lt.2h2v.s6.e7326a8b23c3 from=translated src=- shape=b2254fa1 vocab=e52eec04
-/
theorem arcClearedDerivative_neg_one {p : ℝ × ℝ} {e : ℝ}
    (hb : 0 < p.2) (he : (9 : ℝ) / 10 < e) :
    arcClearedDerivative p.1 p.2 e 1 < 0 := by
  have h := mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hb)
    (arcD_pos e 1)) (arcH_pos (lambda := 1) he (by norm_num) (by norm_num)))
      (arcJ_pos (lambda := 1) he (by norm_num) (by norm_num))
  simpa only [arcClearedDerivative, sub_self, mul_one, mul_zero, zero_mul,
    zero_sub, add_zero, sub_zero] using neg_lt_zero.mpr h

/--
@isnad1 id=eq.5h4v.s6.90462b930093 from=translated src=- shape=6df6eb51 vocab=ed6e07ab
-/
theorem arcClearedDerivative_root_unique {p : ℝ × ℝ} {e x y : ℝ}
    (hs : PhaseCoefficientSigns (parameterPhasePolynomial p e))
    (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1)
    (hpx : arcClearedDerivative p.1 p.2 e x = 0)
    (hpy : arcClearedDerivative p.1 p.2 e y = 0) : x = y := by
  have hdx := sub_pos.mpr hx.2
  have hdy := sub_pos.mpr hy.2
  have hdiv := hs.positive_root_unique (parameterPhasePolynomial_degree_le p e)
    (div_pos hx.1 hdx) (div_pos hy.1 hdy)
    ((parameterPhasePolynomial_zero_iff hx.1 hx.2).mp hpx)
    ((parameterPhasePolynomial_zero_iff hy.1 hy.2).mp hpy)
  have hcross := (div_eq_div_iff hdx.ne' hdy.ne').mp hdiv
  nlinarith

/--
@isnad1 id=lt.7h4v.s7.52f9f98a5c30 from=translated src=- shape=a71be0f7 vocab=c570338f
-/
theorem arcClearedDerivative_pos_left {p : ℝ × ℝ} {e lambda x : ℝ}
    (hs : PhaseCoefficientSigns (parameterPhasePolynomial p e))
    (ha : 0 < p.1) (he : (9 : ℝ) / 10 < e)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcClearedDerivative p.1 p.2 e lambda = 0)
    (hx0 : 0 < x) (hxl : x < lambda) : 0 < arcClearedDerivative p.1 p.2 e x := by
  by_contra h
  have hx := le_of_not_gt h
  have h0 := arcClearedDerivative_pos_zero ha he
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx0.le
    (arcClearedDerivative_continuous p e).continuousOn ⟨hx, h0.le⟩
  have hz0 : 0 < z := by
    by_contra h
    have hz' : z = 0 := by linarith [hz.1]
    rw [hz'] at hzero
    linarith
  have hzl := arcClearedDerivative_root_unique hs
    ⟨hz0, by linarith [hz.2, hl.2]⟩ hl hzero hroot
  linarith [hz.2]

/--
@isnad1 id=lt.7h4v.s7.235946c193c0 from=translated src=- shape=b1ace182 vocab=c570338f
-/
theorem arcClearedDerivative_neg_right {p : ℝ × ℝ} {e lambda x : ℝ}
    (hs : PhaseCoefficientSigns (parameterPhasePolynomial p e))
    (hb : 0 < p.2) (he : (9 : ℝ) / 10 < e)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcClearedDerivative p.1 p.2 e lambda = 0)
    (hlx : lambda < x) (hx1 : x < 1) : arcClearedDerivative p.1 p.2 e x < 0 := by
  by_contra h
  have hx := le_of_not_gt h
  have h1 := arcClearedDerivative_neg_one hb he
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx1.le
    (arcClearedDerivative_continuous p e).continuousOn ⟨h1.le, hx⟩
  have hz1 : z < 1 := by
    by_contra h
    have hz' : z = 1 := by linarith [hz.2]
    rw [hz'] at hzero
    linarith
  have hzl := arcClearedDerivative_root_unique hs
    ⟨by linarith [hz.1, hl.1], hz1⟩ hl hzero hroot
  linarith [hz.1]

/--
@isnad1 id=iff.2h3v.s7.42def5c1f3ec from=translated src=- shape=55d578f7 vocab=a41e33d0
-/
theorem general_complexPhase_arc_deriv_zero_iff {p : ℝ × ℝ} {e x : ℝ}
    (he : (9 : ℝ) / 10 < e) (hx : x ∈ Set.Ioo 0 1) :
    deriv (fun t => complexPhase p.1 p.2 (gammaPath e t)) x = 0 ↔
      arcClearedDerivative p.1 p.2 e x = 0 := by
  rw [(hasDerivAt_complexPhase_on_arc p.1 p.2 he hx.1 hx.2).deriv]
  have h := arcLogPhaseDerivative_cleared p.1 p.2 he hx.1 hx.2
  have hz := congrArg (fun v : ℝ => v = 0) h
  have hd := (arc_derivative_denominator_pos he hx.1 hx.2).ne'
  simpa only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, mul_eq_zero,
    hd, false_or] using hz.to_iff

/--
@isnad1 id=lt.3h3v.s7.cc68f3082cd8 from=translated src=- shape=01e9f3e5 vocab=a41e33d0
-/
theorem general_complexPhase_arc_deriv_pos {p : ℝ × ℝ} {e x : ℝ}
    (he : (9 : ℝ) / 10 < e) (hx : x ∈ Set.Ioo 0 1)
    (hQ : 0 < arcClearedDerivative p.1 p.2 e x) :
    0 < deriv (fun t => complexPhase p.1 p.2 (gammaPath e t)) x := by
  have h := arcLogPhaseDerivative_cleared p.1 p.2 he hx.1 hx.2
  have hp : 0 < x * (1 - x) * arcD e x * arcH e x * arcJ e x *
      arcLogPhaseDerivative p.1 p.2 e x := by rw [h]; exact hQ
  have hd := (mul_pos_iff_of_pos_left (arc_derivative_denominator_pos he hx.1 hx.2)).mp hp
  rw [(hasDerivAt_complexPhase_on_arc p.1 p.2 he hx.1 hx.2).deriv]
  exact div_pos hd (by norm_num)

/--
@isnad1 id=lt.3h3v.s7.c4952169e24d from=translated src=- shape=80da3055 vocab=a41e33d0
-/
theorem general_complexPhase_arc_deriv_neg {p : ℝ × ℝ} {e x : ℝ}
    (he : (9 : ℝ) / 10 < e) (hx : x ∈ Set.Ioo 0 1)
    (hQ : arcClearedDerivative p.1 p.2 e x < 0) :
    deriv (fun t => complexPhase p.1 p.2 (gammaPath e t)) x < 0 := by
  have h := arcLogPhaseDerivative_cleared p.1 p.2 he hx.1 hx.2
  have hp : x * (1 - x) * arcD e x * arcH e x * arcJ e x *
      arcLogPhaseDerivative p.1 p.2 e x < 0 := by rw [h]; exact hQ
  have hd := neg_of_mul_neg_right hp (arc_derivative_denominator_pos he hx.1 hx.2).le
  rw [(hasDerivAt_complexPhase_on_arc p.1 p.2 he hx.1 hx.2).deriv]
  exact div_neg_of_neg_of_pos hd (by norm_num)

/--
@isnad1 id=lt.8h4v.s7.88cef58ddba7 from=translated src=- shape=1250ad55 vocab=10f173b3
-/
theorem general_complexPhase_arc_strict_max {p : ℝ × ℝ} {e lambda : ℝ}
    (hs : PhaseCoefficientSigns (parameterPhasePolynomial p e))
    (ha : 0 < p.1) (hb : 0 < p.2) (he : (9 : ℝ) / 10 < e)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcClearedDerivative p.1 p.2 e lambda = 0) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≠ lambda →
      complexPhase p.1 p.2 (gammaPath e x) < complexPhase p.1 p.2 (gammaPath e lambda) := by
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hxl | hlx
  · have hmono : StrictMonoOn (fun t => complexPhase p.1 p.2 (gammaPath e t))
        (Set.Icc x lambda) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x lambda)
      · intro t ht
        exact (hasDerivAt_complexPhase_on_arc _ _ he (lt_of_lt_of_le hx.1 ht.1)
          (lt_of_le_of_lt ht.2 hl.2)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact general_complexPhase_arc_deriv_pos he ⟨hx.1.trans ht.1, ht.2.trans hl.2⟩
          (arcClearedDerivative_pos_left hs ha he hl hroot (hx.1.trans ht.1) ht.2)
    exact hmono ⟨le_rfl, hxl.le⟩ ⟨hxl.le, le_rfl⟩ hxl
  · have hanti : StrictAntiOn (fun t => complexPhase p.1 p.2 (gammaPath e t))
        (Set.Icc lambda x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc lambda x)
      · intro t ht
        exact (hasDerivAt_complexPhase_on_arc _ _ he (lt_of_lt_of_le hl.1 ht.1)
          (lt_of_le_of_lt ht.2 hx.2)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact general_complexPhase_arc_deriv_neg he ⟨hl.1.trans ht.1, ht.2.trans hx.2⟩
          (arcClearedDerivative_neg_right hs hb he hl hroot ht.1 (ht.2.trans hx.2))
    exact hanti ⟨le_rfl, hlx.le⟩ ⟨hlx.le, le_rfl⟩ hlx

end PiIrrationality
