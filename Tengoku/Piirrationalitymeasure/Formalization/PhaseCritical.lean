import Tengoku.Piirrationalitymeasure.Formalization.ArcPhase
import Tengoku.Piirrationalitymeasure.Formalization.PhaseRootCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Existence and uniqueness of the phase critical point on the controlled arc.
-/

namespace PiIrrationality

/--
@isnad1 id=continuo.0h1v.s4.5e895b6443fa from=translated src=- shape=f736e2c1 vocab=0448e22c
-/
theorem arcPhaseNumerator_continuous (e : ℝ) : Continuous (arcPhaseNumerator e) := by
  unfold arcPhaseNumerator
  fun_prop

/--
@isnad1 id=eq.6h3v.s6.63ce544c58fd from=translated src=- shape=5b8ec1ab vocab=6b6b5661
-/
theorem arcPhaseNumerator_root_unique {e x y : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1)
    (hx : x ∈ Set.Ioo 0 1) (hy : y ∈ Set.Ioo 0 1)
    (hpx : arcPhaseNumerator e x = 0) (hpy : arcPhaseNumerator e y = 0) : x = y := by
  have hdenx := sub_pos.mpr hx.2
  have hdeny := sub_pos.mpr hy.2
  have hdiv := phaseTransformedPolynomial_positive_root_unique he he1
    (div_pos hx.1 hdenx) (div_pos hy.1 hdeny)
    ((arcPhaseNumerator_zero_iff hx.1 hx.2).mp hpx)
    ((arcPhaseNumerator_zero_iff hy.1 hy.2).mp hpy)
  have hcross := (div_eq_div_iff hdenx.ne' hdeny.ne').mp hdiv
  nlinarith

/--
@isnad1 id=existsun.2h1v.s6.c0ceb60d8ed0 from=translated src=- shape=3e2fd4a7 vocab=1fe60cc7
-/
theorem arcPhaseNumerator_unique_root {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    ∃! lambda : ℝ, lambda ∈ Set.Ioo 0 1 ∧ arcPhaseNumerator e lambda = 0 := by
  have h0 : 0 < arcPhaseNumerator e 0 := by
    rw [arcPhaseNumerator_at_zero]
    exact phaseC0_pos he
  have h1 : arcPhaseNumerator e 1 < 0 := by
    rw [arcPhaseNumerator_at_one]
    exact phaseC6_neg e
  obtain ⟨lambda, hl, hroot⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    (arcPhaseNumerator_continuous e).continuousOn ⟨h1.le, h0.le⟩
  have hl0 : 0 < lambda := by
    by_contra h
    have hz : lambda = 0 := by linarith [hl.1]
    rw [hz] at hroot
    linarith
  have hl1 : lambda < 1 := by
    by_contra h
    have hz : lambda = 1 := by linarith [hl.2]
    rw [hz] at hroot
    linarith
  refine ⟨lambda, ⟨⟨hl0, hl1⟩, hroot⟩, ?_⟩
  intro y hy
  exact arcPhaseNumerator_root_unique he he1 hy.1 ⟨hl0, hl1⟩ hy.2 hroot

/--
@isnad1 id=existsun.2h1v.s7.277e9f85303e from=translated src=- shape=51911295 vocab=c805a670
-/
theorem complexPhase_on_arc_unique_critical {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    ∃! lambda : ℝ, lambda ∈ Set.Ioo 0 1 ∧
      deriv (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t)) lambda = 0 := by
  obtain ⟨lambda, hl, huniq⟩ := arcPhaseNumerator_unique_root he he1
  refine ⟨lambda, ⟨hl.1, (complexPhase_on_arc_deriv_zero_iff he hl.1.1 hl.1.2).mpr hl.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, (complexPhase_on_arc_deriv_zero_iff he hy.1.1 hy.1.2).mp hy.2⟩

/--
@isnad1 id=lt.6h3v.s6.b9963c9cd987 from=translated src=- shape=6ad94086 vocab=6b6b5661
-/
theorem arcPhaseNumerator_pos_left {e lambda x : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcPhaseNumerator e lambda = 0)
    (hx0 : 0 < x) (hxl : x < lambda) : 0 < arcPhaseNumerator e x := by
  by_contra h
  have hx : arcPhaseNumerator e x ≤ 0 := le_of_not_gt h
  have h0 : 0 < arcPhaseNumerator e 0 := by
    rw [arcPhaseNumerator_at_zero]
    exact phaseC0_pos he
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx0.le
    (arcPhaseNumerator_continuous e).continuousOn ⟨hx, h0.le⟩
  have hz0 : 0 < z := by
    by_contra h
    have hz' : z = 0 := by linarith [hz.1]
    rw [hz'] at hzero
    linarith
  have hzl : z = lambda :=
    arcPhaseNumerator_root_unique he he1 ⟨hz0, by linarith [hz.2, hl.2]⟩ hl hzero hroot
  linarith [hz.2]

/--
@isnad1 id=lt.6h3v.s6.2d04754eb3e6 from=translated src=- shape=9de7f594 vocab=6b6b5661
-/
theorem arcPhaseNumerator_neg_right {e lambda x : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcPhaseNumerator e lambda = 0)
    (hlx : lambda < x) (hx1 : x < 1) : arcPhaseNumerator e x < 0 := by
  by_contra h
  have hx : 0 ≤ arcPhaseNumerator e x := le_of_not_gt h
  have h1 : arcPhaseNumerator e 1 < 0 := by
    rw [arcPhaseNumerator_at_one]
    exact phaseC6_neg e
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' hx1.le
    (arcPhaseNumerator_continuous e).continuousOn ⟨h1.le, hx⟩
  have hz1 : z < 1 := by
    by_contra h
    have hz' : z = 1 := by linarith [hz.2]
    rw [hz'] at hzero
    linarith
  have hzl : z = lambda :=
    arcPhaseNumerator_root_unique he he1 ⟨by linarith [hz.1, hl.1], hz1⟩ hl hzero hroot
  linarith [hz.1]

/--
@isnad1 id=lt.3h2v.s7.e4a273ecae1e from=translated src=- shape=fa377ed2 vocab=e47993c5
-/
theorem complexPhase_on_arc_deriv_pos {e x : ℝ}
    (he : (9 : ℝ) / 10 < e) (hx : x ∈ Set.Ioo 0 1)
    (hQ : 0 < arcPhaseNumerator e x) :
    0 < deriv (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t)) x := by
  have h := twice_complexPhase_deriv_cleared he hx.1 hx.2
  rw [(hasDerivAt_twice_complexPhase_on_arc _ _ he hx.1 hx.2).deriv] at h
  have hfactor : 0 < (125 : ℝ) / 557 * (1 + e ^ 2) := by positivity
  have hp : 0 < x * (1 - x) * arcD e x * arcH e x * arcJ e x *
      arcLogPhaseDerivative (1857 / 5570) (3714 / 5570) e x := by
    rw [h]
    exact mul_pos hfactor hQ
  have hd := (mul_pos_iff_of_pos_left (arc_derivative_denominator_pos he hx.1 hx.2)).mp hp
  rw [(hasDerivAt_complexPhase_on_arc _ _ he hx.1 hx.2).deriv]
  exact div_pos hd (by norm_num)

/--
@isnad1 id=lt.3h2v.s7.a37125fdd94f from=translated src=- shape=66c9079d vocab=e47993c5
-/
theorem complexPhase_on_arc_deriv_neg {e x : ℝ}
    (he : (9 : ℝ) / 10 < e) (hx : x ∈ Set.Ioo 0 1)
    (hQ : arcPhaseNumerator e x < 0) :
    deriv (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t)) x < 0 := by
  have h := twice_complexPhase_deriv_cleared he hx.1 hx.2
  rw [(hasDerivAt_twice_complexPhase_on_arc _ _ he hx.1 hx.2).deriv] at h
  have hfactor : 0 < (125 : ℝ) / 557 * (1 + e ^ 2) := by positivity
  have hp : x * (1 - x) * arcD e x * arcH e x * arcJ e x *
      arcLogPhaseDerivative (1857 / 5570) (3714 / 5570) e x < 0 := by
    rw [h]
    exact mul_neg_of_pos_of_neg hfactor hQ
  have hd := neg_of_mul_neg_right hp (arc_derivative_denominator_pos he hx.1 hx.2).le
  rw [(hasDerivAt_complexPhase_on_arc _ _ he hx.1 hx.2).deriv]
  exact div_neg_of_neg_of_pos hd (by norm_num)

/--
@isnad1 id=lt.6h3v.s7.83c8b37b30e0 from=translated src=- shape=40df1f08 vocab=4cd4494b
-/
theorem complexPhase_on_arc_strict_max_of_root {e lambda : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1)
    (hl : lambda ∈ Set.Ioo 0 1) (hroot : arcPhaseNumerator e lambda = 0) :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≠ lambda →
      complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e x) <
        complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e lambda) := by
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hxl | hlx
  · have hmono : StrictMonoOn
        (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t))
        (Set.Icc x lambda) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x lambda)
      · intro t ht
        exact (hasDerivAt_complexPhase_on_arc _ _ he (lt_of_lt_of_le hx.1 ht.1)
          (lt_of_le_of_lt ht.2 hl.2)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact complexPhase_on_arc_deriv_pos he ⟨hx.1.trans ht.1, ht.2.trans hl.2⟩
          (arcPhaseNumerator_pos_left he he1 hl hroot (hx.1.trans ht.1) ht.2)
    exact hmono ⟨le_rfl, hxl.le⟩ ⟨hxl.le, le_rfl⟩ hxl
  · have hanti : StrictAntiOn
        (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t))
        (Set.Icc lambda x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc lambda x)
      · intro t ht
        exact (hasDerivAt_complexPhase_on_arc _ _ he (lt_of_lt_of_le hl.1 ht.1)
          (lt_of_le_of_lt ht.2 hx.2)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact complexPhase_on_arc_deriv_neg he ⟨hl.1.trans ht.1, ht.2.trans hx.2⟩
          (arcPhaseNumerator_neg_right he he1 hl hroot ht.1 (ht.2.trans hx.2))
    exact hanti ⟨le_rfl, hlx.le⟩ ⟨hlx.le, le_rfl⟩ hlx

/--
@isnad1 id=existsun.2h1v.s8.ab78e8bbb945 from=translated src=- shape=91f1f588 vocab=c805a670
-/
theorem complexPhase_on_arc_unique_maximum {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    ∃! lambda : ℝ, lambda ∈ Set.Ioo 0 1 ∧
      deriv (fun t => complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e t)) lambda = 0 ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≠ lambda →
        complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e x) <
          complexPhase (1857 / 5570) (3714 / 5570) (gammaPath e lambda) := by
  obtain ⟨lambda, hl, huniq⟩ := arcPhaseNumerator_unique_root he he1
  refine ⟨lambda, ⟨hl.1, ?_, complexPhase_on_arc_strict_max_of_root he he1 hl.1 hl.2⟩, ?_⟩
  · exact (complexPhase_on_arc_deriv_zero_iff he hl.1.1 hl.1.2).mpr hl.2
  · intro y hy
    exact huniq y ⟨hy.1, (complexPhase_on_arc_deriv_zero_iff he hy.1.1 hy.1.2).mp hy.2.1⟩

end PiIrrationality
