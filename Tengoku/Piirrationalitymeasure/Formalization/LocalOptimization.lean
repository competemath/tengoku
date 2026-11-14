import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Differential identities for the auxiliary function used in the local
optimality argument of Section 6.8.
-/

namespace PiIrrationality

noncomputable def auxiliaryH (r s g : ℝ) : ℝ → ℝ :=
  (fun _ => 1) + (fun x => r + g - x) / (fun x => -s - g + x)

/--
@isnad1 id=hasderiv.1h4v.s7.f973ad5c20d2 from=translated src=- shape=7784e829 vocab=a089ce4c
-/
theorem auxiliaryH_hasDerivAt {r s g w : ℝ}
    (hden : -s - g + w ≠ 0) :
    HasDerivAt (auxiliaryH r s g)
      (-(r - s) / (-s - g + w) ^ 2) w := by
  have hnum := (hasDerivAt_const w (r + g)).sub (hasDerivAt_id w)
  have hden' := (hasDerivAt_const w (-s - g)).add (hasDerivAt_id w)
  have hquot := hnum.div hden' hden
  have hconst := (hasDerivAt_const w (1 : ℝ)).add hquot
  have hconst' := hconst.congr_of_eventuallyEq
    (f₁ := fun x : ℝ => 1 + (r + g - x) / (-s - g + x))
    (Filter.Eventually.of_forall (fun x => by rfl))
  have hconst'' : HasDerivAt (fun x : ℝ => 1 + (r + g - x) / (-s - g + x))
      (0 + ((0 - 1) * (-s - g + w) - (r + g - w) * (0 + 1)) /
        (-s - g + w) ^ 2) w := by
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, id] using hconst'
  rw [show auxiliaryH r s g =
      (fun x : ℝ => 1 + (r + g - x) / (-s - g + x)) by
        funext x
        rfl]
  convert hconst'' using 1
  ring

/--
@isnad1 id=eq.1h4v.s7.3924378d08e8 from=translated src=- shape=524c822c vocab=8c2bf03d
-/
theorem auxiliaryH_deriv_formula {r s g w : ℝ}
    (hden : -s - g + w ≠ 0) :
    deriv (auxiliaryH r s g) w =
      -(r - s) / (-s - g + w) ^ 2 :=
  (auxiliaryH_hasDerivAt hden).deriv

/--
@isnad1 id=lt.1h4v.s6.0cb0a770b188 from=translated src=- shape=295c8b2b vocab=2e77cf20
-/
theorem auxiliaryH_denominator_sq_pos {r s g w : ℝ}
    (hden : 0 < -s - g + w) : 0 < (-s - g + w) ^ 2 := by
  positivity

/--
@isnad1 id=eq.2h5v.s7.34f6eaa7d905 from=translated src=- shape=74400405 vocab=35370068
-/
theorem auxiliaryH_sub_formula {r s g x y : ℝ}
    (hx : -s - g + x ≠ 0) (hy : -s - g + y ≠ 0) :
    auxiliaryH r s g y - auxiliaryH r s g x =
      -(r - s) * (y - x) /
        ((-s - g + y) * (-s - g + x)) := by
  simp only [auxiliaryH, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.one_apply]
  field_simp [hx, hy]
  ring

/--
@isnad1 id=lt.5h7v.s6.e365f5fbcbc5 from=translated src=- shape=60230214 vocab=5d64efbe
-/
theorem auxiliaryH_strictAntiOn {r s g l u : ℝ}
    (hrs : s < r)
    (hden : ∀ w ∈ Set.Ioo l u, 0 < -s - g + w) :
    ∀ ⦃x y : ℝ⦄, x ∈ Set.Ioo l u → y ∈ Set.Ioo l u → x < y →
      auxiliaryH r s g y < auxiliaryH r s g x := by
  intro x y hx hy hxy
  have hxden : 0 < -s - g + x := hden x hx
  have hyden : 0 < -s - g + y := hden y hy
  have hsub := auxiliaryH_sub_formula (r := r) (s := s) (g := g)
    (x := x) (y := y) hxden.ne' hyden.ne'
  have hnum : 0 < (r - s) * (y - x) := mul_pos (sub_pos.mpr hrs) (sub_pos.mpr hxy)
  have hdenpos : 0 < (-s - g + y) * (-s - g + x) := mul_pos hyden hxden
  have hquot : 0 < (r - s) * (y - x) /
      ((-s - g + y) * (-s - g + x)) := div_pos hnum hdenpos
  apply sub_lt_zero.mp
  rw [hsub]
  convert neg_lt_zero.mpr hquot using 1 <;> ring

/--
@isnad1 id=eq.0h5v.s6.db981753e1d6 from=translated src=- shape=62ababed vocab=23b39d30
-/
theorem auxiliaryBound_eq_auxiliaryH
    (r s G phi : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    AuxiliaryBound r s (fun x => G x - phi x) p =
      auxiliaryH (r p) (s p) (G p) (phi p) := by
  unfold AuxiliaryBound auxiliaryH
  simp
  ring

/--
@isnad1 id=strictlo.4h6v.s7.e5793803e801 from=translated src=- shape=2f93296c vocab=00b7898c
-/
theorem strictLocalMinimizer_of_quadratic_lower_bound
    (f : ℝ × ℝ → ℝ) (domain : ℝ × ℝ → Prop) (p0 : ℝ × ℝ)
    {kappa C rho : ℝ} (hkappa : 0 < kappa) (hC : 0 ≤ C) (hrho : 0 < rho)
    (hbound : ∀ p : ℝ × ℝ, domain p → p ≠ p0 → ‖p - p0‖ < rho →
      f p0 + kappa * ‖p - p0‖ - C * ‖p - p0‖ ^ 2 ≤ f p) :
    StrictLocalMinimizer f domain p0 := by
  let delta : ℝ := min rho (kappa / (2 * (C + 1)))
  have hden : 0 < 2 * (C + 1) := by positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  refine ⟨delta, hdelta, ?_⟩
  intro p hpdom hpp0 hdist
  have hdistpos : 0 < ‖p - p0‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hpp0)
  have hsmall : ‖p - p0‖ < kappa / (2 * (C + 1)) := by
    simpa [delta] using (lt_of_lt_of_le hdist (min_le_right _ _))
  have hscaled : ‖p - p0‖ * (2 * (C + 1)) < kappa :=
    (lt_div_iff₀ hden).mp hsmall
  have hcr : C * ‖p - p0‖ < kappa := by
    nlinarith [hscaled, hdistpos]
  have hquad : 0 < kappa * ‖p - p0‖ - C * ‖p - p0‖ ^ 2 := by
    have hprod : 0 < ‖p - p0‖ * (kappa - C * ‖p - p0‖) :=
      mul_pos hdistpos (sub_pos.mpr hcr)
    nlinarith [hprod]
  have hdistrho : ‖p - p0‖ < rho := by
    simpa [delta] using (lt_of_lt_of_le hdist (min_le_left _ _))
  have hb := hbound p hpdom hpp0 hdistrho
  linarith

end PiIrrationality
