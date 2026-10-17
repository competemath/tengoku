import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.Clipping

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
@isnad1 id=cofinite.0h1v.s5.55773454586e from=translated src=- shape=f787e61f vocab=6f273a99
-/
lemma cofinite_top : Cofinite (⊤ : Submodule ℝ X) := by
  refine ⟨?_, inferInstance⟩
  simpa only [Submodule.top_coe] using isClosed_univ (X := X)

/--
@isnad1 id=nontrivi.2h2v.s6.63f4a5624082 from=translated src=- shape=11235a9c vocab=8f1fca2e
-/
lemma cofinite_nontrivial (hinf : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X}
    (hF : Cofinite F) : Nontrivial F := by
  by_contra hn
  have : Subsingleton F := not_nontrivial_iff_subsingleton.mp hn
  have : FiniteDimensional ℝ (X ⧸ F) := hF.2
  exact hinf (Module.Finite.of_submodule_quotient F)

/--
@isnad1 id=ex.2h2v.s7.a38c51db160c from=translated src=- shape=983f884b vocab=0c86aa09
-/
lemma cofinite_has_unit (hinf : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X}
    (hF : Cofinite F) : ∃ y ∈ F, ‖y‖ = 1 := by
  have : Nontrivial F := cofinite_nontrivial hinf hF
  obtain ⟨y, hy⟩ := exists_norm_eq F (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨y, y.property, hy⟩

/--
@isnad1 id=le.2h4v.s8.84014ef96408 from=translated src=- shape=8e5c3650 vocab=c5b48e5c
-/
lemma norm_average_scale_le (x z : X) {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (‖x + r • z‖ + ‖x - r • z‖) / 2 ≤ (‖x + z‖ + ‖x - z‖) / 2 := by
  have h₁ : x + r • z = ((1 + r) / 2) • (x + z) + ((1 - r) / 2) • (x - z) := by
    module
  have h₂ : x - r • z = ((1 - r) / 2) • (x + z) + ((1 + r) / 2) • (x - z) := by
    module
  have hpos : 0 ≤ (1 + r) / 2 := by linarith
  have hneg : 0 ≤ (1 - r) / 2 := by linarith
  have hp := norm_add_le (((1 + r) / 2) • (x + z)) (((1 - r) / 2) • (x - z))
  have hm := norm_add_le (((1 - r) / 2) • (x + z)) (((1 + r) / 2) • (x - z))
  rw [← h₁, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hpos, abs_of_nonneg hneg] at hp
  rw [← h₂, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hpos, abs_of_nonneg hneg] at hm
  nlinarith

/--
@isnad1 id=le.1h4v.s7.814416ca962c from=translated src=- shape=c5b37029 vocab=40805200
-/
lemma increment_normalize_le (x y : X) {t : ℝ} (hy : 1 ≤ ‖y‖) :
    averagedIncrement (normSeminorm ℝ X) x t (‖y‖⁻¹ • y) ≤
      averagedIncrement (normSeminorm ℝ X) x t y := by
  have hyn : 0 < ‖y‖ := by linarith
  have hi : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hyn).mpr hy
  have h := norm_average_scale_le x (t • y) (inv_nonneg.mpr hyn.le) hi
  simpa only [averagedIncrement, coe_normSeminorm, smul_smul, mul_comm t,
    sub_le_sub_iff_right] using h

/--
@isnad1 id=le.1h4v.s5.16455d4dd73d from=translated src=- shape=8df68a90 vocab=4fff61b9
-/
lemma averagedIncrement_nonneg {x y : X} (hx : ‖x‖ = 1) (t : ℝ) :
    0 ≤ averagedIncrement (normSeminorm ℝ X) x t y := by
  have h := norm_add_le (x + t • y) (x - t • y)
  have heq : x + t • y + (x - t • y) = (2 : ℝ) • x := by module
  rw [heq, norm_smul, hx] at h
  norm_num at h
  change 0 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  linarith

/--
@isnad1 id=le.3h4v.s6.e32b31d7bd15 from=translated src=- shape=2ab84106 vocab=4fff61b9
-/
lemma averagedIncrement_le {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : averagedIncrement (normSeminorm ℝ X) x t y ≤ t := by
  have hp := norm_add_le x (t • y)
  have hm := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy, hx, mul_one] at hp hm
  change (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ t
  linarith

/--
@isnad1 id=le.2h4v.s6.df0f12aa5e72 from=translated src=- shape=2aedf142 vocab=289d02ac
-/
lemma averagedIncrement_ge_t_sub_one {x y : X} {t : ℝ} (ht : 0 ≤ t) (hy : 1 ≤ ‖y‖) :
    t - 1 ≤ averagedIncrement (normSeminorm ℝ X) x t y := by
  have h := norm_sub_le (x + t • y) (x - t • y)
  have heq : x + t • y - (x - t • y) = (2 * t) • y := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * t)] at h
  change t - 1 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  nlinarith

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Inner sets are kept explicit to make nonemptiness and conditional completeness visible. -/
def averageValues (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, 1 ≤ ‖y‖ ∧ a = averagedIncrement (normSeminorm ℝ X) x t y}

def oneSidedValues (x : X) (t : ℝ) (F : Submodule ℝ X) : Set ℝ :=
  {a | ∃ y ∈ F, ‖y‖ = 1 ∧ a = ‖x + t • y‖ - 1}

/--
@isnad1 id=nonempty.2h4v.s6.47c2778027da from=translated src=- shape=e6af4fec vocab=68437f42
-/
lemma averageValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) (x : X) (t : ℝ)
    {F : Submodule ℝ X} (hF : Cofinite F) : (averageValues x t F).Nonempty := by
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact ⟨_, y, hy, hny.ge, rfl⟩

/--
@isnad1 id=bddbelow.0h4v.s5.73e922929225 from=translated src=- shape=c3b81d0c vocab=9e4ef156
-/
lemma averageValues_bddBelow (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (averageValues x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hy, hny, rfl⟩
  change -1 ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1
  linarith [norm_nonneg (x + t • y), norm_nonneg (x - t • y)]

/--
@isnad1 id=nonempty.2h4v.s6.58229a72db50 from=translated src=- shape=e6af4fec vocab=2bf0d0a8
-/
lemma oneSidedValues_nonempty (hinf : ¬ FiniteDimensional ℝ X) (x : X) (t : ℝ)
    {F : Submodule ℝ X} (hF : Cofinite F) : (oneSidedValues x t F).Nonempty := by
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact ⟨_, y, hy, hny, rfl⟩

/--
@isnad1 id=bddbelow.0h4v.s5.c9523a83e41e from=translated src=- shape=c3b81d0c vocab=538898d5
-/
lemma oneSidedValues_bddBelow (x : X) (t : ℝ) (F : Submodule ℝ X) :
    BddBelow (oneSidedValues x t F) := by
  refine ⟨-1, ?_⟩
  rintro a ⟨y, hy, hny, rfl⟩
  linarith [norm_nonneg (x + t • y)]

/--
@isnad1 id=bddabove.3h3v.s6.2c21970f31a0 from=translated src=- shape=eb20b45e vocab=bd8bafb9
-/
lemma H_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (averageValues x t F)} := by
  refine ⟨t, ?_⟩
  rintro r ⟨F, hF, rfl⟩
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  exact (csInf_le (averageValues_bddBelow x t F) ⟨y, hy, hny.ge, rfl⟩).trans
    (averagedIncrement_le hx hny ht)

/--
@isnad1 id=bddabove.3h3v.s6.477564ed23da from=translated src=- shape=eb20b45e vocab=2f3c9486
-/
lemma D_outer_bddAbove (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    BddAbove {r | ∃ F : Submodule ℝ X, Cofinite F ∧ r = sInf (oneSidedValues x t F)} := by
  refine ⟨t, ?_⟩
  rintro r ⟨F, hF, rfl⟩
  obtain ⟨y, hy, hny⟩ := cofinite_has_unit hinf hF
  apply (csInf_le (oneSidedValues_bddBelow x t F) ⟨y, hy, hny, rfl⟩).trans
  have h := norm_add_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hny, mul_one, hx] at h
  linarith

/--
@isnad1 id=le.5h5v.s7.38f3955bd463 from=translated src=- shape=d3ff0c35 vocab=41294185
-/
lemma le_H_of_cofinite (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {F : Submodule ℝ X} (hF : Cofinite F) {a : ℝ}
    (ha : ∀ y ∈ F, 1 ≤ ‖y‖ → a ≤ averagedIncrement (normSeminorm ℝ X) x t y) :
    a ≤ H (normSeminorm ℝ X) x t := by
  apply le_trans (b := sInf (averageValues x t F))
  · apply le_csInf (averageValues_nonempty hinf x t hF)
    rintro r ⟨y, hy, hny, rfl⟩
    exact ha y hy hny
  · exact le_csSup (H_outer_bddAbove hinf hx ht) ⟨F, hF, rfl⟩

/--
@isnad1 id=le.5h5v.s8.085948646693 from=translated src=- shape=bf8fbac7 vocab=925872b8
-/
lemma le_D_of_cofinite (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {F : Submodule ℝ X} (hF : Cofinite F) {a : ℝ}
    (ha : ∀ y ∈ F, ‖y‖ = 1 → a ≤ ‖x + t • y‖ - 1) :
    a ≤ D (normSeminorm ℝ X) x t := by
  apply le_trans (b := sInf (oneSidedValues x t F))
  · apply le_csInf (oneSidedValues_nonempty hinf x t hF)
    rintro r ⟨y, hy, hny, rfl⟩
    exact ha y hy hny
  · exact le_csSup (D_outer_bddAbove hinf hx ht) ⟨F, hF, rfl⟩

/--
@isnad1 id=le.3h3v.s6.2f89666f1137 from=translated src=- shape=a8abf2f1 vocab=0073de73
-/
lemma H_ge_t_sub_one (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : t - 1 ≤ H (normSeminorm ℝ X) x t :=
  le_H_of_cofinite hinf hx ht cofinite_top
    (fun _ _ hy => averagedIncrement_ge_t_sub_one ht hy)

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω}

end ExactModuli

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
@isnad1 id=le.3h4v.s7.63f1f9e2e519 from=translated src=- shape=427cda9c vocab=c3bafd86
-/
lemma norm_ray_ge_t_sub_one {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : t - 1 ≤ ‖x + t • y‖ := by
  have h := norm_sub_le (x + t • y) x
  have heq : x + t • y - x = t • y := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy, mul_one, hx] at h
  linarith

/-- The one-sided lower estimate needs only a norming functional.
@isnad1 id=le.3h3v.s6.2359b0ea019b from=translated src=- shape=aaea288d vocab=595991e5
-/
theorem oneSided_lower_bound (hinf : ¬ FiniteDimensional ℝ X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : max 0 (t - 2) ≤ D (normSeminorm ℝ X) x t := by
  obtain ⟨φ, hφnorm, hφx⟩ := exists_dual_vector ℝ x (by rw [hx]; norm_num)
  have hφx' : φ x = 1 := by
    change φ x = ‖x‖ at hφx
    simpa only [hx] using hφx
  apply le_D_of_cofinite hinf hx ht (cofinite_ker φ)
  intro y hy hny
  have hφy : φ y = 0 := hy
  have happ : φ (x + t • y) = 1 := by simp [hφx', hφy]
  have hnorm := φ.le_opNorm (x + t • y)
  rw [happ, hφnorm, one_mul, norm_one] at hnorm
  have hrev := norm_ray_ge_t_sub_one hx hny ht
  exact max_le (by linarith) (by linarith)

/-- A single almost antipodal endpoint controls all radii, including the corner t=2.
@isnad1 id=le.6h6v.s8.0d556b2da407 from=translated src=- shape=db9e3841 vocab=a1fd5ce9
-/
lemma norm_ray_endpoint_bound {x y : X} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {L ε t : ℝ} (hL : 0 < L) (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hend : ‖x + L • y‖ ≤ 1 + ε) :
    ‖x + t • y‖ ≤ 1 + ε + max 0 (t - L) := by
  by_cases htL : t ≤ L
  · have hr : 0 ≤ t / L := div_nonneg ht hL.le
    have hr' : t / L ≤ 1 := (div_le_one hL).mpr htL
    have hid : x + t • y = (1 - t / L) • x + (t / L) • (x + L • y) := by
      have hmul : t / L * L = t := div_mul_cancel₀ t hL.ne'
      rw [smul_add, smul_smul, hmul]
      module
    rw [max_eq_left (sub_nonpos.mpr htL), add_zero, hid]
    have h := norm_add_le ((1 - t / L) • x) ((t / L) • (x + L • y))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hr'), abs_of_nonneg hr, hx, mul_one] at h
    nlinarith
  · have hLt : L ≤ t := le_of_not_ge htL
    have hid : x + t • y = (x + L • y) + (t - L) • y := by module
    rw [max_eq_right (sub_nonneg.mpr hLt), hid]
    have h := norm_add_le (x + L • y) ((t - L) • y)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hLt), hy, mul_one] at h
    linarith

end ExactModuli

end

end OAI
