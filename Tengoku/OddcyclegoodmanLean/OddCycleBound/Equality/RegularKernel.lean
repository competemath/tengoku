import Tengoku.OddcyclegoodmanLean.OddCycleBound.Necklace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regular graphons and the spectral step of Proposition 6.2

For an a.e. `q`-regular graphon `U` we prove, without eigenvalues, the facts used in the proof of
Proposition 6.2: `t(P_k, U) = q^k`, and the Hilbert–Schmidt version of the operator-norm bound
`‖T_U‖ ≤ q`, namely `‖U ∘ K‖_HS ≤ q ‖K‖_HS`. With `m = 2a + 1`, the cycle density
`t(C_m, U)` is the Hilbert–Schmidt pairing of the `a`-fold and `(a+1)`-fold kernel powers, and the
chain `t(C_m, U) ≤ q^{m-2} ∫∫ U² ≤ q^{m-1}` together with its equality cases gives `U ∈ {0,1}` and
`∫ U(x,z) U(z,y) dz = q U(x,y)` almost everywhere (equation `eq:equal-neighbourhoods`).
-/

open MeasureTheory

namespace OddCycleBound.Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Hilbert–Schmidt pairing `∫∫ K L` of two kernels.-/
noncomputable def hsInner (μ : Measure Ω) (K L : Ω → Ω → ℝ) : ℝ :=
  ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ)

/--
@isnad1 id=integrab.2h4v.s6.130fbf0f972d from=translated src=- shape=409e49e2 vocab=a7126426
-/
lemma _root_.OddCycleBound.GoodK.integrable_mul {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2) (μ.prod μ) := by
  obtain ⟨CK, _, hCK⟩ := hK.bdd
  obtain ⟨CL, _, hCL⟩ := hL.bdd
  refine (integrable_const (CK * CL)).mono' (hK.meas.mul hL.meas).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCK _ _) (hCL _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hCK p.1 p.2))

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=goodk.2h4v.s5.fe735c2c0f78 from=translated src=- shape=5719a316 vocab=a3ed93cc
-/
lemma goodK_sub_smul {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (c : ℝ) :
    GoodK (fun x y => A x y - c * B x y) := by
  obtain ⟨CA, hCA0, hCA⟩ := hA.bdd
  obtain ⟨CB, hCB0, hCB⟩ := hB.bdd
  refine ⟨hA.meas.sub (hB.meas.const_mul c), ⟨CA + |c| * CB, by positivity, fun x y => ?_⟩⟩
  calc |A x y - c * B x y| ≤ |A x y| + |c * B x y| := abs_sub _ _
    _ ≤ CA + |c| * CB := by
        rw [abs_mul]
        exact add_le_add (hCA x y) (mul_le_mul_of_nonneg_left (hCB x y) (abs_nonneg c))

omit [IsProbabilityMeasure μ] in
/--
@isnad1 id=le.0h3v.s4.2bdf5a825e93 from=translated src=- shape=2558a3be vocab=dbdc0699
-/
lemma hsInner_self_nonneg (K : Ω → Ω → ℝ) : 0 ≤ hsInner μ K K :=
  integral_nonneg fun _ => mul_self_nonneg _

/--
@isnad1 id=eq.2h5v.s7.1e4e3713e8c9 from=translated src=- shape=6deed10e vocab=ddc86cfc
-/
lemma hsInner_sub_smul_self {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (c : ℝ) :
    hsInner μ (fun x y => A x y - c * B x y) (fun x y => A x y - c * B x y) =
      hsInner μ A A - 2 * c * hsInner μ A B + c ^ 2 * hsInner μ B B := by
  unfold hsInner
  have e : ∀ p : Ω × Ω, (A p.1 p.2 - c * B p.1 p.2) * (A p.1 p.2 - c * B p.1 p.2) =
      A p.1 p.2 * A p.1 p.2 - 2 * c * (A p.1 p.2 * B p.1 p.2) +
        c ^ 2 * (B p.1 p.2 * B p.1 p.2) := fun p => by ring
  simp_rw [e]
  have h1 : Integrable (fun p : Ω × Ω => A p.1 p.2 * A p.1 p.2) (μ.prod μ) :=
    hA.integrable_mul hA
  have h2 : Integrable (fun p : Ω × Ω => 2 * c * (A p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hA.integrable_mul hB).const_mul _
  have h3 : Integrable (fun p : Ω × Ω => c ^ 2 * (B p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hB.integrable_mul hB).const_mul _
  have h12 : Integrable (fun p : Ω × Ω =>
      A p.1 p.2 * A p.1 p.2 - 2 * c * (A p.1 p.2 * B p.1 p.2)) (μ.prod μ) := h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul]

/--
@isnad1 id=eq.3h6v.s6.2156399a7ffb from=translated src=- shape=e2d46e5e vocab=c436e2ca
-/
lemma hsInner_sub_left {A B C : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (hC : GoodK C)
    (c : ℝ) :
    hsInner μ C (fun x y => A x y - c * B x y) = hsInner μ C A - c * hsInner μ C B := by
  unfold hsInner
  have e : ∀ p : Ω × Ω, C p.1 p.2 * (A p.1 p.2 - c * B p.1 p.2) =
      C p.1 p.2 * A p.1 p.2 - c * (C p.1 p.2 * B p.1 p.2) := fun p => by ring
  simp_rw [e]
  have h1 : Integrable (fun p : Ω × Ω => C p.1 p.2 * A p.1 p.2) (μ.prod μ) :=
    hC.integrable_mul hA
  have h2 : Integrable (fun p : Ω × Ω => c * (C p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hC.integrable_mul hB).const_mul _
  rw [integral_sub h1 h2, integral_const_mul]

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing.
@isnad1 id=le.2h4v.s6.f6ce3a326a2d from=translated src=- shape=1f7fd70b vocab=46ee882e
-/
lemma hsInner_sq_le {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    hsInner μ A B ^ 2 ≤ hsInner μ A A * hsInner μ B B := by
  have h : ∀ t : ℝ,
      0 ≤ hsInner μ B B * (t * t) + (-2 * hsInner μ A B) * t + hsInner μ A A := by
    intro t
    have := hsInner_self_nonneg (μ := μ) (fun x y => A x y - t * B x y)
    rw [hsInner_sub_smul_self hA hB t] at this
    nlinarith [this]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

/--
@isnad1 id=eq.3h4v.s6.360e21979938 from=translated src=- shape=1a515568 vocab=36df1e24
-/
lemma hsInner_eq_zero_of_self_eq_zero {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B)
    (h : hsInner μ B B = 0) : hsInner μ A B = 0 := by
  have := hsInner_sq_le (μ := μ) hA hB
  rw [h, mul_zero] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _))

/--
@isnad1 id=eventual.2h3v.s6.a721af39dc08 from=translated src=- shape=287bf74b vocab=33a30b84
-/
lemma ae_eq_zero_of_hsInner_self_eq_zero {A : Ω → Ω → ℝ} (hA : GoodK A)
    (h : hsInner μ A A = 0) : ∀ᵐ p ∂(μ.prod μ), A p.1 p.2 = 0 := by
  unfold hsInner at h
  rw [integral_eq_zero_iff_of_nonneg (fun p => mul_self_nonneg _) (hA.integrable_mul hA)] at h
  filter_upwards [h] with p hp
  exact mul_self_eq_zero.mp hp

/-- The trace of a product is the Hilbert–Schmidt pairing when the second factor is symmetric.
@isnad1 id=eq.3h4v.s6.3ce1d7503185 from=translated src=- shape=917c30a4 vocab=26f9ab7a
-/
lemma trace_comp_eq_hsInner {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B)
    (hBs : ∀ x y, B x y = B y x) : trace μ (comp μ A B) = hsInner μ A B := by
  unfold trace comp hsInner
  rw [integral_prod _ (hA.integrable_mul hB)]
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun z => ?_))
  simp only [hBs z x]

/--
@isnad1 id=eq.1h5v.s6.1cd168aa3eff from=translated src=- shape=820a71ca vocab=250e7020
-/
lemma comp_compPow_compPow {U : Ω → Ω → ℝ} (hU : GoodK U) : ∀ a b : ℕ,
    comp μ (compPow μ U a) (compPow μ U b) = compPow μ U (a + b + 1)
  | 0, b => by rw [show 0 + b + 1 = b + 1 by omega]; rfl
  | a + 1, b => by
      show comp μ (comp μ U (compPow μ U a)) (compPow μ U b) = _
      rw [comp_assoc hU (goodK_compPow hU a) (goodK_compPow hU b), comp_compPow_compPow hU a b,
        show a + 1 + b + 1 = (a + b + 1) + 1 by omega]
      rfl

/-- `⟨U^{a+1}, U^{b+1}⟩_HS = t(C_{a+b+2}, U)` for a graphon `U`.
@isnad1 id=eq.1h5v.s6.d54aea0547ae from=translated src=- shape=825e0b7a vocab=81eb243e
-/
lemma hsInner_compPow {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) (a b : ℕ) :
    hsInner μ (compPow μ U a) (compPow μ U b) = trace μ (compPow μ U (a + b + 1)) := by
  have hGU := goodK_of_isGraphon hU
  rw [← comp_compPow_compPow hGU a b,
    trace_comp_eq_hsInner (goodK_compPow hGU a) (goodK_compPow hGU b)
      (compPow_symm hGU hU.symm b)]

/-! ### Regular graphons -/

variable {U : Ω → Ω → ℝ}

/--
@isnad1 id=eq.2h5v.s6.13b8afd9e53b from=translated src=- shape=999ed83d vocab=5c3c64e5
-/
lemma integral_comp_row {L : Ω → Ω → ℝ} (hU : IsGraphon U μ) (hL : GoodK L) (x : Ω) :
    ∫ y, comp μ U L x y ∂μ = kernelOp U μ (fun z => ∫ y, L z y ∂μ) x := by
  have hGU := goodK_of_isGraphon hU
  obtain ⟨C, _, hC⟩ := hL.bdd
  have hint : Integrable (Function.uncurry fun y z => U x z * L z y) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun y z => U x z * L z y) :=
      (hGU.meas.comp (measurable_const.prodMk measurable_snd)).mul
        (hL.meas.comp (measurable_snd.prodMk measurable_fst))
    refine (integrable_const (1 * C)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by rw [abs_of_nonneg (hU.nonneg _ _)]; exact hU.le_one _ _) (hC _ _)
      (abs_nonneg _) zero_le_one
  calc ∫ y, comp μ U L x y ∂μ = ∫ y, ∫ z, U x z * L z y ∂μ ∂μ := rfl
    _ = ∫ z, ∫ y, U x z * L z y ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ z, U x z * ∫ y, L z y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        exact integral_const_mul _ _
    _ = kernelOp U μ (fun z => ∫ y, L z y ∂μ) x := rfl

/--
@isnad1 id=good.1h3v.s5.7a8fde7b3381 from=translated src=- shape=cef1941f vocab=de5f156f
-/
lemma good_rowIntegral {L : Ω → Ω → ℝ} (hL : GoodK L) : Good (fun z => ∫ y, L z y ∂μ) := by
  obtain ⟨C, hC0, hC⟩ := hL.bdd
  refine ⟨(show StronglyMeasurable (Function.uncurry L) from
    hL.meas.stronglyMeasurable).integral_prod_right', ⟨C, hC0, fun z => ?_⟩⟩
  calc |∫ y, L z y ∂μ| ≤ ∫ y, |L z y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, C ∂μ := integral_mono (hL.integrable_row z).abs (integrable_const C)
        fun y => hC z y
    _ = C := by simp

/--
@isnad1 id=goodk.1h2v.s5.d82756c3900c from=translated src=- shape=25237f7c vocab=a615398d
-/
lemma goodK_sq {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (fun x y => K x y * K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine ⟨hK.meas.mul hK.meas, ⟨C * C, mul_nonneg hC0 hC0, fun x y => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hC x y) (hC x y) (abs_nonneg _) hC0

end OddCycleBound.Equality
