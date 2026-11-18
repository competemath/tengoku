import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

/--
@isnad1 id=eq.5h6v.s7.089302f5c6c0 from=translated src=- shape=18299175 vocab=1ddfebe1
-/
theorem second_prefactor_identity
    (Y qe qg qx₁ qx₂ Li : ℝ)
    (hqe : 0 < qe) (hqg : 0 < qg) (hqx₁ : 0 < qx₁)
    (hqx₂ : 0 < qx₂) (hLi : 0 < Li) :
    Y / (qe * Real.sqrt ((qx₁ / qg) * (qx₂ / qg))) =
      (Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) := by
  have hs1 : Real.sqrt (qx₁ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₁ hqg))
  have hs2 : Real.sqrt (qx₂ / qg) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hqx₂ hqg))
  have ht1 : Real.sqrt (Li / qx₁) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₁))
  have ht2 : Real.sqrt (Li / qx₂) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos hLi hqx₂))
  have hqg0 : qg ≠ 0 := ne_of_gt hqg
  have hqe0 : qe ≠ 0 := ne_of_gt hqe
  have hLi0 : Li ≠ 0 := ne_of_gt hLi
  have hqx10 : qx₁ ≠ 0 := ne_of_gt hqx₁
  have hqx20 : qx₂ ≠ 0 := ne_of_gt hqx₂
  rw [Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
  have ha : Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₁ hqg))]
    congr 1
    field_simp
  have hb : Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂) = Real.sqrt (Li / qg) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hqx₂ hqg))]
    congr 1
    field_simp
  have hc : Real.sqrt (Li / qg) * Real.sqrt (Li / qg) = Li / qg := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt (div_pos hLi hqg))
  have hmain :
      Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂) *
        (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg)) = Li / qg := by
    calc
      _ = (Real.sqrt (qx₁ / qg) * Real.sqrt (Li / qx₁)) *
          (Real.sqrt (qx₂ / qg) * Real.sqrt (Li / qx₂)) := by ring
      _ = Li / qg := by rw [ha, hb, hc]
  apply (div_eq_iff (mul_ne_zero hqe0 (mul_ne_zero hs1 hs2))).2
  calc
    Y = (Y * qg / (qe * Li)) * ((Li / qg) * qe) := by field_simp
    _ = ((Y * qg / (qe * Li)) * Real.sqrt (Li / qx₁) * Real.sqrt (Li / qx₂)) *
          (qe * (Real.sqrt (qx₁ / qg) * Real.sqrt (qx₂ / qg))) := by
       rw [← hmain]
       ring

namespace ActualEisensteinCubic

section

open scoped ComplexConjugate

/--
@isnad1 id=eq.1h2v.s10.04ec2d6d1c6c from=translated src=- shape=b0950409 vocab=f14a059f
-/
theorem canonicalSextic_conj_as_row_label
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (e : O) :
    star (canonicalSextic P hgood (Ideal.Quotient.mk P e)) =
      canonicalSextic P hgood (Ideal.Quotient.mk P e) *
        (canonicalSextic P hgood (Ideal.Quotient.mk P e)) ^ 4 := by
  let χ := canonicalSextic P hgood
  let x : O ⧸ P := Ideal.Quotient.mk P e
  have hconj : star (χ x) = (χ x)⁻¹ := by
    by_cases hx : IsUnit x
    · let u : (O ⧸ P)ˣ := hx.unit
      have hu : (u : O ⧸ P) = x := hx.unit_spec
      rw [← hu]
      exact (canonicalSextic_inverse_eq_conj_on_units P hgood u).symm
    · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
      simp [hzero]
  rw [hconj]
  by_cases hx : IsUnit x
  · have h6 : (χ x) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0),
        canonicalSextic_pow_six P hgood]
      exact MulChar.one_apply hx
    apply inv_eq_of_mul_eq_one_right
    calc
      χ x * (χ x * (χ x) ^ 4) = (χ x) ^ 6 := by ring
      _ = 1 := h6
  · have hzero : χ x = 0 := MulChar.map_nonunit χ hx
    change (χ x)⁻¹ = χ x * (χ x) ^ 4
    simp [hzero]

/--
@isnad1 id=eq.1h5v.s7.297e988bcb4d from=translated src=- shape=f052f5b6 vocab=a5e97cb1
-/
theorem finiteSquarefreeRow_mul
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a b : O) :
    finiteSquarefreeRow P hgood S (a * b) =
      finiteSquarefreeRow P hgood S a * finiteSquarefreeRow P hgood S b := by
  classical
  simp only [finiteSquarefreeRow, map_mul, Finset.prod_mul_distrib]

end

noncomputable def rowCoprimeMask
    {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (u : O) : ℂ := by
  classical
  exact if ∃ i ∈ S, u ∈ P i then 0 else 1

/--
@isnad1 id=eq.1h4v.s8.0579114eea16 from=translated src=- shape=994c2f83 vocab=af591cc7
-/
theorem finiteSquarefreeRow_self_pair
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood S u =
      rowCoprimeMask P S u := by
  classical
  unfold finiteSquarefreeRow rowCoprimeMask
  rw [star_prod, ← Finset.prod_mul_distrib]
  by_cases h : ∃ i ∈ S, u ∈ P i
  · rw [ite_eq_left h]
    obtain ⟨i, hi, hui⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hui, MulChar.map_zero]
    simp
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    rw [MulChar.star_apply', ← MulChar.mul_apply, inv_mul_cancel]
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    exact isUnit_iff_ne_zero.mpr fun hui => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hui⟩

/--
@isnad1 id=eq.1h5v.s9.4cd3068423eb from=translated src=- shape=cfbc8664 vocab=ad802e11
-/
theorem finiteSquarefreeRow_pair_kernel
    {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1 ∉ P i)
    (S T : Finset ι) (u : O) :
    star (finiteSquarefreeRow P hgood S u) * finiteSquarefreeRow P hgood T u =
      rowCoprimeMask P (S ∩ T) u *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by
  have hsplit (A B : Finset ι) :
      finiteSquarefreeRow P hgood A u =
        finiteSquarefreeRow P hgood (A ∩ B) u *
        finiteSquarefreeRow P hgood (A \ B) u := by
    exact (Finset.prod_inter_mul_prod_sdiff A B _).symm
  rw [hsplit S T, hsplit T S, Finset.inter_comm T S, star_mul]
  calc
    _ = (star (finiteSquarefreeRow P hgood (S ∩ T) u) *
          finiteSquarefreeRow P hgood (S ∩ T) u) *
        star (finiteSquarefreeRow P hgood (S \ T) u) *
        finiteSquarefreeRow P hgood (T \ S) u := by ring
    _ = _ := by rw [finiteSquarefreeRow_self_pair]

private theorem mask_powerset {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, p i then 1 else 0 := by
  have hprod : (if ∃ i ∈ S, p i then (0 : ℂ) else 1) =
      ∏ i ∈ S, (1 - if p i then (1 : ℂ) else 0) := by
    by_cases h : ∃ i ∈ S, p i
    · rw [ite_eq_left h]
      obtain ⟨i, hi, hp⟩ := h
      symm
      apply Finset.prod_eq_zero hi
      simp [hp]
    · rw [ite_eq_right h]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [show ¬p i from fun hp => h ⟨i, hi, hp⟩]
  rw [hprod, Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro E hE
  simp only [Finset.prod_const_one, mul_one]
  congr 1
  by_cases h : ∀ i ∈ E, p i
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hp⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hp]

/--
@isnad1 id=eq.0h4v.s8.01589048def8 from=translated src=- shape=b02b783d vocab=da72596b
-/
theorem rowCoprimeMask_subsets
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (u : O) :
    rowCoprimeMask P S u =
      ∑ E ∈ S.powerset, (-1 : ℂ) ^ E.card *
        if ∀ i ∈ E, u ∈ P i then 1 else 0 := by
  classical
  exact mask_powerset S (fun i => u ∈ P i)

/--
@isnad1 id=eq.2h3v.s8.22bf0ac10526 from=translated src=- shape=2714d4a0 vocab=235bacd0
-/
theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

/--
@isnad1 id=iff.1h4v.s8.0001e5a3c841 from=translated src=- shape=d66b2fe0 vocab=0a57a9b3
-/
theorem mem_prime_product_iff
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (u : O) :
    u ∈ (∏ i ∈ S, P i) ↔ ∀ i ∈ S, u ∈ P i := by
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp
  · intro i hi j hj hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)

end ActualEisensteinCubic

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical

noncomputable def primeSubsetProduct (F : Finset (Ideal O))
    (E : Finset (primePool F)) : Ideal O := ∏ i ∈ E, i.1

noncomputable def residualSexticRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I J : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact finiteSquarefreeRow (fun i : primePool F => i.1)
    (primePool_good F hFgood) (idealSupport F I \ idealSupport F J) u

end

open ActualEisensteinCubic

/--
@isnad1 id=dvd.2h3v.s10.8fdeb2cd0467 from=translated src=- shape=540f3b33 vocab=74a0bc61
-/
theorem idealSupport_product_dvd
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (E : Finset (primePool F))
    (hE : E ⊆ idealSupport F I) :
    (∏ i ∈ E, i.1) ∣ I := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply Ideal.isCoprime_of_isMaximal
    exact Subtype.val_injective.ne hij
  · intro i hi
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      ((mem_idealSupport_iff F I i).mp (hE hi))

/--
@isnad1 id=and.2h4v.s11.e939833ae4da from=translated src=- shape=ff5dcaf0 vocab=b1592dc5
-/
theorem commonSupport_product_dvd
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I J : Ideal O) (E : Finset (primePool F))
    (hE : E ∈ (idealSupport F I ∩ idealSupport F J).powerset) :
    (∏ i ∈ E, i.1) ∣ I ∧ (∏ i ∈ E, i.1) ∣ J := by
  have hsub := Finset.mem_powerset.mp hE
  exact ⟨idealSupport_product_dvd F hFpos I E
    (fun i hi => (Finset.mem_inter.mp (hsub hi)).1),
    idealSupport_product_dvd F hFpos J E
    (fun i hi => (Finset.mem_inter.mp (hsub hi)).2)⟩

end ConcretePrimeRowBridge

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
abbrev LogPlane := WithLp 2 (ℝ × ℝ)

/--
@isnad1 id=eq.1h3v.s8.46a5bf2c4884 from=translated src=- shape=d79f6c17 vocab=b6a69b93
-/
theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def complexPoint (x y : ℝ) : ℂ := ⟨x, y⟩

/--
@isnad1 id=eq.0h2v.s4.1349a499119d from=translated src=- shape=8806ad8a vocab=cb675b87
-/
theorem complexPoint_eq (x y : ℝ) : complexPoint x y = (x : ℂ) + Complex.I * (y : ℂ) := by
  apply Complex.ext <;> simp [complexPoint]

def planeComplexIso : LogPlane ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).trans
    Complex.equivRealProdCLM.toLinearEquiv.symm
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖complexPoint (WithLp.ofLp z).1 (WithLp.ofLp z).2‖ ^ 2 =
      ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, complexPoint, Real.norm_eq_abs,  sq]

/--
@isnad1 id=eq.0h2v.s8.8b9cf834b16c from=translated src=- shape=34ba40e6 vocab=de5c0170
-/
@[simp] theorem planeComplexIso_apply (x y : ℝ) :
    planeComplexIso (WithLp.toLp 2 (x, y)) = complexPoint x y := rfl

/--
@isnad1 id=isometry.0h1v.s4.e80b3a747a1a from=translated src=- shape=a4c439d3 vocab=05fba010
-/
theorem horizontal_isometry (η : ℝ) : Isometry (fun x : ℝ => complexPoint x η) := by
  apply Isometry.of_dist_eq
  intro x y
  have h : complexPoint x η - complexPoint y η = ((x - y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, Complex.norm_real]

/--
@isnad1 id=hastempe.0h1v.s4.6b50dface241 from=translated src=- shape=a4c439d3 vocab=1e0cd58f
-/
theorem horizontal_temperate (η : ℝ) :
    (fun x : ℝ => complexPoint x η).HasTemperateGrowth := by
  have heq : (fun x : ℝ => complexPoint x η) =
      (fun x : ℝ => Complex.ofRealCLM x + Complex.I * (η : ℂ)) := by
    funext x
    exact complexPoint_eq x η
  rw [heq]
  fun_prop

def horizontalSlice (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (horizontal_temperate η)
    (horizontal_isometry η).antilipschitzWith f

/--
@isnad1 id=eq.0h3v.s7.cdf5d500fa89 from=translated src=- shape=e48239c5 vocab=1b1233ea
-/
@[simp] theorem horizontalSlice_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    horizontalSlice f η x = f (complexPoint x η) := rfl

def partialFourier (f : SchwartzMap ℂ ℂ) (η x : ℝ) : ℂ :=
  𝓕 (fun y : ℝ => f (complexPoint x y)) η

/--
@isnad1 id=eq.0h3v.s7.d3915de817c7 from=translated src=- shape=04837905 vocab=36423dda
-/
theorem partialFourier_eq_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x =
      ∫ y : ℝ, Real.fourierChar (-inner ℝ y η) • f (complexPoint x y) := rfl

/--
@isnad1 id=eq.0h3v.s7.65434bfa62e0 from=translated src=- shape=236499a9 vocab=167cc612
-/
theorem partialFourier_eq_exp_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x = ∫ y : ℝ,
      Complex.exp (((-2 * Real.pi * (y * η) : ℝ) : ℂ) * Complex.I) *
        f ((x : ℂ) + Complex.I * (y : ℂ)) := by
  have hin (y : ℝ) : inner ℝ y η = y * η := by simp [RCLike.inner_apply, mul_comm]
  simp only [partialFourier, Real.fourier_eq', hin, complexPoint_eq, smul_eq_mul]

def verticalMajorant (f : SchwartzMap ℂ ℂ) (y : ℝ) : ℝ :=
  ((SchwartzMap.seminorm ℝ 0 0) f + (SchwartzMap.seminorm ℝ 2 0) f) * (1 + y ^ 2)⁻¹

/--
@isnad1 id=integrab.0h1v.s5.0261f70980a3 from=translated src=- shape=b295917b vocab=f2bded5d
-/
theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

/--
@isnad1 id=le.0h3v.s6.2ce485665037 from=translated src=- shape=d9cec576 vocab=edb1e910
-/
theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

/--
@isnad1 id=continuo.0h2v.s5.2e667b616602 from=translated src=- shape=876650a4 vocab=0664e41a
-/
theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

/--
@isnad1 id=integrab.0h2v.s6.e4d598478a21 from=translated src=- shape=78ec3247 vocab=f7fcdf54
-/
theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

/--
@isnad1 id=eq.0h3v.s7.699644449467 from=translated src=- shape=181f025e vocab=3c4ed8b5
-/
theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

def partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (horizontalSlice (𝓕 f) η)

/--
@isnad1 id=eq.0h3v.s6.e5c4ff40117d from=translated src=- shape=03e88913 vocab=64eb2d3d
-/
theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

/--
@isnad1 id=eq.0h2v.s6.e97a63ea906a from=translated src=- shape=f07ee2fd vocab=64eb2d3d
-/
theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

/--
@isnad1 id=eq.0h3v.s7.ad8ad268ebd1 from=translated src=- shape=84d8e6bb vocab=9f16996c
-/
theorem fourier_partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourierSchwartz f η : ℝ → ℂ) ξ =
      𝓕 (f : ℂ → ℂ) ((ξ : ℂ) + Complex.I * (η : ℂ)) := by
  rw [partialFourierSchwartz_coe, fourier_partialFourier, complexPoint_eq]

/--
@isnad1 id=hasfderi.0h2v.s6.139016367152 from=translated src=- shape=0e3e1b15 vocab=cd7396fd
-/
theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

/--
@isnad1 id=eq.0h2v.s7.86abdf96dbf3 from=translated src=- shape=3a5b0dff vocab=5fce0edc
-/
theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

/--
@isnad1 id=eq.0h2v.s8.458f49841536 from=translated src=- shape=a05ec628 vocab=5fce0edc
-/
theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

/--
@isnad1 id=summable.0h0v.s5.5d76d76a3860 from=translated src=- shape=9200eb2e vocab=f72536ee
-/
theorem summable_int_cauchy_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  classical
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ℤ))]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (hp.subtype (fun n : ℤ => n ∉ ({0} : Finset ℤ)))
  intro n
  have hn : n.val ≠ 0 := by simpa only [Finset.mem_singleton] using n.property
  have hnr : (n.val : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsq : 0 < (n.val : ℝ) ^ 2 := sq_pos_of_ne_zero hnr
  change (1 + (n.val : ℝ) ^ 2)⁻¹ ≤ 1 / (n.val : ℝ) ^ 2
  simpa only [one_div] using
    one_div_le_one_div_of_le hsq (show (n.val : ℝ) ^ 2 ≤ 1 + (n.val : ℝ) ^ 2 by linarith)

/--
@isnad1 id=summable.0h0v.s6.9575b833f194 from=translated src=- shape=6bdf7331 vocab=5689753b
-/
theorem summable_int_cauchy_product :
    Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) :=
  summable_int_cauchy_weight.mul_of_nonneg summable_int_cauchy_weight
    (fun _ => by positivity) (fun _ => by positivity)

/--
@isnad1 id=summable.1h2v.s7.5400b28f87da from=translated src=- shape=a76c1908 vocab=ed663f9b
-/
theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

/--
@isnad1 id=summable.1h2v.s7.73f0aef9c97b from=translated src=- shape=4f25ec50 vocab=ed663f9b
-/
theorem summable_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) : Summable F :=
  (summable_norm_of_cauchy_product F C hF).of_norm

def planeDecayConstant (F : SchwartzMap ℂ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 F + SchwartzMap.seminorm ℝ 2 0 F +
    SchwartzMap.seminorm ℝ 4 0 F

/--
@isnad1 id=le.0h1v.s5.f89f0e7e0c11 from=translated src=- shape=31d5eeaa vocab=3beb0dbd
-/
theorem planeDecayConstant_nonneg (F : SchwartzMap ℂ ℂ) : 0 ≤ planeDecayConstant F := by
  unfold planeDecayConstant
  positivity

/--
@isnad1 id=le.0h3v.s7.febbabd4d724 from=translated src=- shape=5f5e47f1 vocab=4918d4c8
-/
theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

/--
@isnad1 id=le.0h3v.s7.60e2d6f42a44 from=translated src=- shape=eac87b88 vocab=91d3ff73
-/
theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

/--
@isnad1 id=le.0h3v.s8.5a4da24e06a8 from=translated src=- shape=6a9c0412 vocab=93e92934
-/
theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

/--
@isnad1 id=eq.0h2v.s8.091eecfb45f8 from=translated src=- shape=f2a5e9e1 vocab=aace7872
-/
theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

/--
@isnad1 id=le.0h2v.s9.c7dc54272370 from=translated src=- shape=64fb01db vocab=5b1574f6
-/
theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

/--
@isnad1 id=le.0h3v.s8.bc6b5ca8c2f4 from=translated src=- shape=32523591 vocab=1e485b91
-/
theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

def partialFourierDecayConstant (f : SchwartzMap ℂ ℂ) : ℝ :=
  Real.pi * (planeDecayConstant (𝓕 f) +
    planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} (𝓕 f))))

/--
@isnad1 id=le.0h1v.s5.2bb89da898fa from=translated src=- shape=31d5eeaa vocab=582643c5
-/
theorem partialFourierDecayConstant_nonneg (f : SchwartzMap ℂ ℂ) :
    0 ≤ partialFourierDecayConstant f :=
  mul_nonneg Real.pi_pos.le
    (add_nonneg (planeDecayConstant_nonneg _) (planeDecayConstant_nonneg _))

/--
@isnad1 id=le.0h3v.s6.a9e911debd37 from=translated src=- shape=34a8c8e9 vocab=d373f369
-/
theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

/--
@isnad1 id=le.0h3v.s6.ad351271ea71 from=translated src=- shape=ca543bc8 vocab=a25bc14b
-/
theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

/--
@isnad1 id=summable.0h1v.s5.55ea256c795d from=translated src=- shape=e788eb89 vocab=2bc23318
-/
theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

/--
@isnad1 id=summable.0h1v.s6.075bec1ee0c9 from=translated src=- shape=0960b139 vocab=0a852664
-/
theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

/--
@isnad1 id=summable.0h1v.s6.3b7411cf4ea9 from=translated src=- shape=c257469f vocab=b66b6edb
-/
theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

/--
@isnad1 id=summable.0h1v.s6.8d6e5e9a6777 from=translated src=- shape=8950d1d7 vocab=5fce2c0f
-/
theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

/--
@isnad1 id=isometry.0h1v.s4.89f805244890 from=translated src=- shape=4827ab61 vocab=05fba010
-/
theorem vertical_isometry (x : ℝ) : Isometry (fun y : ℝ => complexPoint x y) := by
  apply Isometry.of_dist_eq
  intro y z
  have h : complexPoint x y - complexPoint x z =
      Complex.I * ((y - z : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]

/--
@isnad1 id=hastempe.0h1v.s4.f2c02c19095d from=translated src=- shape=4827ab61 vocab=1e0cd58f
-/
theorem vertical_temperate (x : ℝ) :
    (fun y : ℝ => complexPoint x y).HasTemperateGrowth := by
  have heq : (fun y : ℝ => complexPoint x y) =
      (fun y : ℝ => (x : ℂ) + Complex.I * Complex.ofRealCLM y) := by
    funext y
    exact complexPoint_eq x y
  rw [heq]
  fun_prop

def verticalSlice (f : 𝓢(ℂ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (vertical_temperate x)
    (vertical_isometry x).antilipschitzWith f

/--
@isnad1 id=eq.0h3v.s7.68e8dc210af0 from=translated src=- shape=81622cfe vocab=5aaf3c5d
-/
@[simp] theorem verticalSlice_apply (f : 𝓢(ℂ, ℂ)) (x y : ℝ) :
    verticalSlice f x y = f (complexPoint x y) := rfl

/--
@isnad1 id=eq.0h1v.s7.f1da0e4ae4d3 from=translated src=- shape=33a0da47 vocab=30302ea8
-/
theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

/--
@isnad1 id=eq.0h2v.s7.37fefcbd36f6 from=translated src=- shape=cc230e92 vocab=40bdfb97
-/
theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

/--
@isnad1 id=eq.0h1v.s8.ae854fbffa11 from=translated src=- shape=810fb29d vocab=5b7530f2
-/
theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
