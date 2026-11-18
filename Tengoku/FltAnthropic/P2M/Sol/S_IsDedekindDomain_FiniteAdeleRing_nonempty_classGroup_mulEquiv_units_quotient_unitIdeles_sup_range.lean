import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IsDedekindDomain_FiniteUnitIdeles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range

set_option autoImplicit false

open _root_.IsDedekindDomain open _root_.IsDedekindDomain.HeightOneSpectrum open _root_.WithZero
open scoped nonZeroDivisors

namespace IsDedekindDomain
export _root_.IsDedekindDomain (FiniteAdeleRing mk HeightOneSpectrum FiniteAdeleRing.unitIdeles)
namespace FiniteAdeleRing
export _root_.IsDedekindDomain.FiniteAdeleRing (ext unitIdeles)
namespace P2MIdeleContent
open _root_.IsDedekindDomain.FiniteAdeleRing open _root_.IsDedekindDomain

noncomputable section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/--
@isnad1 id=eq.0h5v.s8.27eea965b1ef from=translated src=- shape=b85687c8 vocab=ae3acdbd
-/
lemma far_mul_apply (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (x * y) v = x v * y v := rfl

/--
@isnad1 id=eq.0h3v.s7.feb77c904bcd from=translated src=- shape=49358a69 vocab=120983fe
-/
lemma far_one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

def evalAt (v : HeightOneSpectrum R) : (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom _ v).toMonoidHom

/--
@isnad1 id=eq.0h4v.s9.d11a62ec9366 from=translated src=- shape=6a009171 vocab=26b2625a
-/
@[scoped simp] lemma evalAt_val (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (evalAt R K v x : v.adicCompletion K) = (x : FiniteAdeleRing R K) v := rfl

/--
@isnad1 id=ne.0h4v.s8.056aed0e0808 from=translated src=- shape=6e7d0c79 vocab=55189e21
-/
lemma valued_ne_zero (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := by
  rw [← evalAt_val]
  simp only [ne_eq, map_eq_zero]
  exact (evalAt R K v x).ne_zero

def expAt (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) : ℤ :=
  -log (Valued.v ((x : FiniteAdeleRing R K) v))

/--
@isnad1 id=eq.0h3v.s7.3f7b7a73947b from=translated src=- shape=1c401904 vocab=89bb69a6
-/
lemma expAt_one (v : HeightOneSpectrum R) : expAt R K v 1 = 0 := by
  rw [expAt, Units.val_one, far_one_apply, map_one, log_one, neg_zero]

/--
@isnad1 id=eq.0h5v.s8.90c3caca7506 from=translated src=- shape=fba86d6f vocab=3862c38e
-/
lemma expAt_mul (v : HeightOneSpectrum R) (x y : (FiniteAdeleRing R K)ˣ) :
    expAt R K v (x * y) = expAt R K v x + expAt R K v y := by
  simp only [expAt]
  rw [Units.val_mul, far_mul_apply, map_mul,
    log_mul (valued_ne_zero R K v x) (valued_ne_zero R K v y)]
  ring

/--
@isnad1 id=eq.0h4v.s7.2f5e60a1b00c from=translated src=- shape=b370451a vocab=9534df56
-/
lemma expAt_inv (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x⁻¹ = -expAt R K v x := by
  have h := expAt_mul R K v x x⁻¹
  rw [mul_inv_cancel, expAt_one] at h
  omega

/--
@isnad1 id=iff.0h4v.s8.0cbf649383a0 from=translated src=- shape=b012d2c0 vocab=9919b8df
-/
lemma expAt_eq_zero_iff (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x = 0 ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [expAt, neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log (valued_ne_zero R K v x), h, exp_zero]
  · intro h
    rw [h, log_one]

private lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1)
    (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

/--
@isnad1 id=eq.2h4v.s9.b0b0d43c9264 from=translated src=- shape=ca0b8687 vocab=0907453a
-/
theorem expAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : (FiniteAdeleRing R K)ˣ}
    (hx : Valued.v ((x : FiniteAdeleRing R K) v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) ≤ 1) :
    expAt R K v x = 0 := by
  rw [expAt_eq_zero_iff]
  have hmul : Valued.v ((x : FiniteAdeleRing R K) v) *
      Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, ← far_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      far_one_apply, map_one]
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

/--
@isnad1 id=finite.0h3v.s6.3f9bc9a823d7 from=translated src=- shape=a4b8815c vocab=90f9b8b5
-/
theorem finite_support_expAt (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | expAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite,
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := (x : FiniteAdeleRing R K).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  intro hcon
  exact hv (expAt_eq_zero_of_integral R K
    ((mem_adicCompletionIntegers R K v).mp hcon.1)
    ((mem_adicCompletionIntegers R K v).mp hcon.2))

omit [IsDedekindDomain R] in
/--
@isnad1 id=ne.0h3v.s7.50becd14f3c4 from=translated src=- shape=2c70bb0d vocab=1de97356
-/
lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) :
    (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

/--
@isnad1 id=ne.0h4v.s8.292d8f3f3ca1 from=translated src=- shape=01a54517 vocab=57deea1a
-/
lemma zpow_asIdeal_ne_zero (v : HeightOneSpectrum R) (n : ℤ) :
    (v.asIdeal : FractionalIdeal R⁰ K) ^ n ≠ 0 :=
  zpow_ne_zero n (coeIdeal_asIdeal_ne_zero R K v)

/--
@isnad1 id=le.0h3v.s8.b9a695f4fb14 from=translated src=- shape=254e6716 vocab=c86bb5d9
-/
lemma mulSupport_zpow_subset (e : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ (e v)) ⊆
      {v | e v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  intro h0
  exact hv (by rw [h0, zpow_zero])

def assocIdeal (x : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (expAt R K v x)

/--
@isnad1 id=ne.0h3v.s7.470996577688 from=translated src=- shape=e6ed5884 vocab=0a2c0381
-/
lemma assocIdeal_ne_zero (x : (FiniteAdeleRing R K)ˣ) : assocIdeal R K x ≠ 0 := by
  rw [assocIdeal, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_support_expAt R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_asIdeal_ne_zero R K v _

/--
@isnad1 id=eq.0h4v.s6.9622b12609f6 from=translated src=- shape=50b7aa1e vocab=9b8b2e23
-/
theorem count_assocIdeal (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    FractionalIdeal.count K v (assocIdeal R K x) = expAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_support_expAt R K x))

/--
@isnad1 id=eq.0h4v.s8.bbcd1109a143 from=translated src=- shape=633373f7 vocab=00fac4ff
-/
theorem assocIdeal_mul (x y : (FiniteAdeleRing R K)ˣ) :
    assocIdeal R K (x * y) = assocIdeal R K x * assocIdeal R K y := by
  unfold assocIdeal
  rw [← finprod_mul_distrib
    ((finite_support_expAt R K x).subset (mulSupport_zpow_subset R K _))
    ((finite_support_expAt R K y).subset (mulSupport_zpow_subset R K _))]
  apply finprod_congr
  intro v
  rw [expAt_mul, zpow_add₀ (coeIdeal_asIdeal_ne_zero R K v)]

/--
@isnad1 id=eq.3h4v.s8.36154c27b8c0 from=translated src=- shape=9a3813cf vocab=10192a9f
-/
theorem fractionalIdeal_eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  calc I = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v I) :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
  _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v J) := finprod_congr fun v => by rw [h v]
  _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

def contentHom : (FiniteAdeleRing R K)ˣ →* ClassGroup R where
  toFun x := ClassGroup.mk (K := K) (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x))
  map_one' := by
    have h1 : assocIdeal R K (1 : (FiniteAdeleRing R K)ˣ) = 1 := by
      unfold assocIdeal
      rw [finprod_eq_one_of_forall_eq_one]
      intro v
      rw [expAt_one, zpow_zero]
    rw [← map_one (ClassGroup.mk (R := R) (K := K))]
    congr 1
    exact Units.ext (by simpa using h1)
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using assocIdeal_mul R K x y)

/--
@isnad1 id=eq.0h3v.s10.9b5c97cfd0b9 from=translated src=- shape=9f457cc6 vocab=b7b00555
-/
@[scoped simp] lemma contentHom_apply (x : (FiniteAdeleRing R K)ˣ) :
    contentHom R K x = ClassGroup.mk (K := K) (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x)) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.b31e880f840d from=translated src=- shape=34a4e00f vocab=ce6fbd6c
-/
theorem count_spanSingleton_eq_neg_log_valuation (v : HeightOneSpectrum R) (u : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (u : K)) =
      -log (v.valuation K (u : K)) := by
  classical
  rw [← valuationOfNeZeroToFun_eq v u]
  set n : R := (IsLocalization.sec R⁰ (u : K)).1 with hn
  set d : ↥R⁰ := (IsLocalization.sec R⁰ (u : K)).2 with hd
  have hsec : (u : K) * algebraMap R K (d : R) = algebraMap R K n :=
    IsLocalization.sec_spec R⁰ (u : K)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have h_aJ : FractionalIdeal.spanSingleton R⁰ (u : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (d : R)))⁻¹ * ↑(Ideal.span {n}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp
    linear_combination hsec
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero) h_aJ]
  show _ = -log ((valuationOfNeZeroToFun v u : Multiplicative ℤ) : ℤᵐ⁰)
  rw [valuationOfNeZeroToFun]
  simp only [← hn, ← hd]
  rw [show ((Multiplicative.ofAdd _ : Multiplicative ℤ) : ℤᵐ⁰) = exp _ from rfl, log_exp]
  ring

/--
@isnad1 id=eq.0h4v.s8.d4d8fa38ff3d from=translated src=- shape=88be8308 vocab=21315934
-/
lemma valued_coe_eq_valuation (v : HeightOneSpectrum R) (k : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  show Valued.v ((k : v.adicCompletion K)) = _
  exact valuedAdicCompletion_eq_valuation' v k

/--
@isnad1 id=eq.0h4v.s9.0a4a7de9626f from=translated src=- shape=c6fed130 vocab=acc336b6
-/
theorem expAt_principal (v : HeightOneSpectrum R) (u : Kˣ) :
    expAt R K v (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      -log (v.valuation K (u : K)) := by
  unfold expAt
  rw [Units.coe_map, MonoidHom.coe_coe, valued_coe_eq_valuation]

/--
@isnad1 id=eq.0h3v.s10.e261f2be9997 from=translated src=- shape=8dcba608 vocab=4686f0f7
-/
theorem contentHom_principal (u : Kˣ) :
    contentHom R K (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u)
      = 1 := by
  rw [contentHom_apply, ClassGroup.mk_eq_one_iff]
  have key : assocIdeal R K
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      FractionalIdeal.spanSingleton R⁰ (u : K) := by
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero)
    intro v
    rw [count_assocIdeal, count_spanSingleton_eq_neg_log_valuation, expAt_principal]
  simp only [Units.val_mk0, key]
  rw [FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(u : K), rfl⟩⟩

/--
@isnad1 id=eq.1h4v.s8.6c7a1b9d0179 from=translated src=- shape=56ef1d5a vocab=9ae3e353
-/
lemma expAt_eq_zero_of_mem_unitIdeles {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K)
    (v : HeightOneSpectrum R) : expAt R K v x = 0 :=
  expAt_eq_zero_of_integral R K ((mem_adicCompletionIntegers R K v).mp (h.1 v))
    ((mem_adicCompletionIntegers R K v).mp (h.2 v))

/--
@isnad1 id=mem.1h3v.s8.46576ca9be47 from=translated src=- shape=262852c8 vocab=9ae3e353
-/
lemma mem_unitIdeles_of_expAt_eq_zero {x : (FiniteAdeleRing R K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, expAt R K v x = 0) : x ∈ unitIdeles R K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x).mp (h v)).le
  · have h' : expAt R K v x⁻¹ = 0 := by rw [expAt_inv, h v, neg_zero]
    exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x⁻¹).mp h').le

/--
@isnad1 id=eq.1h3v.s9.202171ab6fd3 from=translated src=- shape=4e86b294 vocab=7b59a0ac
-/
theorem contentHom_eq_one_of_mem_unitIdeles {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K) :
    contentHom R K x = 1 := by
  have h1 : assocIdeal R K x = 1 := by
    unfold assocIdeal
    rw [finprod_eq_one_of_forall_eq_one]
    intro v
    rw [expAt_eq_zero_of_mem_unitIdeles R K h v, zpow_zero]
  rw [contentHom_apply, ← map_one (ClassGroup.mk (R := R) (K := K))]
  congr 1
  exact Units.ext (by simpa using h1)

/--
@isnad1 id=eq.0h2v.s10.0aa4b2030f9c from=translated src=- shape=b6db42b6 vocab=42c6e1fc
-/
theorem ker_contentHom_eq :
    (contentHom R K).ker = unitIdeles R K ⊔
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, contentHom_apply, ClassGroup.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx.principal
    have ha' : assocIdeal R K x = FractionalIdeal.spanSingleton R⁰ a := by
      apply FractionalIdeal.coeToSubmodule_injective
      show (assocIdeal R K x : Submodule R K) = (FractionalIdeal.spanSingleton R⁰ a : Submodule R K)
      rw [FractionalIdeal.coe_spanSingleton]
      simpa using ha
    have ha0 : a ≠ 0 := by
      intro h0
      apply assocIdeal_ne_zero R K x
      rw [ha', h0, FractionalIdeal.spanSingleton_zero]
    set u : Kˣ := Units.mk0 a ha0 with hu
    set p : (FiniteAdeleRing R K)ˣ :=
      Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u with hp
    have hquot : x * p⁻¹ ∈ unitIdeles R K := by
      apply mem_unitIdeles_of_expAt_eq_zero
      intro v
      rw [expAt_mul, expAt_inv]
      have h1 : expAt R K v x = FractionalIdeal.count K v (assocIdeal R K x) :=
        (count_assocIdeal R K v x).symm
      have h2 : expAt R K v p = FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
        rw [hp, expAt_principal, count_spanSingleton_eq_neg_log_valuation]
      rw [h1, h2, ha']
      simp [hu]
    have hxp : x = (x * p⁻¹) * p := by group
    rw [hxp]
    exact Subgroup.mul_mem_sup hquot ⟨u, rfl⟩
  · rw [sup_le_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      exact contentHom_eq_one_of_mem_unitIdeles R K hx
    · rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      exact contentHom_principal R K u

private lemma log_exp_neg_one_pow (n : ℕ) : log ((exp (-1 : ℤ)) ^ n) = -(n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, log_one]; simp
  | succ n ih =>
    rw [pow_succ, log_mul (pow_ne_zero _ exp_ne_zero) exp_ne_zero, ih, log_exp]
    push_cast
    ring

/--
@isnad1 id=surjecti.0h2v.s9.cd403a7f7263 from=translated src=- shape=e586f858 vocab=1b5a07e6
-/
theorem contentHom_surjective : Function.Surjective (contentHom R K) := by
  classical
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  choose π hπ using fun v : HeightOneSpectrum R => valuation_exists_uniformizer K v
  set n : HeightOneSpectrum R → ℕ :=
    fun v => (FractionalIdeal.count K v (I : FractionalIdeal R⁰ K)).toNat with hn_def
  have hn : ∀ v, (n v : ℤ) = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := fun v =>
    Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v _)
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 :=
    (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).mono fun v hv => by
      simp [hn_def, hv]
  have hval : ∀ v : HeightOneSpectrum R,
      Valued.v ((algebraMap K (FiniteAdeleRing R K) (π v)) v) = exp (-1 : ℤ) := fun v => by
    rw [valued_coe_eq_valuation, hπ v]

  set a : (v : HeightOneSpectrum R) → v.adicCompletion K :=
    fun v => (algebraMap K (FiniteAdeleRing R K) (π v)) v with ha_def
  have hva : ∀ v, Valued.v (a v) = exp (-1 : ℤ) := fun v => hval v
  have ha0 : ∀ v, a v ≠ 0 := fun v => by
    intro h
    have := hva v
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hale : ∀ v, Valued.v (a v) ≤ 1 := fun v => by
    rw [hva v, ← exp_zero, exp_le_exp]
    norm_num
  let f : FiniteAdeleRing R K :=
    ⟨fun v => a v ^ n v, Filter.Eventually.of_forall fun v =>
      (mem_adicCompletionIntegers R K v).mpr (by
        rw [map_pow]
        exact pow_le_one₀ zero_le (hale v))⟩
  let g : FiniteAdeleRing R K :=
    ⟨fun v => (a v)⁻¹ ^ n v, hfin.mono fun v hv => by
      simp only at hv ⊢
      rw [hv, pow_zero]
      exact one_mem _⟩
  have hfg : f * g = 1 := RestrictedProduct.ext _ _ fun v => by
    show a v ^ n v * (a v)⁻¹ ^ n v = 1
    rw [← mul_pow, mul_inv_cancel₀ (ha0 v), one_pow]
  have hgf : g * f = 1 := by rw [mul_comm]; exact hfg
  set j : (FiniteAdeleRing R K)ˣ := ⟨f, g, hfg, hgf⟩ with hj
  refine ⟨j, ?_⟩
  have hexp : ∀ w : HeightOneSpectrum R, expAt R K w j =
      FractionalIdeal.count K w (I : FractionalIdeal R⁰ K) := fun w => by
    rw [← hn w, expAt]
    show -log (Valued.v (a w ^ n w)) = _
    rw [map_pow, hva w, log_exp_neg_one_pow, neg_neg]
  have hassoc : assocIdeal R K j = (I : FractionalIdeal R⁰ K) := by
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K j)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I))
    intro v
    rw [count_assocIdeal, hexp v]
  rw [contentHom_apply, ← hI, ← ClassGroup.mk_mk0 K]
  congr 1
  exact Units.ext (by simpa using hassoc)

end

end IsDedekindDomain.FiniteAdeleRing.P2MIdeleContent
open scoped _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain.FiniteAdeleRing _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain.FiniteAdeleRing.P2MIdeleContent
open scoped _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain.FiniteAdeleRing
open scoped _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain

open _root_.IsDedekindDomain _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_nonempty_classGroup_mulEquiv_units_quotient_unitIdeles_sup_range.IsDedekindDomain in
/--
@isnad1 id=nonempty.0h2v.s12.00d36ea42c97 from=translated src=- shape=5205962c vocab=a01ebd28
-/
theorem solution
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Nonempty (ClassGroup R ≃* (FiniteAdeleRing R K)ˣ ⧸
      (IsDedekindDomain.FiniteAdeleRing.unitIdeles R K ⊔
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range)) :=
  ⟨((QuotientGroup.quotientKerEquivOfSurjective _
      (IsDedekindDomain.FiniteAdeleRing.P2MIdeleContent.contentHom_surjective R K)).symm).trans
    (QuotientGroup.quotientMulEquivOfEq
      (IsDedekindDomain.FiniteAdeleRing.P2MIdeleContent.ker_contentHom_eq R K))⟩
