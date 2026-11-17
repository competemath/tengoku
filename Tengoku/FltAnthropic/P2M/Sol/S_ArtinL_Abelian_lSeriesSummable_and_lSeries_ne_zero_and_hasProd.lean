import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ArtinL_Abelian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Filter Topology
open scoped Classical

universe u v

namespace ArtinEulerProof

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

def cnt (v : HeightOneSpectrum R) (I : Ideal R) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

/--
@isnad1 id=eq.2h4v.s7.ebfbcc770efb from=translated src=- shape=ea8eeb30 vocab=9b385b58
-/
theorem cnt_mul {I J : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (v : HeightOneSpectrum R) :
    cnt v (I * J) = cnt v I + cnt v J := by
  unfold cnt
  rw [← Associates.mk_mul_mk]
  exact Associates.count_mul (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    v.associates_irreducible

/--
@isnad1 id=eq.1h4v.s7.f323c31104f3 from=translated src=- shape=2cadee2b vocab=b4a82182
-/
theorem cnt_pow {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (n : ℕ) :
    cnt v (I ^ n) = n * cnt v I := by
  unfold cnt
  rw [Associates.mk_pow]
  exact Associates.count_pow (Associates.mk_ne_zero.mpr hI) v.associates_irreducible n

/--
@isnad1 id=eq.0h2v.s4.3447431f93f9 from=translated src=- shape=3c534a39 vocab=a3afc9e0
-/
theorem cnt_self (v : HeightOneSpectrum R) : cnt v v.asIdeal = 1 := by
  unfold cnt
  exact Associates.count_self v.associates_irreducible

/--
@isnad1 id=eq.1h3v.s5.697c9d634470 from=translated src=- shape=da8bbbea vocab=a3afc9e0
-/
theorem cnt_eq_zero_of_ne {v w : HeightOneSpectrum R} (h : v ≠ w) : cnt v w.asIdeal = 0 := by
  unfold cnt
  refine Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible ?_
  intro heq
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at heq
  exact h (HeightOneSpectrum.ext heq)

/--
@isnad1 id=eq.0h2v.s5.bfc2cfcfcd60 from=translated src=- shape=0b62b1dd vocab=72eb0289
-/
theorem cnt_top (v : HeightOneSpectrum R) : cnt v (⊤ : Ideal R) = 0 := by
  unfold cnt
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
  exact Associates.count_zero v.associates_irreducible

/--
@isnad1 id=iff.1h3v.s7.b76273967d7b from=translated src=- shape=c19ba98a vocab=c1a2de0b
-/
theorem cnt_ne_zero_iff {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) :
    cnt v I ≠ 0 ↔ v.asIdeal ∣ I :=
  Associates.count_ne_zero_iff_dvd hI v.irreducible

/--
@isnad1 id=eq.1h5v.s7.1b752a9e5859 from=translated src=- shape=6bddeae2 vocab=cd01a923
-/
theorem cnt_finsetProd {ι : Type*} (s : Finset ι) (f : ι → Ideal R) (hf : ∀ i ∈ s, f i ≠ ⊥)
    (v : HeightOneSpectrum R) : cnt v (∏ i ∈ s, f i) = ∑ i ∈ s, cnt v (f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, cnt_top]
  | insert a s ha ih =>
    have hprod : ∏ i ∈ s, f i ≠ ⊥ :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      cnt_mul (hf a (Finset.mem_insert_self a s)) hprod,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

def ofExp (c : HeightOneSpectrum R →₀ ℕ) : Ideal R := c.prod fun v e => v.asIdeal ^ e

/--
@isnad1 id=ne.0h2v.s5.8e42ea37efe5 from=translated src=- shape=8cdb5231 vocab=2707bb39
-/
theorem ofExp_ne_bot (c : HeightOneSpectrum R →₀ ℕ) : ofExp c ≠ ⊥ := by
  unfold ofExp Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot

/--
@isnad1 id=eq.0h3v.s5.f938babe6b73 from=translated src=- shape=f63a5fc6 vocab=78d00a8f
-/
theorem cnt_ofExp (c : HeightOneSpectrum R →₀ ℕ) (v : HeightOneSpectrum R) :
    cnt v (ofExp c) = c v := by
  unfold ofExp Finsupp.prod
  rw [cnt_finsetProd _ _ fun w _ => pow_ne_zero _ w.ne_bot]
  simp_rw [cnt_pow (HeightOneSpectrum.ne_bot _)]
  rw [Finset.sum_eq_single v]
  · rw [cnt_self, mul_one]
  · intro w _ hw
    rw [cnt_eq_zero_of_ne (Ne.symm hw), mul_zero]
  · intro hv
    rw [Finsupp.notMem_support_iff.mp hv, zero_mul]

/--
@isnad1 id=finite.1h2v.s6.abb61203e362 from=translated src=- shape=c5b70241 vocab=dd5f59b4
-/
theorem finite_support_cnt {I : Ideal R} (hI : I ≠ ⊥) :
    (Function.support fun v : HeightOneSpectrum R => cnt v I).Finite :=
  (Ideal.finite_factors hI).subset fun v hv => (cnt_ne_zero_iff hI v).mp hv

def exps (I : Ideal R) (hI : I ≠ ⊥) : HeightOneSpectrum R →₀ ℕ :=
  Finsupp.ofSupportFinite (fun v => cnt v I) (finite_support_cnt hI)

/--
@isnad1 id=eq.1h3v.s6.527ce59c5ece from=translated src=- shape=1f2b4072 vocab=7a52ae74
-/
theorem exps_apply {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) :
    exps I hI v = cnt v I := rfl

/--
@isnad1 id=eq.1h2v.s6.df8cbef8e2ef from=translated src=- shape=fd242949 vocab=8b9e8a04
-/
theorem ofExp_exps {I : Ideal R} (hI : I ≠ ⊥) : ofExp (exps I hI) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  unfold ofExp Finsupp.prod
  rw [finprod_eq_prod_of_mulSupport_subset (s := (exps I hI).support)]
  · rfl
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hv
    change v.asIdeal ^ cnt v I = 1
    rw [← exps_apply hI, h, pow_zero]

def idealEquiv : (HeightOneSpectrum R →₀ ℕ) ≃ {I : Ideal R // I ≠ ⊥} where
  toFun c := ⟨ofExp c, ofExp_ne_bot c⟩
  invFun I := exps I.1 I.2
  left_inv c := by
    ext v
    rw [exps_apply, cnt_ofExp]
  right_inv I := Subtype.ext (ofExp_exps I.2)

/--
@isnad1 id=eq.0h4v.s6.97e7ab3ea395 from=translated src=- shape=bfcd8720 vocab=ec6f4844
-/
theorem finprod_pow_cnt_ofExp {N : Type*} [CommMonoid N] (f : HeightOneSpectrum R → N)
    (c : HeightOneSpectrum R →₀ ℕ) :
    ∏ᶠ v, f v ^ cnt v (ofExp c) = c.prod fun v e => f v ^ e := by
  simp_rw [cnt_ofExp]
  unfold Finsupp.prod
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  rw [Function.mem_mulSupport] at hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  exact hv (by rw [h, pow_zero])

end Dedekind

section Cpow

/--
@isnad1 id=eq.0h4v.s5.164cb7f6550c from=translated src=- shape=5d88cc5c vocab=cde60e62
-/
theorem natCast_prod_cpow {ι : Type*} (s : Finset ι) (n : ι → ℕ) (z : ℂ) :
    (((∏ i ∈ s, n i : ℕ)) : ℂ) ^ z = ∏ i ∈ s, ((n i : ℂ) ^ z) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Nat.cast_one, Complex.one_cpow]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/--
@isnad1 id=eq.0h3v.s5.e8bf77b47813 from=translated src=- shape=ab709254 vocab=cb498106
-/
theorem natCast_pow_cpow (n e : ℕ) (z : ℂ) : (((n ^ e : ℕ)) : ℂ) ^ z = ((n : ℂ) ^ z) ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, Nat.cast_one, Complex.one_cpow]
  | succ e ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/--
@isnad1 id=eq.1h2v.s5.17011dd24305 from=translated src=- shape=0445874f vocab=47b535c4
-/
theorem norm_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

end Cpow

section NumberField

variable {K : Type u} [Field K] [NumberField K]

/--
@isnad1 id=eq.0h2v.s8.3be3d5be795b from=translated src=- shape=bb09eea9 vocab=c9d64453
-/
theorem absNorm_ofExp (c : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    Ideal.absNorm (ofExp c) = c.prod fun v e => Ideal.absNorm v.asIdeal ^ e := by
  unfold ofExp Finsupp.prod
  rw [map_prod]
  simp_rw [map_pow]

/--
@isnad1 id=lt.0h2v.s7.f7f552292c8c from=translated src=- shape=0bd4bc8f vocab=ec07a487
-/
theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

/--
@isnad1 id=lt.0h2v.s7.d4c8d5812d77 from=translated src=- shape=0bd4bc8f vocab=ec07a487
-/
theorem absNorm_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  zero_lt_one.trans (one_lt_absNorm v)

variable (K) in

/--
@isnad1 id=tendsto.0h1v.s8.1feca127ef08 from=translated src=- shape=407a341b vocab=cc07ac29
-/
theorem tendsto_sum_card_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * Units.regulator K *
        classNumber K) / (Units.torsionOrder K * Real.sqrt |discr K|))) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

variable (K) in

/--
@isnad1 id=lseriess.1h2v.s8.984ec9d32625 from=translated src=- shape=0d9be476 vocab=cc6b80af
-/
theorem summable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := by
  set d : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) with hd
  have h1 := (tendsto_sum_card_div K).isBigO_one ℝ
  have h2 : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, d k) =ᶠ[atTop]
      fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, d k) / n * n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, d k) =O[atTop] fun n => (n : ℝ) ^ (1 : ℝ) := by
    refine h2.trans_isBigO ?_
    have h3 := h1.mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
    refine h3.congr_right fun n => ?_
    rw [Real.rpow_one, one_mul]
  have h4 := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n => Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  refine (LSeriesSummable_congr s fun {n} _ => ?_).1 h4
  simp [hd]

variable (K) in

/--
@isnad1 id=summable.1h2v.s8.93e4a27e44ba from=translated src=- shape=30ab156a vocab=865971a7
-/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
  set f : Ideal (𝓞 K) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-σ) with hf_def
  have hf : ∀ I, 0 ≤ f I := fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))
  rw [← e.summable_iff]
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := fun n =>
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  refine (summable_sigma_of_nonneg fun x => hf _).mpr ⟨fun n => ?_, ?_⟩
  · haveI := hfin n
    exact Summable.of_finite
  · have key : ∀ n : ℕ, ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (f ∘ e) ⟨n, I⟩ =
        Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} * (n : ℝ) ^ (-σ) := by
      intro n
      haveI := hfin n
      letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
      rw [tsum_fintype]
      have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
          (f ∘ e) ⟨n, I⟩ = (n : ℝ) ^ (-σ) := fun I => by
        show (Ideal.absNorm I.1 : ℝ) ^ (-σ) = _
        rw [I.2]
      simp_rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    refine Summable.congr ?_ fun n => (key n).symm
    have h := (summable_card_absNorm K (s := (σ : ℂ)) (by simpa using hσ)).norm
    refine h.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · rw [hn, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr (by linarith)), mul_zero]
    · rw [Complex.norm_natCast, Complex.ofReal_re, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg _)]

variable {M : Type v} [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/--
@isnad1 id=eq.0h4v.s8.1901f079eded from=translated src=- shape=13da0cd9 vocab=91ffb4ee
-/
theorem idealValue_eq (I : Ideal (𝓞 K)) :
    ArtinL.Abelian.idealValue ψ I = ∏ᶠ v, ArtinL.Abelian.localValue ψ v ^ cnt v I := rfl

/--
@isnad1 id=le.0h4v.s7.19e678faab30 from=translated src=- shape=941d742e vocab=39809bee
-/
theorem norm_localValue_le (v : HeightOneSpectrum (𝓞 K)) :
    ‖ArtinL.Abelian.localValue ψ v‖ ≤ 1 := by
  unfold ArtinL.Abelian.localValue
  split_ifs
  · exact (ArtinL.Abelian.norm_apply ψ _).le
  · simp

/--
@isnad1 id=le.0h4v.s7.c672d869ef72 from=translated src=- shape=941d742e vocab=66e0a556
-/
theorem norm_idealValue_le (I : Ideal (𝓞 K)) : ‖ArtinL.Abelian.idealValue ψ I‖ ≤ 1 := by
  rw [idealValue_eq]
  refine finprod_induction (fun x : ℂ => ‖x‖ ≤ 1) ?_ ?_ ?_
  · show ‖(1 : ℂ)‖ ≤ 1
    rw [norm_one]
  · intro x y hx hy
    show ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro v
    show ‖ArtinL.Abelian.localValue ψ v ^ cnt v I‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_localValue_le ψ v)

/--
@isnad1 id=eq.0h4v.s8.2b2f031950e0 from=translated src=- shape=254ae8ff vocab=095e7693
-/
theorem idealValue_ofExp (c : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    ArtinL.Abelian.idealValue ψ (ofExp c) = c.prod fun v e => ArtinL.Abelian.localValue ψ v ^ e := by
  rw [idealValue_eq]
  exact finprod_pow_cnt_ofExp _ c

def wt (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

private def _root_.ArtinEulerProof.term (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  ArtinL.Abelian.idealValue ψ I * (Ideal.absNorm I : ℂ) ^ (-s)

export _root_.ArtinEulerProof (term)

def wtProd (s : ℂ) (c : HeightOneSpectrum (𝓞 K) →₀ ℕ) : ℂ :=
  c.prod fun v e => wt ψ s v ^ e

/--
@isnad1 id=eq.0h5v.s7.c6d1a4afab6a from=translated src=- shape=9c907877 vocab=60f21286
-/
theorem term_ofExp (s : ℂ) (c : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    term ψ s (ofExp c) = wtProd ψ s c := by
  unfold term wtProd wt
  rw [idealValue_ofExp, absNorm_ofExp]
  unfold Finsupp.prod
  rw [natCast_prod_cpow]
  simp_rw [natCast_pow_cpow, ← Finset.prod_mul_distrib, ← mul_pow]

/--
@isnad1 id=eq.1h4v.s8.b9ac11a7884b from=translated src=- shape=63e66286 vocab=74ed47e0
-/
theorem term_bot {s : ℂ} (hs : s ≠ 0) : term ψ s ⊥ = 0 := by
  unfold term
  rw [Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs), mul_zero]

/--
@isnad1 id=le.0h5v.s8.8539a8ff95ac from=translated src=- shape=a98b408c vocab=1632ba33
-/
theorem norm_wt_le (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    ‖wt ψ s v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold wt
  rw [norm_mul, norm_natCast_cpow_neg (absNorm_pos v)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_localValue_le ψ v)

/--
@isnad1 id=le.1h5v.s8.75aaebe8ac62 from=translated src=- shape=d3730e10 vocab=dea4d414
-/
theorem norm_wt_le_half {s : ℂ} (hs : 1 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖wt ψ s v‖ ≤ 1 / 2 := by
  refine (norm_wt_le ψ s v).trans ?_
  have h2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast one_lt_absNorm v
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
        Real.rpow_le_rpow_of_nonpos two_pos h2 (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/--
@isnad1 id=lt.1h5v.s7.7fca12ddcca1 from=translated src=- shape=011637e5 vocab=0479524d
-/
theorem norm_wt_lt_one {s : ℂ} (hs : 1 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖wt ψ s v‖ < 1 :=
  (norm_wt_le_half ψ hs v).trans_lt (by norm_num)

/--
@isnad1 id=le.1h5v.s8.aaad7ebef923 from=translated src=- shape=b103dcb6 vocab=fa6a1038
-/
theorem norm_term_le {s : ℂ} (hs : s ≠ 0) (I : Ideal (𝓞 K)) :
    ‖term ψ s I‖ ≤ (Ideal.absNorm I : ℝ) ^ (-s.re) := by
  unfold term
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos (Ideal.absNorm I) with hI | hpos
  · rw [hI, Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs), norm_zero,
      mul_zero]
    exact Real.rpow_nonneg le_rfl _
  · rw [norm_natCast_cpow_neg hpos]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (norm_idealValue_le ψ I)

/--
@isnad1 id=ne.1h1v.s4.353c69b16094 from=translated src=- shape=2154ac66 vocab=b7c076fb
-/
theorem ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  rintro rfl
  rw [Complex.zero_re] at hs
  linarith

/--
@isnad1 id=summable.1h4v.s8.829f9697c42f from=translated src=- shape=6b3a1d6e vocab=53ee5a1b
-/
theorem summable_norm_term {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖term ψ s I‖ :=
  (summable_absNorm_rpow K hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_term_le ψ (ne_zero_of_one_lt_re hs))

/--
@isnad1 id=summable.1h4v.s8.50ab95cb6215 from=translated src=- shape=7f061e6f vocab=182e9566
-/
theorem summable_norm_wtProd {s : ℂ} (hs : 1 < s.re) :
    Summable fun c : HeightOneSpectrum (𝓞 K) →₀ ℕ => ‖wtProd ψ s c‖ := by
  have h := (summable_norm_term ψ hs).subtype fun I : Ideal (𝓞 K) => I ≠ ⊥
  have h' := (idealEquiv (R := 𝓞 K)).summable_iff.mpr h
  refine h'.congr fun c => ?_
  show ‖term ψ s (ofExp c)‖ = _
  rw [term_ofExp]

/--
@isnad1 id=eq.1h4v.s8.7f8d71af7ec9 from=translated src=- shape=d3b8e75f vocab=3d71cadc
-/
theorem tsum_wtProd_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' c : HeightOneSpectrum (𝓞 K) →₀ ℕ, wtProd ψ s c = ∑' I : Ideal (𝓞 K), term ψ s I := by
  have h1 : ∑' c : HeightOneSpectrum (𝓞 K) →₀ ℕ, wtProd ψ s c =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, term ψ s I := by
    rw [← (idealEquiv (R := 𝓞 K)).tsum_eq]
    refine tsum_congr fun c => ?_
    show _ = term ψ s (ofExp c)
    rw [term_ofExp]
  rw [h1]
  exact tsum_subtype_eq_of_support_subset fun I hI h => by
    rw [Function.mem_support] at hI
    exact hI (h ▸ term_bot ψ (ne_zero_of_one_lt_re hs))

/--
@isnad1 id=eq.1h5v.s10.4965893b80a1 from=translated src=- shape=0c56d3d2 vocab=611b4175
-/
theorem sum_fiber_eq_term {s : ℂ} (hs : 1 < s.re) (n : ℕ)
    [Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n}] :
    ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, term ψ s (I : Ideal (𝓞 K)) =
      LSeries.term (ArtinL.Abelian.coeff ψ) s n := by
  rw [← Finset.sum_subtype (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).toFinset
    (p := fun I : Ideal (𝓞 K) => Ideal.absNorm I = n)
    (fun I => by rw [Set.Finite.mem_toFinset]; rfl) (term ψ s)]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    refine Finset.sum_eq_zero fun I hI => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Ideal.absNorm_eq_zero_iff] at hI
    rw [hI, term_bot ψ (ne_zero_of_one_lt_re hs)]
  · rw [LSeries.term_of_ne_zero hn, ArtinL.Abelian.coeff, ite_eq_right hn, div_eq_mul_inv,
      ← Complex.cpow_neg, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
    unfold term
    rw [hI]

/--
@isnad1 id=hassum.1h4v.s8.7d3972adc1f6 from=translated src=- shape=212ff607 vocab=cc9c3b27
-/
theorem hasSum_lseriesTerm {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => LSeries.term (ArtinL.Abelian.coeff ψ) s n)
      (∑' I : Ideal (𝓞 K), term ψ s I) := by
  have hsum := (summable_norm_term ψ hs).of_norm
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm (S := 𝓞 K))
  have h1 : HasSum ((term ψ s) ∘ e) (∑' I, term ψ s I) := e.hasSum_iff.mpr hsum.hasSum
  refine h1.sigma fun n => ?_
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [← sum_fiber_eq_term ψ hs n]
  exact hasSum_fintype _

/--
@isnad1 id=eq.1h4v.s8.a96901b0d252 from=translated src=- shape=c066ab0b vocab=09bdf119
-/
theorem lseries_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    ArtinL.Abelian.LSeries ψ s = ∑' I : Ideal (𝓞 K), term ψ s I :=
  (hasSum_lseriesTerm ψ hs).tsum_eq

end NumberField

section Finsupp

variable {ι : Type*}

def suppIn (S : Finset ι) : Set (ι →₀ ℕ) := {c | c.support ⊆ S}

/--
@isnad1 id=iff.0h3v.s5.b082443557d1 from=translated src=- shape=22de8101 vocab=6a5b88d0
-/
theorem mem_suppIn {S : Finset ι} {c : ι →₀ ℕ} : c ∈ suppIn S ↔ c.support ⊆ S := Iff.rfl

/--
@isnad1 id=mem.1h5v.s6.0ef29fbb10c0 from=translated src=- shape=33b96483 vocab=70abf29a
-/
theorem single_add_mem_suppIn {S : Finset ι} {a : ι} (e : ℕ) {c : ι →₀ ℕ} (hc : c ∈ suppIn S) :
    Finsupp.single a e + c ∈ suppIn (insert a S) := by
  rw [mem_suppIn] at hc ⊢
  refine Finsupp.support_add.trans ?_
  rw [Finset.insert_eq]
  exact Finset.union_subset_union Finsupp.support_single_subset hc

/--
@isnad1 id=mem.1h4v.s6.6540851ea348 from=translated src=- shape=2cd5d2d2 vocab=550b37a2
-/
theorem erase_mem_suppIn {S : Finset ι} {a : ι} {c : ι →₀ ℕ} (hc : c ∈ suppIn (insert a S)) :
    c.erase a ∈ suppIn S := by
  rw [mem_suppIn] at hc ⊢
  rw [Finsupp.support_erase]
  exact Finset.subset_insert_iff.mp hc

/--
@isnad1 id=eq.2h4v.s6.8287558db589 from=translated src=- shape=09cd8742 vocab=67bcb4a8
-/
theorem apply_eq_zero_of_mem_suppIn {S : Finset ι} {a : ι} (ha : a ∉ S) {c : ι →₀ ℕ}
    (hc : c ∈ suppIn S) : c a = 0 :=
  Finsupp.notMem_support_iff.mp fun h => ha (hc h)

def insertEquiv (S : Finset ι) {a : ι} (ha : a ∉ S) : ℕ × suppIn S ≃ suppIn (insert a S) where
  toFun x := ⟨Finsupp.single a x.1 + x.2.1, single_add_mem_suppIn x.1 x.2.2⟩
  invFun c := (c.1 a, ⟨c.1.erase a, erase_mem_suppIn c.2⟩)
  left_inv x := by
    obtain ⟨e, c, hc⟩ := x
    have hca : c a = 0 := apply_eq_zero_of_mem_suppIn ha hc
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (Finsupp.single a e + c) a = e
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hca, add_zero]
    · show (Finsupp.single a e + c).erase a = c
      rw [Finsupp.erase_add, Finsupp.erase_single, zero_add,
        Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr hca)]
  right_inv c := Subtype.ext (Finsupp.single_add_erase a c.1)

/--
@isnad1 id=eq.1h4v.s8.fdc66972bb94 from=translated src=- shape=9ffdfebb vocab=01671d6e
-/
theorem insertEquiv_apply (S : Finset ι) {a : ι} (ha : a ∉ S) (x : ℕ × suppIn S) :
    ((insertEquiv S ha x : suppIn (insert a S)) : ι →₀ ℕ) = Finsupp.single a x.1 + x.2.1 := rfl

def expProd (w : ι → ℂ) (c : ι →₀ ℕ) : ℂ := c.prod fun i e => w i ^ e

/--
@isnad1 id=eq.0h2v.s5.62a95236fe43 from=translated src=- shape=4b63daf7 vocab=ae4cf13a
-/
theorem expProd_zero (w : ι → ℂ) : expProd w 0 = 1 := Finsupp.prod_zero_index

/--
@isnad1 id=eq.0h5v.s6.db6d5e3eb906 from=translated src=- shape=5e40df74 vocab=2d6e6aa3
-/
theorem expProd_single_add (w : ι → ℂ) (a : ι) (e : ℕ) (c : ι →₀ ℕ) :
    expProd w (Finsupp.single a e + c) = w a ^ e * expProd w c := by
  unfold expProd
  rw [Finsupp.prod_add_index' (h := fun i e => w i ^ e)
      (fun i => pow_zero (w i)) (fun i e₁ e₂ => pow_add (w i) e₁ e₂),
    Finsupp.prod_single_index (h := fun i e => w i ^ e) (pow_zero (w a))]

/--
@isnad1 id=hassum.2h3v.s7.3fa45aad36f5 from=translated src=- shape=1aaf7614 vocab=b45bba25
-/
theorem hasSum_suppIn (w : ι → ℂ) (hw : ∀ i, ‖w i‖ < 1)
    (hG : Summable fun c : ι →₀ ℕ => ‖expProd w c‖) (S : Finset ι) :
    HasSum (fun c : suppIn S => expProd w c) (∏ i ∈ S, (1 - w i)⁻¹) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have h0 : (0 : ι →₀ ℕ) ∈ suppIn (∅ : Finset ι) := by
      rw [mem_suppIn, Finsupp.support_zero]
    have h1 : expProd w ((⟨0, h0⟩ : suppIn (∅ : Finset ι)) : ι →₀ ℕ) = 1 := expProd_zero w
    rw [← h1]
    refine hasSum_single (f := fun c : suppIn (∅ : Finset ι) => expProd w c)
      (⟨0, h0⟩ : suppIn (∅ : Finset ι)) ?_
    intro c hc
    exfalso
    apply hc
    refine Subtype.ext (Finsupp.support_eq_empty.mp ?_)
    exact Finset.subset_empty.mp c.2
  | insert a S ha ih =>
    have hfun : ∀ x : ℕ × suppIn S, expProd w (insertEquiv S ha x) = w a ^ x.1 * expProd w x.2 :=
      fun x => by rw [insertEquiv_apply, expProd_single_add]
    have hsum0 : Summable ((expProd w) ∘ ((↑) : suppIn (insert a S) → ι →₀ ℕ)) :=
      hG.of_norm.subtype (suppIn (insert a S))
    have hsum1 : Summable (((expProd w) ∘ ((↑) : suppIn (insert a S) → ι →₀ ℕ)) ∘
        insertEquiv S ha) :=
      (insertEquiv S ha).summable_iff.mpr hsum0
    have hsum : Summable fun x : ℕ × suppIn S => w a ^ x.1 * expProd w x.2 :=
      hsum1.congr fun x => hfun x
    have hgeo : HasSum (fun n : ℕ => w a ^ n) (1 - w a)⁻¹ := hasSum_geometric_of_norm_lt_one (hw a)
    have key : HasSum (fun x : ℕ × suppIn S => w a ^ x.1 * expProd w x.2)
        ((1 - w a)⁻¹ * ∏ i ∈ S, (1 - w i)⁻¹) := by
      apply hgeo.mul ih
      exact hsum
    rw [Finset.prod_insert ha, ← (insertEquiv S ha).hasSum_iff]
    convert key using 1
    funext x
    exact hfun x

/--
@isnad1 id=hasprod.2h2v.s7.e8e6ecdc3192 from=translated src=- shape=388dcfef vocab=c24647be
-/
theorem hasProd_one_sub_inv (w : ι → ℂ) (hw : ∀ i, ‖w i‖ < 1)
    (hG : Summable fun c : ι →₀ ℕ => ‖expProd w c‖) :
    HasProd (fun i => (1 - w i)⁻¹) (∑' c : ι →₀ ℕ, expProd w c) := by
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  have htail := tendsto_tsum_compl_atTop_zero fun c : ι →₀ ℕ => ‖expProd w c‖
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨s₀, hs₀⟩ := htail ε hε
  refine ⟨s₀.biUnion fun c => c.support, fun S hS => ?_⟩
  have hsub : (suppIn S)ᶜ ⊆ {c : ι →₀ ℕ | c ∉ s₀} := by
    intro c hc hcs
    apply hc
    rw [mem_suppIn]
    exact (Finset.subset_biUnion_of_mem (fun c : ι →₀ ℕ => c.support) hcs).trans hS
  have hGs : Summable (expProd w) := hG.of_norm
  rw [← (hasSum_suppIn w hw hG S).tsum_eq, dist_eq_norm,
    ← hGs.tsum_subtype_add_tsum_subtype_compl (suppIn S), sub_add_cancel_left, norm_neg]
  have h1 : ‖∑' c : ↥(suppIn S)ᶜ, expProd w c‖ ≤ ∑' c : ↥(suppIn S)ᶜ, ‖expProd w c‖ :=
    norm_tsum_le_tsum_norm (hG.subtype _)
  have h2 : ∑' c : ↥(suppIn S)ᶜ, ‖expProd w c‖ ≤ ∑' c : {c : ι →₀ ℕ // c ∉ s₀}, ‖expProd w c‖ :=
    Summable.tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
      (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hG.subtype _) (hG.subtype _)
  have h3 := hs₀ s₀ le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)] at h3
  exact h1.trans_lt (h2.trans_lt h3)

end Finsupp

section Main

variable {K : Type u} [Field K] [NumberField K] {M : Type v} [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/--
@isnad1 id=hasprod.1h4v.s9.637a56aad63f from=translated src=- shape=c17aa9ed vocab=ba92239f
-/
theorem hasProd_lseries {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (ArtinL.Abelian.LSeries ψ s) := by
  have h := hasProd_one_sub_inv (wt ψ s) (norm_wt_lt_one ψ hs) (summable_norm_wtProd ψ hs)
  rw [show (∑' c : HeightOneSpectrum (𝓞 K) →₀ ℕ, expProd (wt ψ s) c) =
      ∑' c, wtProd ψ s c from rfl, tsum_wtProd_eq ψ hs, ← lseries_eq_tsum ψ hs] at h
  exact h

/--
@isnad1 id=summable.1h4v.s8.2d21d63c187f from=translated src=- shape=4a40bbf1 vocab=2786bfac
-/
theorem summable_wt {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => wt ψ s v := by
  refine Summable.of_norm ?_
  have h := (summable_absNorm_rpow K hs).comp_injective
    (show Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal from
      fun v w h => HeightOneSpectrum.ext h)
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_wt_le ψ s)

/--
@isnad1 id=ne.1h4v.s7.fe20f2fd65bc from=translated src=- shape=fbb989e2 vocab=a5afb236
-/
theorem lseries_ne_zero {s : ℂ} (hs : 1 < s.re) : ArtinL.Abelian.LSeries ψ s ≠ 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), 1 - wt ψ s v ≠ 0 := fun v h => by
    have := norm_wt_lt_one ψ hs v
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  have h1 := ((summable_wt ψ hs).clog_one_sub.neg).hasSum.cexp
  have h2 : (Complex.exp ∘ fun v : HeightOneSpectrum (𝓞 K) => -Complex.log (1 - wt ψ s v)) =
      fun v => (1 - wt ψ s v)⁻¹ := by
    funext v
    rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne v)]
  rw [h2] at h1
  rw [(hasProd_lseries ψ hs).unique h1]
  exact Complex.exp_ne_zero _

end Main

end ArtinEulerProof
open scoped _root_.P2MW.S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd.ArtinEulerProof

open ArtinEulerProof in

/--
@isnad1 id=and.1h4v.s9.6bf244377651 from=translated src=- shape=fb649cab vocab=d3e01388
-/
theorem solution
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.Abelian.coeff ψ) s ∧ ArtinL.Abelian.LSeries ψ s ≠ 0 ∧
      HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - ArtinL.Abelian.localValue ψ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
        (ArtinL.Abelian.LSeries ψ s) :=
  ⟨(hasSum_lseriesTerm ψ hs).summable, lseries_ne_zero ψ hs, hasProd_lseries ψ hs⟩

end
open scoped _root_.P2MW.S_ArtinL_Abelian_lSeriesSummable_and_lSeries_ne_zero_and_hasProd.ArtinEulerProof
