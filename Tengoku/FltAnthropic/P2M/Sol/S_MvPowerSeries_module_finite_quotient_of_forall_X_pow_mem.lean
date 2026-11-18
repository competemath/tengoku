import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_module_finite_quotient_of_forall_X_pow_mem

set_option autoImplicit false

universe u v w

open MvPowerSeries

namespace TruncFinEngine

section L0

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

omit [Finite σ] in

/--
@isnad1 id=ex.1h3v.s8.b65492eb050e from=translated src=- shape=0700483c vocab=96386928
-/
theorem exists_le_degree_eq (N : ℕ) (x : σ →₀ ℕ) (hx : N ≤ x.degree) :
    ∃ y : σ →₀ ℕ, y ≤ x ∧ y.degree = N := by
  classical
  induction N with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨y, hyx, hyn⟩ := ih ((Nat.le_succ n).trans hx)
    have hne : x - y ≠ 0 := by
      intro h
      have hle : x ≤ y := tsub_eq_zero_iff_le.mp h
      have : x = y := le_antisymm hle hyx
      subst this
      omega
    obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne (Finsupp.ext hcon)
    refine ⟨y + Finsupp.single i 1, ?_, by simp [hyn]⟩
    intro j
    simp only [Finsupp.coe_add, Pi.add_apply]
    have hyj : y j ≤ x j := hyx j
    have hij : (x - y) i = x i - y i := Finsupp.tsub_apply x y i
    by_cases h : i = j
    · subst h
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_apply, ite_eq_right h]
      omega

omit [Finite σ] in

/--
@isnad1 id=mem.0h3v.s8.f9fe67b8e233 from=translated src=- shape=662cdc93 vocab=a4f002cd
-/
theorem monomial_one_mem_pow_span_X (y : σ →₀ ℕ) :
    (monomial y (1 : R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ y.degree := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.prod_mem_prod fun i _ => ?_
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

/--
@isnad1 id=mem.2h5v.s9.4b9f33f84943 from=translated src=- shape=4056441e vocab=084fdc06
-/
theorem mem_of_forall_coeff_eq_zero_of_forall_monomial_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I)
    (q : MvPowerSeries σ R) (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ I := by
  classical

  have hY : ∀ x : σ →₀ ℕ, ∃ y : σ →₀ ℕ, N ≤ x.degree → y ≤ x ∧ y.degree = N := by
    intro x
    by_cases hx : N ≤ x.degree
    · obtain ⟨y, hy⟩ := exists_le_degree_eq N x hx
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose Y hY using hY
  set D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le N).toFinset.filter fun y => y.degree = N
    with hD
  have hmemD : ∀ y, y ∈ D ↔ y.degree = N := by
    intro y
    simp only [hD, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    intro h; exact h.le

  let r : (σ →₀ ℕ) → MvPowerSeries σ R := fun y z =>
    if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0
  have hr : ∀ y z, coeff z (r y) = if N ≤ (z + y).degree ∧ Y (z + y) = y then coeff (z + y) q else 0 :=
    fun y z => rfl
  have hdecomp : q = ∑ y ∈ D, monomial y (1 : R) * r y := by
    ext x
    rw [map_sum]
    simp_rw [coeff_monomial_mul, one_mul]
    by_cases hx : N ≤ x.degree
    · obtain ⟨hYx, hYdeg⟩ := hY x hx
      rw [Finset.sum_eq_single (Y x)]
      · rw [ite_eq_left hYx, hr, tsub_add_cancel_of_le hYx, ite_eq_left ⟨hx, rfl⟩]
      · intro y _ hne
        split_ifs with hyx
        · rw [hr, tsub_add_cancel_of_le hyx]
          rw [ite_eq_right]
          rintro ⟨_, h⟩
          exact hne h.symm
        · rfl
      · intro h
        exact absurd ((hmemD _).mpr hYdeg) h
    · rw [hq x (not_le.mp hx)]
      symm
      refine Finset.sum_eq_zero fun y hy => ?_
      split_ifs with hyx
      · exfalso
        have := Finsupp.degree_mono hyx
        rw [(hmemD y).mp hy] at this
        exact hx this
      · rfl
  rw [hdecomp]
  refine Ideal.sum_mem _ fun y hy => ?_
  exact Ideal.mul_mem_right _ _ (hI y ((hmemD y).mp hy))

/--
@isnad1 id=mem.1h4v.s8.a312e76865cc from=translated src=- shape=2d8c0d7a vocab=f42a41ea
-/
theorem mem_pow_span_X_of_forall_coeff_eq_zero (N : ℕ) (q : MvPowerSeries σ R)
    (hq : ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0) :
    q ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N :=
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N _
    (fun y hy => hy ▸ monomial_one_mem_pow_span_X (R := R) y) q hq

end L0

section Trunc

variable {σ : Type w} [Finite σ] {R : Type u} [CommRing R]

/--
@isnad1 id=mem.0h4v.s8.dbb75688a110 from=translated src=- shape=65ccd6fa vocab=a67728b4
-/
theorem sub_coe_truncTotal_mem_pow_span_X (N : ℕ) (q : MvPowerSeries σ R) :
    q - ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N := by
  refine mem_pow_span_X_of_forall_coeff_eq_zero N _ fun x hx => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]

/--
@isnad1 id=eq.1h5v.s10.d62c85c43d5f from=translated src=- shape=aaf3a2d9 vocab=0aa2f148
-/
theorem mk_coe_truncTotal (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I) (q : MvPowerSeries σ R) :
    Ideal.Quotient.mk I ((truncTotal N q : MvPolynomial σ R) : MvPowerSeries σ R) =
      Ideal.Quotient.mk I q := by
  rw [Ideal.Quotient.eq]
  have := hI (sub_coe_truncTotal_mem_pow_span_X N q)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

end Trunc

section Bridges

variable {σ : Type w} {R : Type u} [CommRing R]

def lowVanishing (σ : Type w) (R : Type u) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {q | ∀ x : σ →₀ ℕ, x.degree < N → coeff x q = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [map_zero]
  smul_mem' a q hq x hx := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : ij.2 ≤ x := hij ▸ le_add_self
    rw [hq ij.2 ((Finsupp.degree_mono hj).trans_lt hx), mul_zero]

/--
@isnad1 id=le.0h2v.s6.6a9c689ddab5 from=translated src=- shape=3e3f7c07 vocab=e73b6955
-/
theorem span_X_le_lowVanishing_one :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ lowVanishing σ R 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩ x hx
  have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
  subst hx0
  exact coeff_zero_X i

/--
@isnad1 id=le.0h4v.s7.9959bb0dcbc9 from=translated src=- shape=89c991c5 vocab=b9575bb4
-/
theorem lowVanishing_mul_le (a b : ℕ) :
    lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro r hr s hs x hx
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : ij.1.degree < a
  · rw [hr ij.1 hi, zero_mul]
  · have hdeg : x.degree = ij.1.degree + ij.2.degree := by rw [← hij, map_add]
    have hj : ij.2.degree < b := by omega
    rw [hs ij.2 hj, mul_zero]

/--
@isnad1 id=le.0h3v.s7.b2e612fc4233 from=translated src=- shape=d4143556 vocab=28b45ccf
-/
theorem pow_span_X_le_lowVanishing (N : ℕ) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ lowVanishing σ R N := by
  induction N with
  | zero =>
    intro q _ x hx
    exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowVanishing_one).trans (lowVanishing_mul_le n 1)

/--
@isnad1 id=le.1h4v.s9.8e13e288c429 from=translated src=- shape=e4252ada vocab=df67e4cc
-/
theorem pow_span_X_le_of_forall_monomial_mem [Finite σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ y : σ →₀ ℕ, y.degree = N → (monomial y (1 : R) : MvPowerSeries σ R) ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ N ≤ I := fun q hq =>
  mem_of_forall_coeff_eq_zero_of_forall_monomial_mem N I hI q (pow_span_X_le_lowVanishing N hq)

/--
@isnad1 id=le.1h4v.s8.627cf54fe0a2 from=translated src=- shape=ffecf0ee vocab=dab924e1
-/
theorem pow_span_X_le_of_forall_X_pow_mem [Fintype σ] (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ (Fintype.card σ * (N - 1) + 1) ≤ I := by
  classical
  refine pow_span_X_le_of_forall_monomial_mem _ I fun y hy => ?_

  obtain ⟨i, hi⟩ : ∃ i, N ≤ y i := by
    by_contra hcon
    push Not at hcon
    have hle : y.degree ≤ Fintype.card σ * (N - 1) := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, y i ≤ ∑ _i : σ, (N - 1) := Finset.sum_le_sum fun i _ => by have := hcon i; omega
        _ = Fintype.card σ * (N - 1) := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    omega
  have hsplit : y = Finsupp.single i N + (y - Finsupp.single i N) := by
    rw [add_tsub_cancel_of_le]
    intro j
    by_cases hij : i = j
    · subst hij; rwa [Finsupp.single_eq_same]
    · rw [Finsupp.single_apply, ite_eq_right hij]; exact Nat.zero_le _
  rw [hsplit, ← one_mul (1 : R), ← monomial_mul_monomial, ← X_pow_eq]
  exact Ideal.mul_mem_right _ _ (hI i)

end Bridges

section Finite

variable {σ : Type} [Fintype σ] [DecidableEq σ] {R : Type} [CommRing R]

/--
@isnad1 id=finite.1h4v.s8.1cf5b76cf799 from=translated src=- shape=30171ee8 vocab=670a0b17
-/
theorem finite_quotient_of_forall_X_pow_mem (N : ℕ) (I : Ideal (MvPowerSeries σ R))
    (hI : ∀ i : σ, (X i : MvPowerSeries σ R) ^ N ∈ I) : Module.Finite R (MvPowerSeries σ R ⧸ I) := by
  classical
  set M : ℕ := Fintype.card σ * (N - 1) + 1 with hM
  have hpow := pow_span_X_le_of_forall_X_pow_mem N I hI

  let Φ : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R ⧸ I :=
    (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ (MvPolynomial.coeToMvPowerSeries.algHom R).toLinearMap
  let Ψ : ↥(MvPolynomial.restrictTotalDegree σ R M) →ₗ[R] MvPowerSeries σ R ⧸ I := Φ ∘ₗ (Submodule.subtype _)
  haveI : Module.Finite R ↥(MvPolynomial.restrictTotalDegree σ R M) := inferInstance
  refine Module.Finite.of_surjective Ψ fun x => ?_
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨⟨truncTotal M q, ?_⟩, ?_⟩
  · rw [MvPolynomial.mem_restrictTotalDegree]
    exact (totalDegree_truncTotal_lt q (by omega)).le
  · show (Ideal.Quotient.mk I) ((truncTotal M q : MvPolynomial σ R) : MvPowerSeries σ R) = Ideal.Quotient.mk I q
    exact mk_coe_truncTotal M I hpow q

end Finite

end TruncFinEngine

open TruncFinEngine in
/--
@isnad1 id=finite.1h4v.s8.119c6c376f8c from=translated src=- shape=6f943d13 vocab=a859025c
-/
theorem solution
    {σ : Type} [Fintype σ] {R : Type} [CommRing R] (I : Ideal (MvPowerSeries σ R)) (N : ℕ)
    (hI : ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) := by
  classical
  exact finite_quotient_of_forall_X_pow_mem N I hI
