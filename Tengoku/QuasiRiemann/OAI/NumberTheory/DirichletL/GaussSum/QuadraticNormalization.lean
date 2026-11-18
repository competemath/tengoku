import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def quadraticGammaO (c : O) (hc : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
    (‖eisEmbedding c‖ : ℂ)

/--
@isnad1 id=eq.0h0v.s2.1c0cc483d726 from=translated src=- shape=583fb3b9 vocab=d6f4c7dd
-/
theorem quadraticGammaO_traceLambda :
    quadraticGammaO traceLambda traceLambda_ne_zero =
      quadraticGammaTraceLambda := by rfl

/--
@isnad1 id=eq.0h0v.s5.3e134d768137 from=translated src=- shape=87ba9b6e vocab=f6de1a3b
-/
theorem quadraticGammaO_negTraceLambda :
    quadraticGammaO (-traceLambda) (neg_ne_zero.mpr traceLambda_ne_zero) =
      quadraticGammaNegTraceLambda := by rfl

/--
@isnad1 id=eq.2h1v.s6.44e534f5b3a5 from=translated src=- shape=271dedcc vocab=9b1453cb
-/
theorem quadraticGammaO_rational (m : ℕ) (hm : m ≠ 0)
    (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = quadraticGammaRational m hm := by rfl

/--
@isnad1 id=eq.3h1v.s6.b2b4d8a0cbb3 from=translated src=- shape=939420db vocab=2881d363
-/
theorem quadraticGammaO_rational_odd (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaO_rational m hm hc,
    quadraticGammaRational_eq_fourTerms m hm hodd]

end ActualEisensteinCubic

namespace PowerExtraction

/--
@isnad1 id=le.6h5v.s8.34b0694d8205 from=translated src=- shape=a1cdc2e9 vocab=5df71cf7
-/
theorem from_mean_square_and_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

/--
@isnad1 id=le.8h10v.s8.7838470bfed0 from=translated src=- shape=75f9c43f vocab=4aa349eb
-/
theorem from_finite_sixth_power_rows_with_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε C : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ C * D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (C * D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (C * D ^ (49 / 60 : ℝ)) ^ 2 =
      C ^ 2 * D ^ (49 / 30 : ℝ) := by
    rw [mul_pow]
    congr 1
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows_with_constant D ε
    (primes.card : ℝ) ‖A untwisted‖ C hD hε (norm_nonneg _) hC
    hcount (by simpa only [mul_assoc] using hextract)

end PowerExtraction

namespace ActualEisensteinCubic

end ActualEisensteinCubic

namespace PowerExtraction

/--
@isnad1 id=le.2h2v.s7.39ff01001699 from=translated src=- shape=408c4dc4 vocab=ad3e4bb6
-/
theorem dyadic_prime_error_bound (D N : ℕ) (hD : 1 ≤ D)
    (hN : (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤ (N : ℝ)) :
    ((64 * (D / N + 1) : ℕ) : ℝ) ≤
      192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 < (D : ℝ) ^ (11 / 60 : ℝ) :=
    Real.rpow_pos_of_pos hDpos _
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow :
      (D : ℝ) ^ (49 / 60 : ℝ) *
        (D : ℝ) ^ (11 / 60 : ℝ) = D := by
    rw [← Real.rpow_add hDpos]
    norm_num
  have hfrac : (D : ℝ) / N ≤
      2 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    apply (div_le_iff₀ hNpos).mpr
    calc
      (D : ℝ) =
          (D : ℝ) ^ (49 / 60 : ℝ) *
            (D : ℝ) ^ (11 / 60 : ℝ) := hpow.symm
      _ =
          (2 * (D : ℝ) ^ (49 / 60 : ℝ)) *
            ((D : ℝ) ^ (11 / 60 : ℝ) / 2) := by
              ring
      _ ≤ (2 * (D : ℝ) ^ (49 / 60 : ℝ)) * N :=
          mul_le_mul_of_nonneg_left hN (by positivity)
  have hcast : ((D / N : ℕ) : ℝ) ≤ (D : ℝ) / N :=
    Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (D : ℝ) ^ (49 / 60 : ℝ) :=
    Real.one_le_rpow hDreal (by norm_num)
  have hnatcast : ((64 * (D / N + 1) : ℕ) : ℝ) =
      64 * (((D / N : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hnatcast]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex
/--
@isnad1 id=and.1h2v.s6.1e3643ef4fe7 from=translated src=- shape=9628627b vocab=c85d5191
-/
theorem eisenstein_coord_norm_zero (a b : ℤ)
    (h : a*a-a*b+b*b = 0) : a = 0 ∧ b = 0 := by
  have hs : (a-b)^2 + a^2 + b^2 = 0 := by nlinarith [h]
  have ha : a^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg b]
  have hb : b^2 = 0 := by
    nlinarith [sq_nonneg (a-b), sq_nonneg a]
  constructor <;> nlinarith

/--
@isnad1 id=other.1h4v.s10.446b5666a1af from=translated src=- shape=d7960318 vocab=d943c93b
-/
theorem quadraticTraceModChar_coordinate (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  have hq : a*a-a*b+b*b ≠ 0 := by
    intro h
    obtain ⟨ha,hb⟩ := eisenstein_coord_norm_zero a b h
    subst a
    subst b
    exact hc (by simp [ActualEisensteinCoordinates.eval])
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval x y ^ 2) /
      (eisEmbedding (ActualEisensteinCoordinates.eval a b) * eisLam)) = _
  rw [map_pow, eisEmbedding_eval, eisEmbedding_eval]
  exact breveE_quadratic_coordinate a b x y hq

end ActualEisensteinCubic

namespace GaussianAbelPartition

/--
@isnad1 id=eq.1h4v.s7.9af26a44f8db from=translated src=- shape=7e362837 vocab=da81beeb
-/
theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

/--
@isnad1 id=eq.1h5v.s7.f3ded57cdf90 from=translated src=- shape=1d05316d vocab=2a365985
-/
theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic

/--
@isnad1 id=eq.2h2v.s12.469e25ebf064 from=translated src=- shape=2700fac7 vocab=42e4e46e
-/
theorem actual_quadratic_gaussian_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c}))
    (fun r => (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
      (r ^ 2)) W hsum

end GaussianAbelPartition

namespace ActualEisensteinCubic

end ActualEisensteinCubic

namespace GaussianFiberEquiv

open ActualEisensteinCubic

def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

private theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

private theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

/--
@isnad1 id=eq.2h4v.s11.edc0a3035674 from=translated src=- shape=83417365 vocab=55bbaf2a
-/
theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace RankTwoPoisson

open Real

/--
@isnad1 id=summable.0h1v.s6.fa50312be6e6 from=translated src=- shape=984bb0a6 vocab=e221580e
-/
theorem schwartz_int_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/--
@isnad1 id=summable.0h1v.s6.ed6848dc50cb from=translated src=- shape=ab3cb902 vocab=38189bca
-/
theorem schwartz_int_norm_summable (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) :=
  (schwartz_int_summable f).norm

/--
@isnad1 id=eq.0h1v.s8.5d041545f44f from=translated src=- shape=793477b1 vocab=30302ea8
-/
theorem schwartz_int_poisson (f : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, (𝓕 f) (n : ℝ) := by
  simpa [fourier_eval_zero] using
    SchwartzMap.tsum_eq_tsum_fourier f 0

/--
@isnad1 id=eq.0h2v.s9.fcce5b65d166 from=translated src=- shape=5d631823 vocab=56f3671a
-/
theorem tensor_poisson (f g : 𝓢(ℝ, ℂ)) :
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
      ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) := by
  calc
    (∑' z : ℤ × ℤ, f (z.1 : ℝ) * g (z.2 : ℝ)) =
        (∑' m : ℤ, f (m : ℝ)) * (∑' n : ℤ, g (n : ℝ)) :=
      (tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable f) (schwartz_int_norm_summable g)).symm
    _ = (∑' m : ℤ, (𝓕 f) (m : ℝ)) * (∑' n : ℤ, (𝓕 g) (n : ℝ)) :=
      congrArg₂ (· * ·) (schwartz_int_poisson f) (schwartz_int_poisson g)
    _ = ∑' z : ℤ × ℤ, (𝓕 f) (z.1 : ℝ) * (𝓕 g) (z.2 : ℝ) :=
      tsum_mul_tsum_of_summable_norm
        (schwartz_int_norm_summable (𝓕 f))
        (schwartz_int_norm_summable (𝓕 g))
  rfl

private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)

noncomputable def cg (a : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)

private theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha

private theorem cg_poisson {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cg a n) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg a⁻¹ n := by
  simpa only [cg, div_eq_mul_inv, neg_mul, mul_assoc] using
    Complex.tsum_exp_neg_mul_int_sq ha

/--
@isnad1 id=eq.4h2v.s8.e3e3de77733c from=translated src=- shape=14351431 vocab=7f35f0ce
-/
theorem diagonal_gaussian_poisson {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hai : 0 < (a⁻¹).re) (hbi : 0 < (b⁻¹).re) :
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
  calc
    (∑' z : ℤ × ℤ, cg a z.1 * cg b z.2) =
        (∑' m : ℤ, cg a m) * (∑' n : ℤ, cg b n) :=
      (tsum_mul_tsum_of_summable_norm (cg_summable ha).norm (cg_summable hb).norm).symm
    _ = ((1 / a ^ (1 / 2 : ℂ)) * ∑' m : ℤ, cg a⁻¹ m) *
        ((1 / b ^ (1 / 2 : ℂ)) * ∑' n : ℤ, cg b⁻¹ n) := by
      rw [cg_poisson ha, cg_poisson hb]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (1 / b ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, cg a⁻¹ z.1 * cg b⁻¹ z.2 := by
      rw [← tsum_mul_tsum_of_summable_norm (cg_summable hai).norm (cg_summable hbi).norm]
      ring

/--
@isnad1 id=summable.1h1v.s6.bfcfd3fda7b9 from=translated src=- shape=05d29572 vocab=fdde6e68
-/
theorem real_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have h := (cg_summable htc).norm
  simpa [cg, Complex.norm_exp, ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc] using h

noncomputable def eisQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 - (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def eisGauss (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp ((-Real.pi * t * eisQ z : ℝ) : ℂ)

/--
@isnad1 id=le.0h1v.s6.835b67d608a2 from=translated src=- shape=ad152aca vocab=ebd1cf43
-/
theorem eisQ_lower (z : ℤ × ℤ) :
    ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 2 ≤ eisQ z := by
  dsimp [eisQ]
  nlinarith [sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ))]

/--
@isnad1 id=summable.1h1v.s5.684fa677a2a4 from=translated src=- shape=997c4bc7 vocab=0f8cd412
-/
theorem eis_gauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (eisGauss t) := by
  have ht2 : 0 < t / 2 := by positivity
  have h1 := real_gauss_summable ht2
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 2) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 2) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq := eisQ_lower z
  have hpi : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hq hpi
  have hexp : -Real.pi * t * eisQ z ≤
      -Real.pi * (t / 2) * (z.1 : ℝ) ^ 2 +
      -Real.pi * (t / 2) * (z.2 : ℝ) ^ 2 := by
    nlinarith [hmul]
  simpa [eisGauss, Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

private noncomputable def phase (k n : ℤ) : ℂ :=
  Complex.exp (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I)

private noncomputable def g1 (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 * cg (((3 * t) / 4 : ℝ) : ℂ) z.2 * phase z.1 z.2

private theorem phase_norm (k n : ℤ) : ‖phase k n‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem g1_summable {t : ℝ} (ht : 0 < t) : Summable (g1 t) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := (cg_summable (a := ((t⁻¹ : ℝ) : ℂ)) (by simpa using htinv)).norm
  have h2 := (cg_summable (a := (((3 * t) / 4 : ℝ) : ℂ)) (by simpa using ht3)).norm
  have hmaj : Summable (fun z : ℤ × ℤ =>
      ‖cg ((t⁻¹ : ℝ) : ℂ) z.1‖ * ‖cg (((3 * t) / 4 : ℝ) : ℂ) z.2‖) :=
    h1.mul_of_nonneg h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hmaj.of_norm_bounded ?_
  intro z
  simp [g1,  phase_norm]

private theorem eisGauss_split (t : ℝ) (m n : ℤ) :
    eisGauss t (m, n) =
      Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (((t : ℂ) * (n : ℂ)) / 2) * (m : ℂ)) := by
  dsimp [eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem eis_exponent_identity {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    (-(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * ((t : ℂ) * (n : ℂ) / 2)) ^ 2) =
      (-(Real.pi : ℂ) * (((t⁻¹ : ℝ) : ℂ)) * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2) +
        (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem first_transform_term {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
      Complex.exp (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * (((t : ℂ) * (n : ℂ)) / 2)) ^ 2) =
      g1 t (k, n) := by
  have hn : ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) =
      -(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hn, ← Complex.exp_add, eis_exponent_identity ht k n]
  simp only [Complex.exp_add]
  dsimp [g1, cg, phase]
  push_cast
  ring_nf

private theorem first_poisson_slice {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (∑' m : ℤ, eisGauss t (m, n)) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  let C : ℂ := Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ)
  let B : ℂ := ((t : ℂ) * (n : ℂ)) / 2
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / (t : ℂ) * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact eisGauss_split t m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k := by
    exact Complex.tsum_exp_neg_quadratic htc B
  calc
    (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ht k n

private noncomputable def dualTerm (t : ℝ) (z : ℤ × ℤ) : ℂ :=
  cg ((t⁻¹ : ℝ) : ℂ) z.1 *
    Complex.exp (-(Real.pi : ℂ) / (((3 * t) / 4 : ℝ) : ℂ) *
      ((z.2 : ℂ) + (z.1 : ℂ) / 2) ^ 2)

private theorem second_transform_term (t : ℝ) (k n : ℤ) :
    cg ((((3 * t) / 4 : ℝ) : ℂ)) n * phase k n =
      Complex.exp (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * (-(Complex.I * (k : ℂ)) / 2) * (n : ℂ)) := by
  dsimp [cg, phase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem second_poisson_slice {t : ℝ} (ht : 0 < t) (k : ℤ) :
    (∑' n : ℤ, g1 t (k, n)) =
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualTerm t (k, l) := by
  have ht3 : 0 < 3 * t / 4 := by positivity
  have ht3c : 0 < (((3 * t) / 4 : ℝ) : ℂ).re := by simpa using ht3
  let A : ℂ := (((3 * t) / 4 : ℝ) : ℂ)
  let B : ℂ := -(Complex.I * (k : ℂ)) / 2
  let C : ℂ := cg ((t⁻¹ : ℝ) : ℂ) k
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    calc
      g1 t (k, n) = C * (cg A n * phase k n) := by
        dsimp [g1, C, A]
        ring
      _ = C * F n := by rw [second_transform_term t k n]
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic ht3c B
  have hterm (l : ℤ) : C * H l = dualTerm t (k,l) := by
    have hb : Complex.I * B = (k : ℂ) / 2 := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualTerm, C, A]
    rw [hb]
  calc
    (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualTerm t (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualTerm t (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

/--
@isnad1 id=eq.1h1v.s7.6bdf96a3201d from=translated src=- shape=3d9b4e87 vocab=83a8a2cb
-/
theorem eisenstein_gaussian_poisson_iterated {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
  have hE := eis_gauss_summable ht
  have hG := g1_summable ht
  have hEcomm :
      (∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => eisGauss t (m,n))) from hE).tsum_comm
  have hGcomm :
      (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, g1 t (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => g1 t (k,n))) from hG).tsum_comm
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) := hE.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n) := hEcomm.symm
    _ = ∑' n : ℤ, (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, g1 t (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ht n
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) := tsum_mul_left
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, g1 t (k,n)) := by
      rw [hGcomm]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualTerm t (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice ht k
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
      rw [tsum_mul_left]
      ring

private theorem dualTerm_eq_eisGauss {t : ℝ} (ht : 0 < t) (k l : ℤ) :
    dualTerm t (k,l) = eisGauss (4 / (3 * t)) (k,-l) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp [dualTerm, cg, eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring

private theorem dualTerm_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualTerm t) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have h := (e.summable_iff).2 (eis_gauss_summable htd)
  apply h.congr
  intro z
  change eisGauss (4 / (3 * t)) (z.1, -z.2) = dualTerm t z
  exact (dualTerm_eq_eisGauss ht z.1 z.2).symm

/--
@isnad1 id=eq.1h1v.s7.05af130be8b9 from=translated src=- shape=158fb63d vocab=75b3503a
-/
theorem eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hdual : (∑' z : ℤ × ℤ, dualTerm t z) =
      ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z := by
    calc
      (∑' z : ℤ × ℤ, dualTerm t z) =
          ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) (e z) := by
        apply tsum_congr
        intro z
        exact dualTerm_eq_eisGauss ht z.1 z.2
      _ = ∑' z : ℤ × ℤ, eisGauss (4 / (3 * t)) z :=
        Equiv.tsum_eq e _
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l)) :=
      eisenstein_gaussian_poisson_iterated ht
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          (∑' z : ℤ × ℤ, dualTerm t z) := by
      rw [(dualTerm_summable ht).tsum_prod]
    _ = _ := by rw [hdual]

end RankTwoPoisson

end

end OAI
