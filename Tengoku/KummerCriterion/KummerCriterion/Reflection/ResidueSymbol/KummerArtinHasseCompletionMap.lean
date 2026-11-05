module

public import Tengoku.Seed.NumberTheory.Padics.HeightOneSpectrum
import Tengoku.Seed.Topology.Algebra.Valued.WithZeroMulInt
public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ZetaPrime
public import Tengoku.Seed.RingTheory.Ideal.Int
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rational `p`-adic base place for the lambda-local correction

This file records the rational height-one prime `(p)` and proves that the
cyclotomic `lambda` prime lies over it. These are the concrete inputs
extending the rational map `ℚ → K` to the corresponding valuation completions.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The rational prime ideal `(p)` in `ℤ`.-/
def lambdaRationalPrimeIdeal : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

/-- The height-one spectrum point of `ℤ` attached to the rational prime `p`.-/
def lambdaRationalHeightOneSpectrum : IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := lambdaRationalPrimeIdeal p
  isPrime := (Int.ideal_span_isMaximal_of_prime p).isPrime
  ne_bot := by
    rw [lambdaRationalPrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero

/-- The cyclotomic `lambda` prime lies over the rational prime `(p)`.
@isnad1 id=liesover.0h2v.s6.ea7331ebc925 from=translated src=- shape=6fa64ffb vocab=1138ea5c
-/
theorem zetaPrime_liesOver_lambdaRationalPrimeIdeal :
    (zetaPrime p K).LiesOver (lambdaRationalPrimeIdeal p) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hζpow : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) (p ^ (0 + 1)) := by simp
  have h :
      (Ideal.span ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)})).LiesOver
        (Ideal.span ({(p : ℤ)})) :=
    IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one _ _ hζpow
  simpa [zetaPrime, lambdaRationalPrimeIdeal] using h

end KummerArtinHasse
end Furtwaengler
end KummerCriterion

/-!
# Valuation-completion model for the lambda-local Kummer--Artin--Hasse trace

The existing `LambdaLocalIntegerRing` is an adic completion of the localized
cyclotomic integer ring. It is the model already used by the principal-unit
filtration. For the `Q_p`-linear trace in the explicit local correction,
mathlib's available field/DVR API is instead attached to
`HeightOneSpectrum.adicCompletion`.

This file exposes the valuation-completion model attached to the same prime
`lambda = zetaPrime p K`. The final explicit Kummer--Artin--Hasse trace
source is routed through this valuation-completion model; the older
`LambdaLocalIntegerRing` stack is legacy infrastructure for the adic
principal-unit filtration, not the final trace API.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The height-one prime of `𝓞 K` corresponding to `lambda = zeta_p - 1`.-/
def lambdaHeightOneSpectrum : IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := zetaPrime p K
  isPrime := zetaPrime_isPrime p K
  ne_bot := zetaPrime_ne_bot p K

/-- The valuation completion of `K` at `lambda`.-/
abbrev LambdaValuedCompletion : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletion K

/-- The valuation-completion integer ring at `lambda`.-/
abbrev LambdaValuedIntegerRing : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletionIntegers K

instance lambdaValuedCompletion_field : Field (LambdaValuedCompletion p K) :=
  inferInstance

end KummerArtinHasse
end Furtwaengler
end KummerCriterion

/-!
# The rational `p`-adic map into the lambda completion

This file proves the valuation-comparison input needed to extend the rational
map `ℚ → K` to completions. The comparison is concrete: the cyclotomic
`lambda` prime lies over `(p)`, so the lambda valuation on `K`, restricted to
`ℚ`, is equivalent to the rational `p`-adic valuation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped NumberField TensorProduct Topology WithZero

namespace KummerCriterion
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The `Nat.Primes` object attached to the current rational prime `p`.-/
abbrev lambdaPadicPrime : Nat.Primes :=
  ⟨p, Fact.out⟩

/-- Integer membership in the cyclotomic `lambda` prime is exactly membership
in the rational prime `(p)`.
@isnad1 id=iff.0h3v.s7.365fcc1bb824 from=translated src=- shape=6d5dcad2 vocab=c0109539
-/
theorem intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal (n : ℤ) :
    algebraMap ℤ (𝓞 K) n ∈ zetaPrime p K ↔
      n ∈ lambdaRationalPrimeIdeal p := by
  have : (zetaPrime p K).LiesOver (lambdaRationalPrimeIdeal p) :=
    zetaPrime_liesOver_lambdaRationalPrimeIdeal (p := p) (K := K)
  simpa using
    (Ideal.mem_of_liesOver (A := ℤ) (B := 𝓞 K)
      (P := zetaPrime p K) (p := lambdaRationalPrimeIdeal p) n).symm

/-- The rational `p`-adic valuation detects exactly whether the denominator
is prime to `(p)`.
@isnad1 id=iff.0h2v.s7.9cc080d529eb from=translated src=- shape=6b0b34ed vocab=5447661b
-/
theorem lambdaRationalValuation_le_one_iff_den (x : ℚ) :
    (lambdaRationalHeightOneSpectrum p).valuation ℚ x ≤ 1 ↔
      (x.den : ℤ) ∉ lambdaRationalPrimeIdeal p := by
  simpa [lambdaRationalHeightOneSpectrum, lambdaRationalPrimeIdeal] using
    (Rat.valuation_le_one_iff_den
      (R := ℤ) (𝔭 := lambdaRationalHeightOneSpectrum p) (x := x))

/--
@isnad1 id=eq.0h1v.s5.9ad226013870 from=translated src=- shape=03ae60b0 vocab=f89159b8
-/
theorem lambdaRationalHeightOneSpectrum_eq_primesEquiv_symm :
    lambdaRationalHeightOneSpectrum p =
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm (lambdaPadicPrime p) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  change lambdaRationalPrimeIdeal p =
    (Ideal.span ({(p : ℤ)} : Set ℤ)).map
      (Rat.IsIntegralClosure.intEquiv ℤ).symm
  ext z
  simp [lambdaRationalPrimeIdeal, Rat.IsIntegralClosure.intEquiv,
    Ideal.mem_span_singleton]

/--
@isnad1 id=eq.0h1v.s5.c5cc2cfa8518 from=translated src=- shape=b11f63ee vocab=9e267596
-/
theorem primesEquiv_lambdaRationalHeightOneSpectrum :
    Rat.HeightOneSpectrum.primesEquiv
        (R := ℤ) (lambdaRationalHeightOneSpectrum p) =
      lambdaPadicPrime p := by
  rw [lambdaRationalHeightOneSpectrum_eq_primesEquiv_symm]
  exact Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply (lambdaPadicPrime p)

/-- The lambda valuation on `K`, restricted to rational elements, detects the
same denominators as the rational `p`-adic valuation.
@isnad1 id=iff.0h3v.s7.728e26ee8c95 from=translated src=- shape=09ff4ed1 vocab=6782472a
-/
theorem lambdaValuation_algebraMap_rat_le_one_iff_den (x : ℚ) :
    (lambdaHeightOneSpectrum p K).valuation K (algebraMap ℚ K x) ≤ 1 ↔
      (x.den : ℤ) ∉ lambdaRationalPrimeIdeal p := by
  classical
  have hden_ne : (algebraMap ℤ (𝓞 K) (x.den : ℤ)) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast x.den_nz)
  have hcop :
      algebraMap ℤ (𝓞 K) (x.den : ℤ) ∈ zetaPrime p K →
        algebraMap ℤ (𝓞 K) x.num ∉ zetaPrime p K := by
    intro hden hnum
    have hdenZ :
        (x.den : ℤ) ∈ lambdaRationalPrimeIdeal p :=
      (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
        (p := p) (K := K) (x.den : ℤ)).mp hden
    have hnumZ :
        x.num ∈ lambdaRationalPrimeIdeal p :=
      (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
        (p := p) (K := K) x.num).mp hnum
    have : (lambdaRationalPrimeIdeal p).IsPrime := by
      simpa [lambdaRationalHeightOneSpectrum] using (lambdaRationalHeightOneSpectrum p).isPrime
    exact (Ideal.IsPrime.notMem_of_isCoprime_of_mem
      (by simpa using! x.isCoprime_num_den.symm.intCast) hdenZ) hnumZ
  have hx :
      algebraMap ℚ K x =
        (algebraMap ℤ (𝓞 K) x.num : K) /
          (algebraMap ℤ (𝓞 K) (x.den : ℤ) : K) := by
    conv_lhs => rw [← Rat.num_div_den x]
    norm_num
  rw [hx]
  simpa [lambdaHeightOneSpectrum] using
    ((lambdaHeightOneSpectrum p K).valuation_div_le_one_iff
      (K := K) (a := algebraMap ℤ (𝓞 K) x.num)
      (b := algebraMap ℤ (𝓞 K) (x.den : ℤ)) hden_ne hcop)
      |>.trans
        (not_congr
          (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
            (p := p) (K := K) (x.den : ℤ)))

/-- The lambda valuation on `K`, pulled back to `ℚ`, is equivalent to the
rational `p`-adic valuation.
@isnad1 id=isequiv.0h2v.s7.a0f67d4def0b from=translated src=- shape=820dd3b7 vocab=dd92fa66
-/
theorem lambdaValuation_comap_rat_isEquiv :
    ((lambdaRationalHeightOneSpectrum p).valuation ℚ).IsEquiv
      (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply,
    lambdaRationalValuation_le_one_iff_den (p := p) x,
    lambdaValuation_algebraMap_rat_le_one_iff_den (p := p) (K := K) x]

/-- The exact-comap valued map from rational elements to the lambda-valued
cyclotomic field.-/
def rationalToLambdaComapWithValRingHom :
    WithVal (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K)) →+*
      WithVal ((lambdaHeightOneSpectrum p K).valuation K) :=
  (WithVal.equiv ((lambdaHeightOneSpectrum p K).valuation K)).symm.toRingHom.comp
    ((algebraMap ℚ K).comp
      (WithVal.equiv
        (((lambdaHeightOneSpectrum p K).valuation K).comap (algebraMap ℚ K))).toRingHom)

/-- The rational `p`-adic valued map into the lambda-valued cyclotomic field.-/
def rationalToLambdaWithValRingHom :
    WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ) →+*
      WithVal ((lambdaHeightOneSpectrum p K).valuation K) :=
  (rationalToLambdaComapWithValRingHom (p := p) (K := K)).comp
    (lambdaValuation_comap_rat_isEquiv (p := p) (K := K)).orderRingIso.toRingHom

/-- Continuity of the rational `p`-adic valued map into the lambda-valued
cyclotomic field. This is the theorem consumed by
`UniformSpace.Completion.mapRingHom`.
@isnad1 id=continuo.0h2v.s10.1ad855d939f0 from=translated src=- shape=c66b5e6a vocab=32104be6
-/
theorem continuous_rationalToLambdaWithValRingHom :
    Continuous (rationalToLambdaWithValRingHom (p := p) (K := K)) := by
  let vQ := (lambdaRationalHeightOneSpectrum p).valuation ℚ
  let vK := (lambdaHeightOneSpectrum p K).valuation K
  let targetP : WithVal vK :=
    (WithVal.equiv vK).symm (algebraMap ℚ K (p : ℚ))
  have hp_mem_rat : (p : ℤ) ∈ lambdaRationalPrimeIdeal p := by
    simp [lambdaRationalPrimeIdeal]
  have hp_mem_zeta : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ zetaPrime p K :=
    (intCast_mem_zetaPrime_iff_mem_lambdaRationalPrimeIdeal
      (p := p) (K := K) (p : ℤ)).mpr hp_mem_rat
  have hp_lt : Valued.v targetP < 1 := by
    have h :
        vK (algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) (p : ℤ))) < 1 :=
      ((lambdaHeightOneSpectrum p K).valuation_lt_one_iff_mem
        (K := K) (algebraMap ℤ (𝓞 K) (p : ℤ))).mpr hp_mem_zeta
    simpa [targetP, vK] using! h
  have hp_tendsto : Tendsto (fun n : ℕ => targetP ^ n) atTop (𝓝 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hp_lt
  refine (uniformContinuous_of_continuousAt_zero
    (rationalToLambdaWithValRingHom (p := p) (K := K)).toAddMonoidHom ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  have hγ_mem :
      {z : WithVal vK | Valued.v.restrict z < γ.1} ∈ 𝓝 (0 : WithVal vK) :=
    (Valued.hasBasis_nhds_zero (WithVal vK) ℤᵐ⁰).mem_of_mem (i := γ) trivial
  obtain ⟨n, hn⟩ := (eventually_atTop.1 (hp_tendsto hγ_mem))
  let sourceP : WithVal vQ :=
    (WithVal.equiv vQ).symm ((p : ℚ) ^ n)
  have hsourceP_ne : Valued.v.restrict sourceP ≠ 0 :=
    ne_of_gt <| by
      rw [Valuation.restrict_pos_iff]
      have hpq_ne : ((p : ℚ) ^ n) ≠ 0 :=
        pow_ne_zero n (by exact_mod_cast (Nat.Prime.ne_zero Fact.out))
      have hsourceP_nz : sourceP ≠ 0 := by
        intro hzero
        apply hpq_ne
        have := congrArg (WithVal.equiv vQ) hzero
        simpa [sourceP] using this
      exact zero_lt_iff.mpr <|
        (Valuation.ne_zero_iff
          (Valued.v : Valuation (WithVal vQ) ℤᵐ⁰)).mpr hsourceP_nz
  refine ⟨Units.mk0 (Valued.v.restrict sourceP) hsourceP_ne, ?_⟩
  intro x hx
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding]
  have hx_val : Valued.v x < Valued.v sourceP := by
    rwa [Valuation.restrict_lt_iff] at hx
  have hx_rat :
      vQ ((WithVal.equiv vQ) x) < vQ ((p : ℚ) ^ n) := by
    simpa [sourceP, vQ] using! hx_val
  have hx_comap :
      (vK.comap (algebraMap ℚ K)) ((WithVal.equiv vQ) x) <
        (vK.comap (algebraMap ℚ K)) ((p : ℚ) ^ n) :=
    (lambdaValuation_comap_rat_isEquiv (p := p) (K := K)).lt_iff_lt.mp hx_rat
  have hx_target :
      Valued.v (rationalToLambdaWithValRingHom (p := p) (K := K) x) <
        Valued.v (targetP ^ n) := by
    simpa [rationalToLambdaWithValRingHom, rationalToLambdaComapWithValRingHom,
      targetP, sourceP, vQ, vK, Valuation.comap_apply, map_pow] using! hx_comap
  exact hx_target.trans <| by
    have hn' : Valued.v.restrict (targetP ^ n) < γ.1 := hn n le_rfl
    rwa [Valuation.restrict_lt_iff_lt_embedding] at hn'

/-- The completion-level map from the rational `p`-adic completion to the
lambda-adic completion of `K`.-/
def rationalToLambdaCompletionRingHom :
    (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ →+*
      LambdaValuedCompletion p K :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K
      (lambdaHeightOneSpectrum p K)).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (rationalToLambdaWithValRingHom (p := p) (K := K))
      (continuous_rationalToLambdaWithValRingHom (p := p) (K := K))).comp <|
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv ℚ
          (lambdaRationalHeightOneSpectrum p)).toRingHom

/--
@isnad1 id=eq.0h3v.s10.b236c22f7a1b from=translated src=- shape=e6008ca1 vocab=8c97e1e1
-/
@[simp]
theorem rationalToLambdaCompletionRingHom_coe
    (x : WithVal ((lambdaRationalHeightOneSpectrum p).valuation ℚ)) :
    rationalToLambdaCompletionRingHom (p := p) (K := K) x =
      (rationalToLambdaWithValRingHom (p := p) (K := K) x :
        LambdaValuedCompletion p K) :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext K
    (lambdaHeightOneSpectrum p K)
    (UniformSpace.Completion.mapRingHom_coe
      (continuous_rationalToLambdaWithValRingHom (p := p) (K := K)) x)

/-- The rational-completion algebra structure on the lambda completion before
identifying the rational completion with mathlib's `ℚ_[p]`.-/
@[reducible]
def rationalCompletionToLambdaAlgebra :
    Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K) :=
  (rationalToLambdaCompletionRingHom (p := p) (K := K)).toAlgebra

/--
@isnad1 id=continuo.0h2v.s9.22be74543459 from=translated src=- shape=27fbf0ec vocab=cea68beb
-/
theorem continuous_algebraMap_rationalCompletionToLambdaAlgebra :
    letI : Algebra ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
        (LambdaValuedCompletion p K) :=
      rationalCompletionToLambdaAlgebra (p := p) (K := K)
    Continuous (algebraMap ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (LambdaValuedCompletion p K)) := by
  change Continuous (rationalToLambdaCompletionRingHom (p := p) (K := K))
  exact
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv K
      (lambdaHeightOneSpectrum p K)).symm.continuous.comp <|
      (UniformSpace.Completion.continuous_map
        (f := rationalToLambdaWithValRingHom (p := p) (K := K))).comp <|
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ
          (lambdaRationalHeightOneSpectrum p)).continuous

end KummerArtinHasse
end Furtwaengler
end KummerCriterion
