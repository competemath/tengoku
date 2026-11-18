import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly

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

namespace TraceLambdaPhase

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate

/--
@isnad1 id=eq.0h0v.s5.32d6d0f844c8 from=translated src=- shape=8e19147c vocab=dd7612cd
-/
theorem eisLam_sq : eisLam ^ 2 = (-3 : ℂ) := by
  change (1 + 2 * omega3) ^ 2 = -3
  linear_combination 4 * omega3_sq

/--
@isnad1 id=eq.0h0v.s5.649d7057641c from=translated src=- shape=3ecff34a vocab=b0e2c665
-/
theorem exp_minus_four_pi_div_three :
    Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) = omega3 := by
  have hshift : Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I / 3) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hshift]
  have harg : ((2 : ℂ) * Real.pi * Complex.I / 3) =
      (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega3
  push_cast
  ring

/--
@isnad1 id=eq.0h0v.s5.c7fb54391c24 from=translated src=- shape=31239df7 vocab=71528127
-/
theorem breveE_traceLambda_square :
    ShortDraftTrace.breveE (1 / (eisLam * eisLam)) = omega3 := by
  have harg : (1 : ℂ) / (eisLam * eisLam) = -(1 : ℂ) / 3 := by
    rw [← pow_two, eisLam_sq]
    ring
  rw [harg]
  change Complex.exp (2 * Real.pi * Complex.I *
    ((-(1 : ℂ) / 3) + conj (-(1 : ℂ) / 3))) = omega3
  have hconj : conj (-(1 : ℂ) / 3) = -(1 : ℂ) / 3 := by
    simp only [map_div₀, map_neg, map_one, map_ofNat]
  rw [hconj]
  convert exp_minus_four_pi_div_three using 1 ; ring_nf

end TraceLambdaPhase

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

/--
@isnad1 id=ne.0h0v.s4.4343a51fb396 from=translated src=- shape=ffdda526 vocab=81256ff3
-/
theorem traceLambda_ne_zero : traceLambda ≠ 0 := by
  intro h
  have hh := congrArg eisEmbedding h
  rw [eisEmbedding_traceLambda, map_zero] at hh
  exact eisLam_ne_zero hh

private theorem traceLambda_span_eq_lambda :
    Ideal.span {traceLambda} = Ideal.span {lambda} := by
  rw [traceLambda_eq_unit_mul_lambda]
  exact Ideal.span_singleton_mul_left_unit neg_omega_isUnit lambda

/--
@isnad1 id=eq.0h0v.s5.f3487bfa8613 from=translated src=- shape=9442d71c vocab=5285cf35
-/
theorem traceLambda_quotient_card :
    Nat.card (O ⧸ Ideal.span {traceLambda}) = 3 := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_card

noncomputable def quadraticGammaTraceLambda : ℂ := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

/--
@isnad1 id=eq.0h0v.s2.88374621e250 from=translated src=- shape=54c8eceb vocab=d0419958
-/
theorem quadraticGammaTraceLambda_eq_I : quadraticGammaTraceLambda = Complex.I := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    simpa only [Nat.card_eq_fintype_card] using traceLambda_quotient_card
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3 := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3
    rw [map_one, show eisEmbedding c = eisLam from eisEmbedding_traceLambda]
    exact breveE_traceLambda_square
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) = 1 + 2 * omega3 := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = eisLam from eisEmbedding_traceLambda, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = Complex.I
  rw [hsum, hnorm]
  change eisLam / ((Real.sqrt 3 : ℝ) : ℂ) = Complex.I
  rw [hLam]
  field_simp

end ActualEisensteinCubic

namespace PoissonFirstLocal
open scoped Classical

def quotientUnitMask {R : Type*} [CommRing R] (z : R) : ℂ :=
  if IsUnit z then 1 else 0

private theorem quotientUnitMask_mul {R : Type*} [CommRing R]
    (a b : R) :
    quotientUnitMask (a * b) =
      quotientUnitMask a * quotientUnitMask b := by
  classical
  by_cases ha : IsUnit a <;> by_cases hb : IsUnit b <;>
    simp [quotientUnitMask, (Commute.all a b).isUnit_mul_iff, ha, hb]

def oldFactorRing {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  let q := χ z
  quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂

def newFactorRing {R : Type*} [CommRing R]
    (parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ z) ^ 4 else quotientUnitMask z

/--
@isnad1 id=eq.1h7v.s7.9908a4da30ef from=translated src=- shape=c65a3c9f vocab=fec8edd1
-/
theorem first_local_identity_ring {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool)
    (z : R) (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    oldFactorRing side parityBit ε₁ ε₂ z χ =
      newFactorRing parityBit ε₁ ε₂ z χ := by
  let q := χ z
  by_cases hu : IsUnit z
  · have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hu]
    have hmask : quotientUnitMask z = 1 := by
      simp [quotientUnitMask, hu]
    change quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else quotientUnitMask z)
    rw [hmask, one_mul, ← pow_add, ← pow_add]
    cases side
    · change q ^ (totalExp₁ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).1]
      split_ifs <;> simp
    · change q ^ (totalExp₂ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).2]
      split_ifs <;> simp
  · have hz : q = 0 := MulChar.map_nonunit χ hu
    simp [oldFactorRing, newFactorRing, quotientUnitMask, hu]

/--
@isnad1 id=eq.1h7v.s8.bc7ad965c47d from=translated src=- shape=bdb7ffd8 vocab=d36578b7
-/
theorem first_prime_product_identity_ring
    {R : Type*} [CommRing R]
    (side : Bool) (P : Finset R)
    (parityBit ε₁ ε₂ : R → Bool)
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      (χ (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      quotientUnitMask
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  classical
  calc
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      ∏ z ∈ P, newFactorRing (parityBit z) (ε₁ z) (ε₂ z) z χ := by
        apply Finset.prod_congr rfl
        intro z hz
        exact first_local_identity_ring side (parityBit z) (ε₁ z) (ε₂ z) z χ hχ
    _ = (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z),
          (χ z) ^ 4) *
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z),
          quotientUnitMask z) := by
        simp only [newFactorRing]
        exact Finset.prod_ite _ _
    _ = _ := by
      have hchar (S : Finset R) :
          (∏ z ∈ S, (χ z) ^ 4) = (χ (∏ z ∈ S, z)) ^ 4 := by
        induction S using Finset.induction_on with
        | empty => simp
        | @insert z S hz ih => simp [hz, ih, map_mul, mul_pow]
      have hmask (S : Finset R) :
          (∏ z ∈ S, quotientUnitMask z) =
            quotientUnitMask (∏ z ∈ S, z) := by
        induction S using Finset.induction_on with
        | empty => simp [quotientUnitMask]
        | @insert z S hz ih =>
            simp [hz, ih, quotientUnitMask_mul]
      rw [hchar, hmask]

end PoissonFirstLocal

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

noncomputable def quadraticGammaNegTraceLambda : ℂ := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

/--
@isnad1 id=eq.0h0v.s2.386e99f3e968 from=translated src=- shape=dfaa3aa7 vocab=e27b65ce
-/
theorem quadraticGammaNegTraceLambda_eq_neg_I :
    quadraticGammaNegTraceLambda = -Complex.I := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hspan : Ideal.span {c} = Ideal.span {traceLambda} := by
    change Ideal.span {-traceLambda} = Ideal.span {traceLambda}
    rw [show -traceLambda = (-1 : O) * traceLambda by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_neg_one traceLambda
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    have hcardNat : Nat.card (O ⧸ Ideal.span {c}) = 3 := by
      rw [hspan]
      exact traceLambda_quotient_card
    simpa only [Nat.card_eq_fintype_card] using hcardNat
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3⁻¹ := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3⁻¹
    rw [map_one, show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda]]
    have harg : (1 : ℂ) / (-eisLam * eisLam) =
        -((1 : ℂ) / (eisLam * eisLam)) := by ring
    rw [harg, ShortDraftTrace.breveE.map_neg_eq_inv,
      breveE_traceLambda_square]
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) =
      1 + 2 * omega3⁻¹ := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3⁻¹
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hωcube : omega3 ^ 3 = 1 := by
    linear_combination (omega3 - 1) * omega3_sq
  have hωinv : omega3⁻¹ = omega3 ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hωcube
  have hsumval : 1 + 2 * omega3⁻¹ = -eisLam := by
    rw [hωinv]
    dsimp [eisLam]
    linear_combination 2 * omega3_sq
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda], norm_neg, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaNegTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = -Complex.I
  rw [hsum, hsumval, hnorm, hLam]
  field_simp

end

noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)

/--
@isnad1 id=eq.1h4v.s8.7937a81f62d4 from=translated src=- shape=7c74acc8 vocab=b0a2414d
-/
theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [ite_eq_left ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [ite_eq_right hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

namespace AnalyticBridge

end AnalyticBridge

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

private def cuspMatrix (a b c d : R) : Matrix (Fin 2) (Fin 2) R := !![a,b;c,d]
private def unramifiedH (u : R) : Matrix (Fin 2) (Fin 2) R := U u * E
private def unramifiedHInv (u : R) : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,u]

/--
@isnad1 id=eq.0h5v.s8.ee684a1ccdd9 from=translated src=- shape=b4709514 vocab=173d70d7
-/
theorem A3_principal_matrix (a b c d : R) :
    cuspMatrix a b c d * (1 : Matrix (Fin 2) (Fin 2) R) =
      !![a,b;c,d] := by
  simp [cuspMatrix]

/--
@isnad1 id=eq.0h2v.s7.b9329775825e from=translated src=- shape=4f7f9a89 vocab=13c112db
-/
theorem A3_ramified_inverse (u : R) :
    L u * L (-u) = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

/--
@isnad1 id=eq.0h2v.s7.c98567568484 from=translated src=- shape=033b0286 vocab=13c112db
-/
theorem A3_ramified_inverse_left (u : R) :
    L (-u) * L u = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

/--
@isnad1 id=eq.0h6v.s8.b074c0d6de66 from=translated src=- shape=f1864eed vocab=a1fe4901
-/
theorem A3_ramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * L (-u) =
      !![a - u * b,b;c - u * d,d] := by
  simp [cuspMatrix, L, mul_comm, sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s8.6a8e13721000 from=translated src=- shape=a3761291 vocab=7226f7da
-/
theorem A3_unramified_H (u : R) :
    unramifiedH u = !![u,-1;1,0] := by
  simp [unramifiedH, U, E]

/--
@isnad1 id=eq.0h2v.s7.b1552a37c234 from=translated src=- shape=10ea7249 vocab=5838b099
-/
theorem A3_unramified_inverse_right (u : R) :
    unramifiedH u * unramifiedHInv u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

/--
@isnad1 id=eq.0h2v.s7.aeb4339ca2b3 from=translated src=- shape=10ea7249 vocab=5838b099
-/
theorem A3_unramified_inverse_left (u : R) :
    unramifiedHInv u * unramifiedH u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

/--
@isnad1 id=eq.0h6v.s8.6284eafb220c from=translated src=- shape=13d6b6b3 vocab=44fb2316
-/
theorem A3_unramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * unramifiedHInv u =
      !![-b,a + u * b;-d,c + u * d] := by
  simp [cuspMatrix, unramifiedHInv, mul_comm]

/--
@isnad1 id=eq.1h6v.s7.dfa39f099524 from=translated src=- shape=378faa7e vocab=54617df9
-/
theorem A3_ramified_det_relation (a b c d u : R)
    (hdet : a * d - b * c = 1) :
    a * (c - u * d) - c * (a - u * b) = -u := by
  calc
    a * (c - u * d) - c * (a - u * b) =
        -u * (a * d - b * c) := by ring
    _ = -u := by rw [hdet]; ring

/--
@isnad1 id=eq.1h6v.s7.86ee4cf748dc from=translated src=- shape=e1aebe20 vocab=26b25aee
-/
theorem A3_ramified_reciprocity_congr (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    (a - u * b) * cprime = 1 + a * (cprime - d) := by
  calc
    (a - u * b) * cprime =
        a * cprime + (a * d - b * (u * cprime)) - a * d := by ring
    _ = 1 + a * (cprime - d) := by rw [hdet]; ring

/--
@isnad1 id=eq.1h5v.s7.fef51f9048c9 from=translated src=- shape=019068c4 vocab=54617df9
-/
theorem A3_unramified_det_relation (a b c d : R)
    (hdet : a * d - b * c = 1) :
    (-b) * c = 1 - a * d := by linear_combination hdet

/--
@isnad1 id=eq.1h5v.s7.ce10cfc8b264 from=translated src=- shape=f07f893e vocab=26b25aee
-/
theorem A3_unramified_inverse_congr (a b c d : R)
    (hdet : a * d - b * c = 1) :
    a * d = 1 + b * c := by linear_combination hdet

end ShortDraftCusp

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

/--
@isnad1 id=eq.0h2v.s6.44bfe2531eec from=translated src=- shape=aae66b34 vocab=16107704
-/
theorem breveE_quarter_trace (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2

/--
@isnad1 id=eq.0h2v.s6.5ac535453f6b from=translated src=- shape=02e204b5 vocab=7245c224
-/
theorem breveGaussianFourTerms_formula (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]

end ActualEisensteinCubic

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
