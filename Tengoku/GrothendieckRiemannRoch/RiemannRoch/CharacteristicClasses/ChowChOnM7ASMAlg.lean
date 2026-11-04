/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.ChowCharacteristicSeries
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.PowerSeries.Substitution
import Tengoku.Seed.RingTheory.PowerSeries.Exp
import Tengoku.Seed.RingTheory.Adjoin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route M7-ASM, part 1: the algebra of Newton / Todd operators

Pure algebra (no geometry).  `psumOp`, `chOfChern`, `tdOfChern` of
`ChowCharacteristicSeries` are the Newton power sums, the Chern character and the Todd operator
attached to a *sequence of Chern operators* `c : ℕ → Module.End ℚ M`.  Here we prove the formal
properties the geometric part needs:

* generic restatements `psumG`, `chG`, `tdG` over any `ℚ`-algebra `R` (equal to the originals
  by `rfl` for `R = Module.End ℚ M`);
* compatibility with algebra homomorphisms (`psumG_map`, `chG_map`, `tdG_map`);
* **additivity / multiplicativity** for a convolution `c_B = c_A * c_D` of *pairwise commuting*
  operators: `psumG_conv_of_commute`, `chG_conv_of_commute`, `tdG_conv_of_commute`;
* closure under a graded family of submodules (`psumG_mem` ...), which gives both degree
  bookkeeping (`c_n` lowers the dimension by `n`) and "lies in a subalgebra";
* compatibility with a linear map intertwining the Chern operators (flat pullback).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
universe u
namespace AlgebraicGeometry.Chow.M7.M7ASM

section Defs

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- Newton power sums attached to the sequence `c` (generic over a `ℚ`-algebra).-/
def psumG (c : ℕ → R) : ℕ → R
  | 0 => 0
  | m + 1 => ((-1 : ℚ) ^ m) • PowerSeries.coeff m
      (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1)) *
        PowerSeries.invOfUnit (PowerSeries.mk c) 1)

/-- Chern character from a Chern sequence, rank `r`.-/
def chG (r : ℕ) (c : ℕ → R) : ℕ → R
  | 0 => (r : ℚ) • 1
  | m + 1 => (1 / ((m + 1).factorial : ℚ)) • psumG c (m + 1)

/-- Todd operator from a Chern sequence.-/
def tdG (c : ℕ → R) (m : ℕ) : R :=
  ∑ j ∈ Finset.range (m + 1), (1 / (j.factorial : ℚ)) •
    PowerSeries.coeff m ((PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c n) ^ j)

end Defs

section EndCompat

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/--
@isnad1 id=eq.0h2v.s6.738952990fad from=translated src=- shape=7f31e541 vocab=0c027743
-/
theorem psumOp_eq_psumG (c : ℕ → Module.End ℚ M) : psumOp c = psumG c := by
  funext m; cases m <;> rfl

/--
@isnad1 id=eq.0h3v.s6.c620b24e2709 from=translated src=- shape=b1670995 vocab=1517d977
-/
theorem chOfChern_eq_chG (r : ℕ) (c : ℕ → Module.End ℚ M) : chOfChern r c = chG r c := by
  funext m; cases m <;> rfl

/--
@isnad1 id=eq.0h2v.s6.974c24464090 from=translated src=- shape=7f31e541 vocab=d43c54a7
-/
theorem tdOfChern_eq_tdG (c : ℕ → Module.End ℚ M) : tdOfChern c = tdG c := by
  funext m; rfl

end EndCompat

/-! ### Algebra homomorphisms -/
section Map

variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

/--
@isnad1 id=eq.1h4v.s8.ea8b308b5866 from=translated src=- shape=7615d045 vocab=fa0f0b7f
-/
theorem map_invOfUnit (φ : A →+* B) (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.map φ (PowerSeries.invOfUnit f 1) =
      PowerSeries.invOfUnit (PowerSeries.map φ f) 1 := by
  have hf' : PowerSeries.constantCoeff f = ((1 : Aˣ) : A) := by simpa using hf
  have h1 : PowerSeries.invOfUnit f 1 * f = 1 := PowerSeries.invOfUnit_mul f 1 hf'
  have hmf : PowerSeries.constantCoeff (PowerSeries.map φ f) = ((1 : Bˣ) : B) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    simp
  have h2 := PowerSeries.mul_invOfUnit (PowerSeries.map φ f) 1 hmf
  calc PowerSeries.map φ (PowerSeries.invOfUnit f 1)
      = PowerSeries.map φ (PowerSeries.invOfUnit f 1) *
          (PowerSeries.map φ f * PowerSeries.invOfUnit (PowerSeries.map φ f) 1) := by
        rw [h2, mul_one]
    _ = (PowerSeries.map φ (PowerSeries.invOfUnit f 1) * PowerSeries.map φ f) *
          PowerSeries.invOfUnit (PowerSeries.map φ f) 1 := by rw [mul_assoc]
    _ = PowerSeries.invOfUnit (PowerSeries.map φ f) 1 := by
        rw [← map_mul, h1, map_one, one_mul]

/--
@isnad1 id=eq.1h5v.s7.5d589ef96d7d from=translated src=- shape=5688e016 vocab=e8527968
-/
theorem psumG_map (φ : A →ₐ[ℚ] B) (c : ℕ → A) (hc : c 0 = 1) (n : ℕ) :
    φ (psumG c n) = psumG (fun i ↦ φ (c i)) n := by
  cases n with
  | zero => simp [psumG]
  | succ m =>
    have hc0 : PowerSeries.constantCoeff (PowerSeries.mk c) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hc]
    have hmk : PowerSeries.map (φ : A →+* B) (PowerSeries.mk c) =
        PowerSeries.mk (fun i ↦ φ (c i)) := by
      ext i; simp
    have hdk : PowerSeries.map (φ : A →+* B)
        (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1))) =
        PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • φ (c (n + 1))) := by
      ext i; simp
    have hinv := map_invOfUnit (φ : A →+* B) (PowerSeries.mk c) hc0
    rw [hmk] at hinv
    simp only [psumG, map_smul]
    congr 1
    have := congrArg (PowerSeries.coeff m)
      (map_mul (PowerSeries.map (φ : A →+* B))
        (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1)))
        (PowerSeries.invOfUnit (PowerSeries.mk c) 1))
    rw [PowerSeries.coeff_map, hdk, hinv] at this
    exact this

/--
@isnad1 id=eq.1h6v.s7.9a3798c70c23 from=translated src=- shape=c6023056 vocab=4f57bb1f
-/
theorem chG_map (φ : A →ₐ[ℚ] B) (r : ℕ) (c : ℕ → A) (hc : c 0 = 1) (n : ℕ) :
    φ (chG r c n) = chG r (fun i ↦ φ (c i)) n := by
  cases n with
  | zero => simp [chG]
  | succ m => simp only [chG, map_smul, psumG_map φ c hc]

/--
@isnad1 id=eq.1h5v.s7.49eff0dc0a94 from=translated src=- shape=5688e016 vocab=a063edb8
-/
theorem tdG_map (φ : A →ₐ[ℚ] B) (c : ℕ → A) (hc : c 0 = 1) (m : ℕ) :
    φ (tdG c m) = tdG (fun i ↦ φ (c i)) m := by
  have hser : PowerSeries.map (φ : A →+* B) (PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c n) =
      PowerSeries.mk fun n ↦ toddLogCoeff n • psumG (fun i ↦ φ (c i)) n := by
    ext i; simp [psumG_map φ c hc]
  unfold tdG
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul]
  congr 1
  rw [← hser, ← map_pow, PowerSeries.coeff_map]
  rfl

end Map

/-! ### The commutative case -/
section Comm

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/--
@isnad1 id=eq.0h2v.s7.2020f1e793ab from=translated src=- shape=2010b296 vocab=cce7d770
-/
theorem natCast_succ_mul_inv (n : ℕ) :
    ((n : K) + 1) * algebraMap ℚ K (1 / ((n : ℚ) + 1)) = 1 := by
  have h : ((n : ℚ) + 1) * (1 / ((n : ℚ) + 1)) = 1 := by field_simp
  have h2 := congrArg (algebraMap ℚ K) h
  rw [map_mul, map_add, map_natCast, map_one] at h2
  exact h2

/--
@isnad1 id=eq.0h2v.s7.46e7f39887c6 from=translated src=- shape=8ee4d90b vocab=78fc0acf
-/
theorem mk_succ_smul_eq_derivative (c : ℕ → K) :
    PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1)) =
      PowerSeries.derivative K (PowerSeries.mk c) := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_derivative, PowerSeries.coeff_mk,
    Algebra.smul_def, map_natCast]
  push_cast
  ring

/--
@isnad1 id=eq.0h3v.s8.5c3128e834ae from=translated src=- shape=2cf07b8f vocab=e4675537
-/
theorem psumG_succ_comm (c : ℕ → K) (m : ℕ) :
    psumG c (m + 1) = ((-1 : ℚ) ^ m) • PowerSeries.coeff m
      (PowerSeries.derivative K (PowerSeries.mk c) *
        PowerSeries.invOfUnit (PowerSeries.mk c) 1) := by
  rw [psumG, mk_succ_smul_eq_derivative]

/--
@isnad1 id=eq.2h3v.s8.c6e6be320018 from=translated src=- shape=84f967f5 vocab=22623214
-/
theorem invOfUnit_mul_series (f g : PowerSeries K) (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.invOfUnit (f * g) 1 =
      PowerSeries.invOfUnit f 1 * PowerSeries.invOfUnit g 1 := by
  have hfg : PowerSeries.constantCoeff (f * g) = ((1 : Kˣ) : K) := by simp [hf, hg]
  have hf' : PowerSeries.constantCoeff f = ((1 : Kˣ) : K) := by simpa using hf
  have hg' : PowerSeries.constantCoeff g = ((1 : Kˣ) : K) := by simpa using hg
  have h1 := PowerSeries.mul_invOfUnit (f * g) 1 hfg
  have h2 := PowerSeries.mul_invOfUnit f 1 hf'
  have h3 := PowerSeries.mul_invOfUnit g 1 hg'
  calc PowerSeries.invOfUnit (f * g) 1
      = PowerSeries.invOfUnit (f * g) 1 *
          ((f * g) * (PowerSeries.invOfUnit f 1 * PowerSeries.invOfUnit g 1)) := by
        have : (f * g) * (PowerSeries.invOfUnit f 1 * PowerSeries.invOfUnit g 1) = 1 := by
          calc (f * g) * (PowerSeries.invOfUnit f 1 * PowerSeries.invOfUnit g 1)
              = (f * PowerSeries.invOfUnit f 1) * (g * PowerSeries.invOfUnit g 1) := by ring
            _ = 1 := by rw [h2, h3, mul_one]
        rw [this, mul_one]
    _ = ((f * g) * PowerSeries.invOfUnit (f * g) 1) *
          (PowerSeries.invOfUnit f 1 * PowerSeries.invOfUnit g 1) := by ring
    _ = _ := by rw [h1, one_mul]

/--
@isnad1 id=eq.2h3v.s9.80ff561cbcc8 from=translated src=- shape=2cb2b974 vocab=d088e143
-/
theorem logDer_mul (f g : PowerSeries K) (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.derivative K (f * g) * PowerSeries.invOfUnit (f * g) 1 =
      PowerSeries.derivative K f * PowerSeries.invOfUnit f 1 +
        PowerSeries.derivative K g * PowerSeries.invOfUnit g 1 := by
  have hf' : PowerSeries.constantCoeff f = ((1 : Kˣ) : K) := by simpa using hf
  have hg' : PowerSeries.constantCoeff g = ((1 : Kˣ) : K) := by simpa using hg
  have h2 := PowerSeries.mul_invOfUnit f 1 hf'
  have h3 := PowerSeries.mul_invOfUnit g 1 hg'
  rw [invOfUnit_mul_series f g hf hg, Derivation.leibniz]
  simp only [smul_eq_mul]
  linear_combination (PowerSeries.derivative K f * PowerSeries.invOfUnit f 1) * h3 +
    (PowerSeries.derivative K g * PowerSeries.invOfUnit g 1) * h2

/-- Product of two sequences in the commutative case: the series is the product.
@isnad1 id=eq.1h4v.s6.89a651df80ed from=translated src=- shape=45b28d19 vocab=91a096ae
-/
theorem mk_conv (cA cD cB : ℕ → K)
    (hB : ∀ n, cB n = ∑ p ∈ Finset.antidiagonal n, cA p.1 * cD p.2) :
    PowerSeries.mk cB = PowerSeries.mk cA * PowerSeries.mk cD := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, hB n]
  simp [PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h2v.s6.cb834110d3de from=translated src=- shape=3a4d0502 vocab=02a87b54
-/
theorem constantCoeff_mk' (c : ℕ → K) : PowerSeries.constantCoeff (PowerSeries.mk c) = c 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.3h5v.s7.7a1cd9dcc5a4 from=translated src=- shape=5dcb313a vocab=749204ec
-/
theorem psumG_conv_comm (cA cD cB : ℕ → K) (hA0 : cA 0 = 1) (hD0 : cD 0 = 1)
    (hB : ∀ n, cB n = ∑ p ∈ Finset.antidiagonal n, cA p.1 * cD p.2) (n : ℕ) :
    psumG cB n = psumG cA n + psumG cD n := by
  cases n with
  | zero => simp [psumG]
  | succ m =>
    have hf : PowerSeries.constantCoeff (PowerSeries.mk cA) = 1 := by
      rw [constantCoeff_mk', hA0]
    have hg : PowerSeries.constantCoeff (PowerSeries.mk cD) = 1 := by
      rw [constantCoeff_mk', hD0]
    rw [psumG_succ_comm, psumG_succ_comm, psumG_succ_comm, mk_conv cA cD cB hB,
      logDer_mul _ _ hf hg, map_add, smul_add]

/--
@isnad1 id=eq.3h7v.s7.7bb9cfac5486 from=translated src=- shape=617c8148 vocab=0b9d6fed
-/
theorem chG_conv_comm (rA rD : ℕ) (cA cD cB : ℕ → K) (hA0 : cA 0 = 1) (hD0 : cD 0 = 1)
    (hB : ∀ n, cB n = ∑ p ∈ Finset.antidiagonal n, cA p.1 * cD p.2) (n : ℕ) :
    chG (rA + rD) cB n = chG rA cA n + chG rD cD n := by
  cases n with
  | zero => simp [chG, add_smul]
  | succ m => simp only [chG, psumG_conv_comm cA cD cB hA0 hD0 hB, smul_add]

/-! #### `exp` of a series -/

/--
@isnad1 id=hassubst.1h2v.s6.e4acab14587d from=translated src=- shape=18747b96 vocab=20f2d46b
-/
theorem hasSubst_of_const_zero (L : PowerSeries K) (hL : PowerSeries.constantCoeff L = 0) :
    PowerSeries.HasSubst L :=
  PowerSeries.HasSubst.of_constantCoeff_zero' hL

/--
@isnad1 id=eq.2h4v.s8.9a6bfaecd0b9 from=translated src=- shape=c42954c0 vocab=8dafd915
-/
theorem coeff_pow_of_lt_of_const_zero (L : PowerSeries K) (hL : PowerSeries.constantCoeff L = 0)
    {m d : ℕ} (h : m < d) : PowerSeries.coeff m (L ^ d) = 0 := by
  obtain ⟨L₁, hL₁⟩ := PowerSeries.X_dvd_iff.mpr hL
  rw [hL₁, mul_pow, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]

/--
@isnad1 id=eq.1h3v.s9.d0a6d8967022 from=translated src=- shape=4de1e8d1 vocab=3531d80d
-/
theorem coeff_exp_subst (L : PowerSeries K) (hL : PowerSeries.constantCoeff L = 0) (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.exp K).subst L) =
      ∑ j ∈ Finset.range (m + 1), (1 / (j.factorial : ℚ)) • PowerSeries.coeff m (L ^ j) := by
  rw [PowerSeries.coeff_subst' (hasSubst_of_const_zero L hL)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m + 1))]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul, Algebra.smul_def]
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hd (by rw [coeff_pow_of_lt_of_const_zero L hL (by omega), smul_zero])

/--
@isnad1 id=eq.1h2v.s7.e80a50191c0d from=translated src=- shape=01a62b0f vocab=5eb51c21
-/
theorem constantCoeff_exp_subst (L : PowerSeries K) (hL : PowerSeries.constantCoeff L = 0) :
    PowerSeries.constantCoeff ((PowerSeries.exp K).subst L) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_exp_subst L hL]
  simp

/-- Uniqueness for the linear ODE `U' = U M`.
@isnad1 id=eq.3h4v.s9.adda61e6043e from=translated src=- shape=1b8d6b62 vocab=0a321e64
-/
theorem ode_unique (U V M : PowerSeries K)
    (hU : PowerSeries.derivative K U = U * M) (hV : PowerSeries.derivative K V = V * M)
    (h0 : PowerSeries.constantCoeff U = PowerSeries.constantCoeff V) : U = V := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    | succ n =>
      have e1 := congrArg (PowerSeries.coeff n) hU
      have e2 := congrArg (PowerSeries.coeff n) hV
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at e1 e2
      have hs : ∑ p ∈ Finset.antidiagonal n, PowerSeries.coeff p.1 U * PowerSeries.coeff p.2 M =
          ∑ p ∈ Finset.antidiagonal n, PowerSeries.coeff p.1 V * PowerSeries.coeff p.2 M := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [Finset.mem_antidiagonal] at hp
        rw [ih p.1 (by omega)]
      have h3 : PowerSeries.coeff (n + 1) U * ((n : K) + 1) =
          PowerSeries.coeff (n + 1) V * ((n : K) + 1) := by
        rw [e1, e2, hs]
      have hinv := natCast_succ_mul_inv (K := K) n
      calc PowerSeries.coeff (n + 1) U
          = PowerSeries.coeff (n + 1) U * (((n : K) + 1) * algebraMap ℚ K (1 / ((n : ℚ) + 1))) := by
            rw [hinv, mul_one]
        _ = (PowerSeries.coeff (n + 1) U * ((n : K) + 1)) * algebraMap ℚ K (1 / ((n : ℚ) + 1)) := by
            ring
        _ = (PowerSeries.coeff (n + 1) V * ((n : K) + 1)) * algebraMap ℚ K (1 / ((n : ℚ) + 1)) := by
            rw [h3]
        _ = PowerSeries.coeff (n + 1) V := by
            rw [mul_assoc, hinv, mul_one]

/-- The Todd log-series `Σ aₙ pₙ tⁿ`.-/
def toddLogSer (c : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c n

/--
@isnad1 id=eq.0h2v.s6.de72a092aec9 from=translated src=- shape=3630532e vocab=611ae2ff
-/
theorem constantCoeff_toddLogSer (c : ℕ → K) : PowerSeries.constantCoeff (toddLogSer c) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, toddLogSer, PowerSeries.coeff_mk]
  simp [toddLogCoeff, psumG]

/--
@isnad1 id=eq.0h3v.s7.5ed01350939b from=translated src=- shape=11d36362 vocab=4e4a5167
-/
theorem tdG_eq_coeff_exp (c : ℕ → K) (m : ℕ) :
    tdG c m = PowerSeries.coeff m ((PowerSeries.exp K).subst (toddLogSer c)) := by
  rw [coeff_exp_subst _ (constantCoeff_toddLogSer c)]
  rfl

end Comm

/-! ### Transfer from a commutative subalgebra to a ring with commuting coefficients -/
section Transfer

variable {R : Type u} [Ring R] [Algebra ℚ R]

open scoped IsMulCommutative in
/--
@isnad1 id=ex.1h2v.s7.da8a7fa014b2 from=translated src=- shape=7b3b4b21 vocab=a50ff502
-/
theorem exists_comm_lift (s : Set R) (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∃ (K : Type u) (_ : CommRing K) (_ : Algebra ℚ K) (φ : K →ₐ[ℚ] R),
      Function.Injective φ ∧ ∀ a ∈ s, ∃ a', φ a' = a := by
  haveI := Algebra.isMulCommutative_adjoin ℚ hs
  exact ⟨Algebra.adjoin ℚ s, inferInstance, inferInstance, (Algebra.adjoin ℚ s).val,
    Subtype.val_injective, fun a ha ↦ ⟨⟨a, Algebra.subset_adjoin ha⟩, rfl⟩⟩

/-- The hypotheses on three sequences: `cB` is the convolution of `cA` and `cD`, with unit
constant terms, and all coefficients of `cA`, `cD` commute pairwise.-/
structure ConvData (cA cD cB : ℕ → R) : Prop where
  /-- `c_0(A) = 1`.-/
  A0 : cA 0 = 1
  /-- `c_0(D) = 1`.-/
  D0 : cD 0 = 1
  /-- The coefficients of `cA` commute.-/
  AA : ∀ i j, cA i * cA j = cA j * cA i
  /-- The coefficients of `cD` commute.-/
  DD : ∀ i j, cD i * cD j = cD j * cD i
  /-- The coefficients of `cA` and `cD` commute.-/
  AD : ∀ i j, cA i * cD j = cD j * cA i
  /-- Whitney convolution.-/
  conv : ∀ n, cB n = ∑ p ∈ Finset.antidiagonal n, cA p.1 * cD p.2

/-- Common lift of a `ConvData` to a commutative algebra.
@isnad1 id=ex.1h4v.s8.cd24f1c964cf from=translated src=- shape=29a89671 vocab=b9d8041d
-/
theorem ConvData.lift {cA cD cB : ℕ → R} (h : ConvData cA cD cB) :
    ∃ (K : Type u) (_ : CommRing K) (_ : Algebra ℚ K) (φ : K →ₐ[ℚ] R) (a d b : ℕ → K),
      Function.Injective φ ∧ (∀ i, φ (a i) = cA i) ∧ (∀ i, φ (d i) = cD i) ∧ (∀ i, φ (b i) = cB i) ∧
      a 0 = 1 ∧ d 0 = 1 ∧ (∀ n, b n = ∑ p ∈ Finset.antidiagonal n, a p.1 * d p.2) := by
  have hs : ∀ x ∈ Set.range cA ∪ Set.range cD, ∀ y ∈ Set.range cA ∪ Set.range cD,
      x * y = y * x := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact h.AA i j
    · exact h.AD i j
    · exact (h.AD j i).symm
    · exact h.DD i j
  obtain ⟨K, _, _, φ, hinj, hl⟩ := exists_comm_lift _ hs
  choose a ha using fun i ↦ hl (cA i) (Or.inl ⟨i, rfl⟩)
  choose d hd using fun i ↦ hl (cD i) (Or.inr ⟨i, rfl⟩)
  refine ⟨K, inferInstance, inferInstance, φ, a, d,
    fun n ↦ ∑ p ∈ Finset.antidiagonal n, a p.1 * d p.2, hinj, ha, hd, ?_, ?_, ?_, fun n ↦ rfl⟩
  · intro n
    rw [map_sum, h.conv n]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_mul, ha, hd]
  · apply hinj
    rw [ha, h.A0, map_one]
  · apply hinj
    rw [hd, h.D0, map_one]

section ConvDataThms

variable {cA cD cB : ℕ → R}

/--
@isnad1 id=eq.1h5v.s6.80d753636164 from=translated src=- shape=0607b94f vocab=69959bc9
-/
theorem ConvData.lift_apply (h : ConvData cA cD cB) (n : ℕ) :
    psumG cB n = psumG cA n + psumG cD n := by
  obtain ⟨K, _, _, φ, a, d, b, hinj, ha, hd, hb, a0, d0, hconv⟩ := h.lift
  have b0 : b 0 = 1 := by simp [hconv 0, a0, d0]
  have e : ∀ (c : ℕ → K) (c' : ℕ → R), (∀ i, φ (c i) = c' i) → c 0 = 1 →
      ∀ n, φ (psumG c n) = psumG c' n := by
    intro c c' hc h0 n
    rw [psumG_map φ c h0]
    have : (fun i ↦ φ (c i)) = c' := funext hc
    rw [this]
  rw [← e b cB hb b0 n, ← e a cA ha a0 n, ← e d cD hd d0 n, ← map_add,
    psumG_conv_comm a d b a0 d0 hconv n]

/-- Newton power sums are additive on a convolution of commuting Chern sequences.
@isnad1 id=eq.1h5v.s6.80d753636164 from=translated src=- shape=0607b94f vocab=69959bc9
-/
theorem ConvData.psum (h : ConvData cA cD cB) (n : ℕ) :
    psumG cB n = psumG cA n + psumG cD n := h.lift_apply n

/-- The Chern character is additive.
@isnad1 id=eq.1h7v.s6.12fa18cbdf13 from=translated src=- shape=d0e93f44 vocab=93ba0da7
-/
theorem ConvData.ch (h : ConvData cA cD cB) (rA rD : ℕ) (n : ℕ) :
    chG (rA + rD) cB n = chG rA cA n + chG rD cD n := by
  cases n with
  | zero => simp [chG, add_smul]
  | succ m => simp only [chG, h.psum, smul_add]

end ConvDataThms

end Transfer

/-! ### Graded families of submodules -/
section Graded

/-- A multiplicative filtration-like family of `ℚ`-submodules `G n` (`G a * G b ⊆ G (a + b)`).
It is used twice: with `G n` = operators lowering dimension by `n`, and with `G n` a fixed
subalgebra.-/
structure GradedFam (R : Type*) [Ring R] [Algebra ℚ R] where
  /-- The pieces.-/
  G : ℕ → Submodule ℚ R
  /-- `1 ∈ G 0`.-/
  one_mem : (1 : R) ∈ G 0
  /-- Multiplicativity.-/
  mul_mem : ∀ {a b : ℕ} {x y : R}, x ∈ G a → y ∈ G b → x * y ∈ G (a + b)

variable {R : Type*} [Ring R] [Algebra ℚ R] (𝒢 : GradedFam R)

/-- The constant family attached to a subalgebra.-/
def GradedFam.const (S : Subalgebra ℚ R) : GradedFam R where
  G := fun _ ↦ S.toSubmodule
  one_mem := S.one_mem
  mul_mem := fun hx hy ↦ S.mul_mem hx hy

/-- A power series whose `n`-th coefficient lies in `G n`.-/
def GSer (F : PowerSeries R) : Prop := ∀ n, PowerSeries.coeff n F ∈ 𝒢.G n

variable {𝒢}

/--
@isnad1 id=gser.2h4v.s5.5626fc449722 from=translated src=- shape=1814d0b0 vocab=633bdf55
-/
theorem GSer.mul {F H : PowerSeries R} (hF : GSer 𝒢 F) (hH : GSer 𝒢 H) : GSer 𝒢 (F * H) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun p hp ↦ ?_
  have := 𝒢.mul_mem (hF p.1) (hH p.2)
  rwa [Finset.mem_antidiagonal.mp hp] at this

/--
@isnad1 id=gser.0h2v.s5.cec0c9b0d249 from=translated src=- shape=f86181c7 vocab=4c5e1764
-/
theorem GSer.one : GSer 𝒢 (1 : PowerSeries R) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; exact 𝒢.one_mem
  · exact Submodule.zero_mem _

/--
@isnad1 id=gser.1h4v.s5.d02f1153a669 from=translated src=- shape=757a7004 vocab=53b95e48
-/
theorem GSer.pow {F : PowerSeries R} (hF : GSer 𝒢 F) (j : ℕ) : GSer 𝒢 (F ^ j) := by
  induction j with
  | zero => rw [pow_zero]; exact GSer.one
  | succ j ih => rw [pow_succ]; exact ih.mul hF

/--
@isnad1 id=gser.1h3v.s6.97d776ff155f from=translated src=- shape=3783b6d4 vocab=6288da67
-/
theorem gSer_mk {c : ℕ → R} (hc : ∀ i, c i ∈ 𝒢.G i) : GSer 𝒢 (PowerSeries.mk c) := by
  intro n; rw [PowerSeries.coeff_mk]; exact hc n

/--
@isnad1 id=gser.1h3v.s6.18b592db4286 from=translated src=- shape=76fcce40 vocab=2f9a43c2
-/
theorem GSer.inv {c : ℕ → R} (hc : ∀ i, c i ∈ 𝒢.G i) :
    GSer 𝒢 (PowerSeries.invOfUnit (PowerSeries.mk c) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with h0
    · subst h0; simpa using 𝒢.one_mem
    · simp only [inv_one, Units.val_one, neg_mul, one_mul]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun x hx ↦ ?_)
      split_ifs with hlt
      · have := 𝒢.mul_mem (hc x.1) (ih x.2 hlt)
        rw [Finset.mem_antidiagonal.mp hx] at this
        simpa only [PowerSeries.coeff_mk] using this
      · exact Submodule.zero_mem _

/--
@isnad1 id=mem.2h5v.s8.35c1efe5ed67 from=translated src=- shape=8b283f6c vocab=6f85ed0b
-/
theorem coeff_mul_mem_shift {F H : PowerSeries R} (hF : ∀ n, PowerSeries.coeff n F ∈ 𝒢.G (n + 1))
    (hH : GSer 𝒢 H) (m : ℕ) : PowerSeries.coeff m (F * H) ∈ 𝒢.G (m + 1) := by
  rw [PowerSeries.coeff_mul]
  refine Submodule.sum_mem _ fun p hp ↦ ?_
  have := 𝒢.mul_mem (hF p.1) (hH p.2)
  have h2 : p.1 + 1 + p.2 = m + 1 := by
    have := Finset.mem_antidiagonal.mp hp
    omega
  rwa [h2] at this

/--
@isnad1 id=mem.1h4v.s7.ef0d2bb18e81 from=translated src=- shape=a7cae12b vocab=1b25872d
-/
theorem psumG_mem {c : ℕ → R} (hc : ∀ i, c i ∈ 𝒢.G i) (n : ℕ) : psumG c n ∈ 𝒢.G n := by
  cases n with
  | zero => exact Submodule.zero_mem _
  | succ m =>
    simp only [psumG]
    refine Submodule.smul_mem _ _ (coeff_mul_mem_shift (F := PowerSeries.mk fun n ↦
      ((n + 1 : ℕ) : ℚ) • c (n + 1)) ?_ (GSer.inv hc) m)
    intro n
    rw [PowerSeries.coeff_mk]
    exact Submodule.smul_mem _ _ (hc (n + 1))

/--
@isnad1 id=mem.1h5v.s7.a9270275f27c from=translated src=- shape=342bdc89 vocab=24644cf7
-/
theorem chG_mem {c : ℕ → R} (hc : ∀ i, c i ∈ 𝒢.G i) (r n : ℕ) : chG r c n ∈ 𝒢.G n := by
  cases n with
  | zero =>
    simp only [chG]
    exact Submodule.smul_mem _ _ 𝒢.one_mem
  | succ m => exact Submodule.smul_mem _ _ (psumG_mem hc _)

/--
@isnad1 id=mem.1h4v.s7.56e3400624e0 from=translated src=- shape=a7cae12b vocab=8d936a54
-/
theorem tdG_mem {c : ℕ → R} (hc : ∀ i, c i ∈ 𝒢.G i) (m : ℕ) : tdG c m ∈ 𝒢.G m := by
  unfold tdG
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
  refine (GSer.pow (F := PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c n) ?_ j) m
  intro n
  rw [PowerSeries.coeff_mk]
  exact Submodule.smul_mem _ _ (psumG_mem hc n)

end Graded

/-! ### Commuting with an element -/
section CommuteWith

variable {R : Type*} [Ring R] [Algebra ℚ R] (c : ℕ → R) (T : R)

/--
@isnad1 id=mem.1h4v.s7.9ebfa20decc3 from=translated src=- shape=3b80c648 vocab=836eb2de
-/
theorem mem_centralizer_of_commute (hT : ∀ i, T * c i = c i * T) (i : ℕ) :
    c i ∈ (GradedFam.const (Subalgebra.centralizer ℚ {T})).G i := by
  show _ ∈ Subalgebra.centralizer ℚ {T}
  rw [Subalgebra.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hT i

/--
@isnad1 id=eq.1h4v.s6.5f60d7145b23 from=translated src=- shape=9e5ba106 vocab=a8d96fa9
-/
theorem psumG_commute (hT : ∀ i, T * c i = c i * T) (n : ℕ) :
    T * psumG c n = psumG c n * T := by
  have : psumG c n ∈ Subalgebra.centralizer ℚ {T} :=
    psumG_mem (𝒢 := GradedFam.const (Subalgebra.centralizer ℚ {T})) (mem_centralizer_of_commute c T hT) n
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this T (Set.mem_singleton _)

/--
@isnad1 id=eq.1h5v.s6.b890268ca73d from=translated src=- shape=822349d4 vocab=a9dc1301
-/
theorem chG_commute (hT : ∀ i, T * c i = c i * T) (r n : ℕ) :
    T * chG r c n = chG r c n * T := by
  have : chG r c n ∈ Subalgebra.centralizer ℚ {T} :=
    chG_mem (𝒢 := GradedFam.const (Subalgebra.centralizer ℚ {T})) (mem_centralizer_of_commute c T hT) r n
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this T (Set.mem_singleton _)

/--
@isnad1 id=eq.1h4v.s6.033999929556 from=translated src=- shape=9e5ba106 vocab=e19d190c
-/
theorem tdG_commute (hT : ∀ i, T * c i = c i * T) (n : ℕ) :
    T * tdG c n = tdG c n * T := by
  have : tdG c n ∈ Subalgebra.centralizer ℚ {T} :=
    tdG_mem (𝒢 := GradedFam.const (Subalgebra.centralizer ℚ {T})) (mem_centralizer_of_commute c T hT) n
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this T (Set.mem_singleton _)

end CommuteWith

/-! ### Inverse of a product in a (noncommutative) power series ring -/
section InvProd

variable {R : Type*} [Ring R]

/--
@isnad1 id=eq.2h3v.s8.e0a7e0d8dc82 from=translated src=- shape=0fb24188 vocab=d962ee12
-/
theorem invOfUnit_mul_ring (f g : PowerSeries R) (hf : PowerSeries.constantCoeff f = 1)
    (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.invOfUnit (f * g) 1 = PowerSeries.invOfUnit g 1 * PowerSeries.invOfUnit f 1 := by
  have hfg : PowerSeries.constantCoeff (f * g) = ((1 : Rˣ) : R) := by simp [hf, hg]
  have hf' : PowerSeries.constantCoeff f = ((1 : Rˣ) : R) := by simpa using hf
  have hg' : PowerSeries.constantCoeff g = ((1 : Rˣ) : R) := by simpa using hg
  have h1 := PowerSeries.invOfUnit_mul (f * g) 1 hfg
  have h2 := PowerSeries.mul_invOfUnit f 1 hf'
  have h3 := PowerSeries.mul_invOfUnit g 1 hg'
  have h4 : (f * g) * (PowerSeries.invOfUnit g 1 * PowerSeries.invOfUnit f 1) = 1 := by
    rw [mul_assoc, ← mul_assoc g, h3, one_mul, h2]
  calc PowerSeries.invOfUnit (f * g) 1
      = PowerSeries.invOfUnit (f * g) 1 *
          ((f * g) * (PowerSeries.invOfUnit g 1 * PowerSeries.invOfUnit f 1)) := by rw [h4, mul_one]
    _ = (PowerSeries.invOfUnit (f * g) 1 * (f * g)) *
          (PowerSeries.invOfUnit g 1 * PowerSeries.invOfUnit f 1) := (mul_assoc _ _ _).symm
    _ = _ := by rw [h1, one_mul]

end InvProd

/-! ### Intertwining linear maps -/
section Inter

variable {M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]

/-- `u ∘ S = S' ∘ u`.-/
def Inter (u : M →ₗ[ℚ] N) (S : Module.End ℚ M) (S' : Module.End ℚ N) : Prop :=
  u ∘ₗ S = S' ∘ₗ u

variable {u : M →ₗ[ℚ] N}

/--
@isnad1 id=inter.0h3v.s7.4134d1c00933 from=translated src=- shape=114856f0 vocab=c9f6185b
-/
theorem Inter.zero : Inter u 0 0 := by simp [Inter]

/--
@isnad1 id=inter.0h3v.s6.7cd173163bb0 from=translated src=- shape=114856f0 vocab=c9f6185b
-/
theorem Inter.one : Inter u 1 1 := by
  simp [Inter, Module.End.one_eq_id]

/--
@isnad1 id=inter.2h7v.s7.006336a1fd08 from=translated src=- shape=79e7d561 vocab=356b591e
-/
theorem Inter.add {S₁ S₂ : Module.End ℚ M} {S₁' S₂' : Module.End ℚ N}
    (h₁ : Inter u S₁ S₁') (h₂ : Inter u S₂ S₂') : Inter u (S₁ + S₂) (S₁' + S₂') := by
  unfold Inter at *
  rw [LinearMap.comp_add, LinearMap.add_comp, h₁, h₂]

/--
@isnad1 id=inter.1h6v.s7.1455f989ee4c from=translated src=- shape=0fc2f391 vocab=eba5d7dd
-/
theorem Inter.smul (q : ℚ) {S : Module.End ℚ M} {S' : Module.End ℚ N} (h : Inter u S S') :
    Inter u (q • S) (q • S') := by
  unfold Inter at *
  rw [LinearMap.comp_smul, LinearMap.smul_comp, h]

/--
@isnad1 id=inter.1h5v.s7.a8930c563731 from=translated src=- shape=b419ca28 vocab=e41e19d3
-/
theorem Inter.neg {S : Module.End ℚ M} {S' : Module.End ℚ N} (h : Inter u S S') :
    Inter u (-S) (-S') := by
  have := h.smul (-1)
  simpa using this

/--
@isnad1 id=inter.2h7v.s7.86c6ad6bdfc5 from=translated src=- shape=79e7d561 vocab=6f28f196
-/
theorem Inter.mul {S₁ S₂ : Module.End ℚ M} {S₁' S₂' : Module.End ℚ N}
    (h₁ : Inter u S₁ S₁') (h₂ : Inter u S₂ S₂') : Inter u (S₁ * S₂) (S₁' * S₂') := by
  unfold Inter at *
  apply LinearMap.ext
  intro x
  have e1 := LinearMap.congr_fun h₁ (S₂ x)
  have e2 := LinearMap.congr_fun h₂ x
  simp only [LinearMap.comp_apply, Module.End.mul_apply] at e1 e2 ⊢
  rw [e1, e2]

/--
@isnad1 id=inter.1h7v.s7.e4da2ad881a6 from=translated src=- shape=627ad67b vocab=db90ee45
-/
theorem Inter.sum {ι : Type*} (s : Finset ι) {S : ι → Module.End ℚ M} {S' : ι → Module.End ℚ N}
    (h : ∀ i ∈ s, Inter u (S i) (S' i)) : Inter u (∑ i ∈ s, S i) (∑ i ∈ s, S' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Inter.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Coefficientwise intertwining of power series.-/
def ISer (u : M →ₗ[ℚ] N) (F : PowerSeries (Module.End ℚ M)) (F' : PowerSeries (Module.End ℚ N)) :
    Prop := ∀ n, Inter u (PowerSeries.coeff n F) (PowerSeries.coeff n F')

/--
@isnad1 id=iser.2h7v.s7.91503b75a71a from=translated src=- shape=7894927c vocab=8be47112
-/
theorem ISer.mul {F H : PowerSeries (Module.End ℚ M)} {F' H' : PowerSeries (Module.End ℚ N)}
    (hF : ISer u F F') (hH : ISer u H H') : ISer u (F * H) (F' * H') := by
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  exact Inter.sum _ fun p _ ↦ (hF p.1).mul (hH p.2)

/--
@isnad1 id=iser.0h3v.s7.ce09e5334320 from=translated src=- shape=e06d536f vocab=8f74b088
-/
theorem ISer.one : ISer u (1 : PowerSeries (Module.End ℚ M)) (1 : PowerSeries (Module.End ℚ N)) := by
  intro n
  rw [PowerSeries.coeff_one, PowerSeries.coeff_one]
  split_ifs
  · exact Inter.one
  · exact Inter.zero

/--
@isnad1 id=iser.1h6v.s7.19a603a167ab from=translated src=- shape=ddb55d9b vocab=c5945f26
-/
theorem ISer.pow {F : PowerSeries (Module.End ℚ M)} {F' : PowerSeries (Module.End ℚ N)}
    (hF : ISer u F F') (j : ℕ) : ISer u (F ^ j) (F' ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact ISer.one
  | succ j ih => rw [pow_succ, pow_succ]; exact ih.mul hF

/--
@isnad1 id=iser.1h5v.s6.bbcf0301a0ec from=translated src=- shape=8c574b41 vocab=7dba08a4
-/
theorem iSer_mk {c : ℕ → Module.End ℚ M} {c' : ℕ → Module.End ℚ N}
    (hc : ∀ i, Inter u (c i) (c' i)) : ISer u (PowerSeries.mk c) (PowerSeries.mk c') := by
  intro n; simpa using hc n

/--
@isnad1 id=iser.1h5v.s8.bce6c9f26e24 from=translated src=- shape=01f24e19 vocab=24aea9d2
-/
theorem ISer.inv {c : ℕ → Module.End ℚ M} {c' : ℕ → Module.End ℚ N}
    (hc : ∀ i, Inter u (c i) (c' i)) :
    ISer u (PowerSeries.invOfUnit (PowerSeries.mk c) 1)
      (PowerSeries.invOfUnit (PowerSeries.mk c') 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit, PowerSeries.coeff_invOfUnit]
    split_ifs with h0
    · simpa using Inter.one
    · simp only [inv_one, Units.val_one, neg_mul, one_mul]
      refine Inter.neg (Inter.sum _ fun x hx ↦ ?_)
      split_ifs with hlt
      · simpa using (hc x.1).mul (ih x.2 hlt)
      · exact Inter.zero

/--
@isnad1 id=inter.1h6v.s7.88fcc2f6551e from=translated src=- shape=cbb319d8 vocab=070f3927
-/
theorem psumG_inter {c : ℕ → Module.End ℚ M} {c' : ℕ → Module.End ℚ N}
    (hc : ∀ i, Inter u (c i) (c' i)) (n : ℕ) : Inter u (psumG c n) (psumG c' n) := by
  cases n with
  | zero => exact Inter.zero
  | succ m =>
    simp only [psumG]
    refine Inter.smul _ ?_
    have hd : ISer u (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c (n + 1)))
        (PowerSeries.mk (fun n ↦ ((n + 1 : ℕ) : ℚ) • c' (n + 1))) :=
      iSer_mk fun n ↦ (hc (n + 1)).smul _
    exact (hd.mul (ISer.inv hc)) m

/--
@isnad1 id=inter.1h7v.s7.b212a6194dbb from=translated src=- shape=70ce6642 vocab=0a9e537b
-/
theorem chG_inter {c : ℕ → Module.End ℚ M} {c' : ℕ → Module.End ℚ N}
    (hc : ∀ i, Inter u (c i) (c' i)) (r n : ℕ) : Inter u (chG r c n) (chG r c' n) := by
  cases n with
  | zero => exact Inter.one.smul _
  | succ m => exact (psumG_inter hc _).smul _

/--
@isnad1 id=inter.1h6v.s7.de6c2407667b from=translated src=- shape=cbb319d8 vocab=6c90bbbc
-/
theorem tdG_inter {c : ℕ → Module.End ℚ M} {c' : ℕ → Module.End ℚ N}
    (hc : ∀ i, Inter u (c i) (c' i)) (m : ℕ) : Inter u (tdG c m) (tdG c' m) := by
  unfold tdG
  refine Inter.sum _ fun j _ ↦ Inter.smul _ ?_
  have hL : ISer u (PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c n)
      (PowerSeries.mk fun n ↦ toddLogCoeff n • psumG c' n) :=
    iSer_mk fun n ↦ (psumG_inter hc n).smul _
  exact (hL.pow j) m

end Inter

end AlgebraicGeometry.Chow.M7.M7ASM
