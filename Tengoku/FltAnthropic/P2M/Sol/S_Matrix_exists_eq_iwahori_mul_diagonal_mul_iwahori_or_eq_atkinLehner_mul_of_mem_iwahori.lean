import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.lean`: removed 4 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
namespace P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori

section LevelULocalBlock

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LevelULocal

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

def pr : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)

/--
@isnad1 id=prime.0h1v.s3.698370a2b5c6 from=translated src=- shape=32354d46 vocab=77e6247e
-/
theorem pr_prime : (pr v).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

/--
@isnad1 id=fact.0h1v.s3.ec24230f1203 from=translated src=- shape=bee9f040 vocab=02bced59
-/
scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

/--
@isnad1 id=ne.0h1v.s4.cebc5a012d6e from=translated src=- shape=c0e41946 vocab=5d3bd90d
-/
theorem pr_ne_zero : pr v ≠ 0 := (pr_prime v).ne_zero
/--
@isnad1 id=eq.0h1v.s4.041d31cb96ad from=translated src=- shape=5ae2e4d5 vocab=d2288a8d
-/
theorem natGenerator_eq_pr : Rat.HeightOneSpectrum.natGenerator v = pr v := rfl
/--
@isnad1 id=iff.0h2v.s7.8afe216250f4 from=translated src=- shape=a59a80cb vocab=46c37ad9
-/
theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

/--
@isnad1 id=iff.0h2v.s7.f44b8b469843 from=translated src=- shape=ffd93404 vocab=d1df84ce
-/
theorem natCast_mem_asIdeal_iff_pr_dvd (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pr v ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]

/--
@isnad1 id=eq.0h1v.s6.97700f6e5066 from=translated src=- shape=60736f74 vocab=54091408
-/
theorem asIdeal_eq_span_pr : v.asIdeal = Ideal.span {(pr v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  rw [natGenerator_eq_pr] at h
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

/--
@isnad1 id=eq.0h1v.s6.2332990fbff8 from=translated src=- shape=0f359a61 vocab=42d0b12b
-/
theorem valuation_pr : v.valuation ℚ (pr v : ℚ) = WithZero.exp (-1) := by
  rw [show (pr v : ℚ) = algebraMap (𝓞 ℚ) ℚ (pr v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast pr_ne_zero v)
    (asIdeal_eq_span_pr v)

/--
@isnad1 id=eq.0h2v.s9.855ecbd84dfd from=translated src=- shape=99a5a5bc vocab=bebd3a09
-/
theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ 𝕂 r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

/--
@isnad1 id=eq.0h2v.s8.c43dee60edd4 from=translated src=- shape=c98e70c2 vocab=d895a768
-/
theorem algebraMap_natCast (n : ℕ) : algebraMap ℚ 𝕂 (n : ℚ) = (n : 𝕂) := map_natCast _ n
/--
@isnad1 id=eq.0h1v.s8.813cb9b536ba from=translated src=- shape=c6edf309 vocab=4f051caa
-/
theorem valued_pr : Valued.v ((pr v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_pr]
/--
@isnad1 id=ne.0h1v.s8.9d8b5bf6b6cb from=translated src=- shape=31bc7237 vocab=4fdacb2c
-/
theorem pr_ne_zero' : ((pr v : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_pr v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

/--
@isnad1 id=mem.0h2v.s8.5261912db99e from=translated src=- shape=c1c1b6e8 vocab=fe3db615
-/
theorem natCast_mem_integers (n : ℕ) : ((n : ℕ) : 𝕂) ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

/--
@isnad1 id=mem.0h1v.s8.1925b66eaf2c from=translated src=- shape=fc5b79c1 vocab=703850c7
-/
theorem pr_mem_integers : ((pr v : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers v _

/--
@isnad1 id=le.1h2v.s8.ddf6156ae3b8 from=translated src=- shape=68a9801e vocab=ff7f4337
-/
theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hx

/--
@isnad1 id=iff.1h2v.s10.3c4799c597a3 from=translated src=- shape=becb9cc0 vocab=0caf8eb9
-/
theorem pr_inv_mul_mem_integers_iff {x : 𝕂} (hx : x ∈ 𝓞v) :
    ((pr v : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v ↔ Valued.v x < 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_pr]
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
      ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    rw [hm, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_lt_exp]
    omega

/--
@isnad1 id=mem.1h2v.s9.174f1d15a71e from=translated src=- shape=aba8ae88 vocab=8028f592
-/
theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

end Places

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

/--
@isnad1 id=iff.0h2v.s9.77d3ee55bd94 from=translated src=- shape=d76ec0b1 vocab=25c88f55
-/
theorem mem_intMat_iff (M : M₂) : M ∈ intMat v ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl
/--
@isnad1 id=mem.2h3v.s10.dce5f7d0b289 from=translated src=- shape=36d950b8 vocab=6924f676
-/
theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat v) : c • M ∈ intMat v :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)
/--
@isnad1 id=mem.1h2v.s9.cce02c5ed250 from=translated src=- shape=0c4713a4 vocab=fe93b867
-/
theorem det_mem_integers {M : M₂} (hM : M ∈ intMat v) : M.det ∈ 𝓞v := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

/--
@isnad1 id=mem.1h2v.s9.2c844a61e416 from=translated src=- shape=53f553f3 vocab=f0917659
-/
theorem adjugate_mem_intMat {M : M₂} (hM : M ∈ intMat v) : M.adjugate ∈ intMat v := by
  rw [Matrix.adjugate_fin_two]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hM 1 1
  · simpa using neg_mem (hM 0 1)
  · simpa using neg_mem (hM 1 0)
  · simpa using hM 0 0

theorem eq_smul_adjugate {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi = M.det⁻¹ • M.adjugate := by
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have key : Mi * (M * M.adjugate) = M.det • Mi := by
    rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
  rw [← mul_assoc, h2, one_mul] at key
  rw [key, smul_smul, inv_mul_cancel₀ hdet, one_smul]

/--
@isnad1 id=eq.1h3v.s10.874313c754d6 from=translated src=- shape=3fb44161 vocab=fb588f09
-/
theorem det_mul_det_eq_one {M Mi : M₂} (h1 : M * Mi = 1) : M.det * Mi.det = 1 := by
  rw [← Matrix.det_mul, h1, Matrix.det_one]

/--
@isnad1 id=mem.4h3v.s11.1aa05a7c4abd from=translated src=- shape=92e8365e vocab=ee3d6549
-/
theorem inv_mem_intMat_of_valued_det {M Mi : M₂} (hM : M ∈ intMat v) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : Valued.v M.det = 1) : Mi ∈ intMat v := by
  rw [eq_smul_adjugate v h1 h2]
  exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hdet) (adjugate_mem_intMat v hM)

/--
@isnad1 id=eq.2h3v.s10.96bc8ceb1510 from=translated src=- shape=b762f5dd vocab=f375d39d
-/
theorem inv_apply_one_zero {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi 1 0 = -(M.det⁻¹ * M 1 0) := by
  rw [eq_smul_adjugate v h1 h2, Matrix.adjugate_fin_two]
  simp

def tM : M₂ := !![1, 0; 0, ϖ]

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

def tbM : M₂ := !![ϖ, 0; 0, 1]

def tbMi : M₂ := !![ϖ⁻¹, 0; 0, 1]

def wM : M₂ := !![0, 1; 1, 0]

/--
@isnad1 id=eq.0h2v.s10.4900ea95d589 from=translated src=- shape=351498d5 vocab=0a8d92a9
-/
theorem tMi_mul_mul_tM (Y : M₂) : tMi v * Y * tM v = !![Y 0 0, ϖ * Y 0 1; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tM, tMi] <;> field_simp

/--
@isnad1 id=iff.1h2v.s10.2f3008fc8b43 from=translated src=- shape=a8ae7b18 vocab=499d2997
-/
theorem tMi_mul_mul_tM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tMi v * Y * tM v ∈ intMat v ↔ Valued.v (Y 1 0) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 1 0), tMi_mul_mul_tM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using hY 0 0
    · simpa using mul_mem (pr_mem_integers v) (hY 0 1)
    · simpa using h
    · simpa using hY 1 1

/--
@isnad1 id=ex.2h2v.s10.f7c89373e4d7 from=translated src=- shape=9db63cec vocab=fd819f74
-/
theorem exists_exp_valued_det {Y : M₂} (hY : Y ∈ intMat v) (hdet : Y.det ≠ 0) :
    ∃ m : ℤ, m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have h0 : Valued.v Y.det ≠ 0 := (Valuation.ne_zero_iff _).2 hdet
  have hm : Valued.v Y.det = WithZero.exp (WithZero.log (Valued.v Y.det)) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v Y.det), ?_, hm⟩
  have := valued_le_one_of_mem v (det_mem_integers v hY)
  rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  exact this

/--
@isnad1 id=ex.3h3v.s11.a9a0108a6be7 from=translated src=- shape=2da220c0 vocab=aa2dfd26
-/
theorem valued_det_bounds {Y Yi : M₂} (h1 : Y * Yi = 1) (hY : Y ∈ intMat v) (hpYi : ϖ • Yi ∈ intMat v) :
    ∃ m : ℤ, -2 ≤ m ∧ m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have hdet0 : Y.det ≠ 0 := fun h => by
    have := det_mul_det_eq_one v h1; rw [h, zero_mul] at this; exact zero_ne_one this
  obtain ⟨m, hm0, hm⟩ := exists_exp_valued_det v hY hdet0
  refine ⟨m, ?_, hm0, hm⟩

  have h2 := valued_le_one_of_mem v (det_mem_integers v hpYi)
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, valued_pr] at h2
  have hYi : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have := det_mul_det_eq_one v h1
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, this, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  rw [hYi, hm, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h2
  omega

end LocalMatrix

section LocalMatrix2

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

end LocalMatrix2

section Eichler

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def dM (e : ℕ) : M₂ := !![1, 0; 0, ϖ ^ e]

def dMi (e : ℕ) : M₂ := !![1, 0; 0, (ϖ ^ e)⁻¹]

def E00 : M₂ := !![1, 0; 0, 0]

def E01 : M₂ := !![0, 1; 0, 0]

end Eichler

section Peirce

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def E10 : M₂ := !![0, 0; 1, 0]

def E11 : M₂ := !![0, 0; 0, 1]

/--
@isnad1 id=ex.5h2v.s13.f5bd46f0c8ca from=translated src=- shape=f18c63e7 vocab=d6d06a09
-/
theorem exists_iwahori_mul_tbM_mul {Y : M₂} (hY : Y ∈ intMat v) (h00 : ϖ⁻¹ * Y 0 0 ∈ 𝓞v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v)
    (h11 : Valued.v (Y 1 1) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι' := by
  have hp0 := pr_ne_zero' v
  set α := ϖ⁻¹ * Y 0 0 with hα
  set γ := ϖ⁻¹ * Y 1 0 with hγ
  set β := Y 0 1 with hβ
  set δ := Y 1 1 with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  have hδi : δ⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h11
  have hY00 : Y 0 0 = ϖ * α := by rw [hα, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY10 : Y 1 0 = ϖ * γ := by rw [hγ, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set α' := α - β * γ * δ⁻¹ with hα'
  have hα'O : α' ∈ 𝓞v := sub_mem h00 (mul_mem (mul_mem (hY 0 1) h10) hδi)
  have hdet' : Y.det = ϖ * (α' * δ) := by
    rw [Matrix.det_fin_two, hY00, hY10, hα']; field_simp; ring
  have hαδ : Valued.v (α' * δ) = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (α' * δ) = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (α' * δ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hα'v : Valued.v α' = 1 := by
    rw [map_mul, h11, mul_one] at hαδ; exact hαδ
  have hα'0 : α' ≠ 0 := fun h0 => by rw [h0, map_zero] at hα'v; exact zero_ne_one hα'v
  have hα'i : α'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hα'v
  have hβO : β ∈ 𝓞v := hY 0 1
  have hδO : δ ∈ 𝓞v := hY 1 1
  have hx : ϖ * γ * δ⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hδi
  have hnx : -(ϖ * γ * δ⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(β * α'⁻¹ * δ⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hβO hα'i) hδi)
  refine ⟨!![α', β; 0, δ], !![α'⁻¹, -(β * α'⁻¹ * δ⁻¹); 0, δ⁻¹], !![1, 0; ϖ * γ * δ⁻¹, 1], !![1, 0; -(ϖ * γ * δ⁻¹), 1],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'O, hβO, zero_mem, hδO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'i, hδi, zero_mem, hy]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zero_mem]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * γ * δ⁻¹) = γ * δ⁻¹ by field_simp]
    exact mul_mem h10 hδi
  · ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tbM, hY00, hY10, hα'] <;> (try field_simp) <;> ring

/--
@isnad1 id=ex.5h2v.s13.1c27aaf1d67f from=translated src=- shape=f18c63e7 vocab=a950a201
-/
theorem exists_iwahori_mul_tM_mul {Y : M₂} (hY : Y ∈ intMat v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * Y 1 1 ∈ 𝓞v)
    (h00 : Valued.v (Y 0 0) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tM v * ι' := by
  have hp0 := pr_ne_zero' v
  set a := Y 0 0 with ha
  set b := Y 0 1 with hb
  set c := ϖ⁻¹ * Y 1 0 with hc
  set d := ϖ⁻¹ * Y 1 1 with hd
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, map_zero] at h00; exact zero_ne_one h00
  have hai : a⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h00
  have hY10 : Y 1 0 = ϖ * c := by rw [hc, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY11 : Y 1 1 = ϖ * d := by rw [hd, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set d' := d - c * b * a⁻¹ with hd'
  have hd'O : d' ∈ 𝓞v := sub_mem h11 (mul_mem (mul_mem h10 (hY 0 1)) hai)
  have hdet' : Y.det = ϖ * (a * d') := by
    rw [Matrix.det_fin_two, hY10, hY11, hd']; field_simp; ring
  have had : Valued.v (a * d') = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (a * d') = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (a * d')) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hd'v : Valued.v d' = 1 := by rw [map_mul, h00, one_mul] at had; exact had
  have hd'0 : d' ≠ 0 := fun h0 => by rw [h0, map_zero] at hd'v; exact zero_ne_one hd'v
  have hd'i : d'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hd'v
  have haO : a ∈ 𝓞v := hY 0 0
  have hbO : b ∈ 𝓞v := hY 0 1
  have hx : ϖ * c * a⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hai
  have hnx : -(ϖ * c * a⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(b * a⁻¹ * d'⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hbO hai) hd'i)
  refine ⟨!![1, 0; ϖ * c * a⁻¹, 1], !![1, 0; -(ϖ * c * a⁻¹), 1], !![a, b; 0, d'], !![a⁻¹, -(b * a⁻¹ * d'⁻¹); 0, d'⁻¹],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hd'O, hbO, zero_mem, haO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hai, hd'i, zero_mem, hy]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * c * a⁻¹) = c * a⁻¹ by field_simp]
    exact mul_mem h10 hai
  · simp [zero_mem]
  · ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tM, hY10, hY11, hd'] <;> (try field_simp) <;> ring

end Peirce

section IwahoriHecke

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def alM : M₂ := !![0, 1; ϖ, 0]
def alMi : M₂ := !![0, ϖ⁻¹; 1, 0]

/--
@isnad1 id=eq.0h1v.s9.e67635a10cc8 from=translated src=- shape=3df2d618 vocab=f042802a
-/
theorem alM_mul_alMi : alM v * alMi v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, mul_inv_cancel₀ hp0]
/--
@isnad1 id=eq.0h1v.s9.86fe16b84980 from=translated src=- shape=3df2d618 vocab=f042802a
-/
theorem alMi_mul_alM : alMi v * alM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, inv_mul_cancel₀ hp0]

/--
@isnad1 id=iff.1h2v.s11.0c2375a9ca5b from=translated src=- shape=432737b6 vocab=6462a4cc
-/
theorem iwahori_iff {X : M₂} (hX : X ∈ intMat v) : tMi v * X * tM v ∈ intMat v ↔ ϖ⁻¹ * X 1 0 ∈ 𝓞v :=
  (tMi_mul_mul_tM_mem_iff v hX).trans (pr_inv_mul_mem_integers_iff v (hX 1 0)).symm

/--
@isnad1 id=or.1h2v.s9.74665b36b533 from=translated src=- shape=17d3df6e vocab=e0b7a200
-/
theorem valued_eq_one_or_pr_inv_mul_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x = 1 ∨ ϖ⁻¹ * x ∈ 𝓞v := by
  rcases (valued_le_one_of_mem v hx).lt_or_eq with h | h
  · exact Or.inr ((pr_inv_mul_mem_integers_iff v hx).2 h)
  · exact Or.inl h

/--
@isnad1 id=lt.3h2v.s11.5430bfbaa753 from=translated src=- shape=6ca76659 vocab=c962a8de
-/
theorem valued_diag_mul_lt_one {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) : Valued.v (η 0 0 * η 1 1) < 1 := by
  have hp0 := pr_ne_zero' v
  have e1 : η 0 0 * η 1 1 = η.det + η 0 1 * (ϖ * (ϖ⁻¹ * η 1 0)) := by
    rw [mul_inv_cancel_left₀ hp0, Matrix.det_fin_two]; ring
  rw [e1]
  refine lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt ?_ ?_)
  · rw [hdet, valued_pr, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  · rw [map_mul, map_mul, valued_pr]
    calc Valued.v (η 0 1) * (WithZero.exp (-1) * Valued.v (ϖ⁻¹ * η 1 0))
        ≤ 1 * (WithZero.exp (-1) * 1) :=
          mul_le_mul' (valued_le_one_of_mem v (hη 0 1)) (mul_le_mul_right (valued_le_one_of_mem v h10) _)
      _ < 1 := by rw [one_mul, mul_one, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)

/--
@isnad1 id=mem.4h2v.s11.ddaa9e50d0cf from=translated src=- shape=a88c0065 vocab=e842b42e
-/
theorem pr_inv_mul_apply_zero_zero_mem {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) (h11 : Valued.v (η 1 1) = 1) : ϖ⁻¹ * η 0 0 ∈ 𝓞v := by
  have h := valued_diag_mul_lt_one v hη h10 hdet
  rw [map_mul, h11, mul_one] at h
  exact (pr_inv_mul_mem_integers_iff v (hη 0 0)).2 h

/--
@isnad1 id=and.5h3v.s12.89bc146af14d from=translated src=- shape=91523c04 vocab=5c197a72
-/
theorem iwahori_inv_mem {κ κi : M₂} (h1 : κ * κi = 1) (h2 : κi * κ = 1) (hκ : κ ∈ intMat v)
    (hκ' : tMi v * κ * tM v ∈ intMat v) (hdet : Valued.v κ.det = 1) :
    κi ∈ intMat v ∧ tMi v * κi * tM v ∈ intMat v := by
  have hκiO : κi ∈ intMat v := inv_mem_intMat_of_valued_det v hκ h1 h2 hdet
  refine ⟨hκiO, (iwahori_iff v hκiO).2 ?_⟩
  rw [inv_apply_one_zero v h1 h2, mul_neg, ← mul_assoc, mul_comm ϖ⁻¹, mul_assoc]
  exact neg_mem (mul_mem (inv_mem_integers_of_valued_eq_one v hdet) ((iwahori_iff v hκ).1 hκ'))

end IwahoriHecke

section ULocal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

/--
@isnad1 id=eq.8h3v.s13.be302c95a8ac from=translated src=- shape=9930d608 vocab=5c4be3f7
-/
theorem valued_det_eq_valued_pr {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v)) :
    Valued.v Y.det = Valued.v ϖ := by
  have hp0 := pr_ne_zero' v
  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v h1 hY hpYi
  have hvp : Valued.v ϖ = WithZero.exp (-1) := valued_pr v
  have hYidet : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, det_mul_det_eq_one v h1, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  obtain rfl | rfl | rfl : m = -2 ∨ m = -1 ∨ m = 0 := by omega
  · exfalso
    apply hpY
    have hZ1 : (ϖ • Yi) * (ϖ⁻¹ • Y) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul, h2]
    have hZ2 : (ϖ⁻¹ • Y) * (ϖ • Yi) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul, h1]
    have hdetZ : Valued.v (ϖ • Yi).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, hvp, hYidet, hm, ← WithZero.exp_nsmul,
        ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
      congr 1
    exact iwahori_inv_mem v hZ1 hZ2 hpYi hpYi' hdetZ
  · rw [hm, hvp]
  · exfalso
    apply hYi
    have hdet1 : Valued.v Y.det = 1 := by rw [hm, WithZero.exp_zero]
    exact iwahori_inv_mem v h1 h2 hY hY' hdet1

end ULocal

section Lib

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

/--
@isnad1 id=ex.7h3v.s12.847b0460d4c4 from=translated src=- shape=fbaf2ac1 vocab=ccde6948
-/
theorem exists_eq_alM_mul {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1) (hη : η ∈ intMat v)
    (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h00 : ϖ⁻¹ * η 0 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * η 1 1 ∈ 𝓞v) :
    ∃ κ κi : M₂, κ ∈ intMat v ∧ κi ∈ intMat v ∧ κ * κi = 1 ∧ κi * κ = 1 ∧ ϖ⁻¹ * κ 1 0 ∈ 𝓞v ∧ η = alM v * κ := by
  have hp0 := pr_ne_zero' v
  set κ : M₂ := alMi v * η with hκ
  set κi : M₂ := ηi * alM v with hκi
  have hηκ : η = alM v * κ := by rw [hκ, ← mul_assoc, alM_mul_alMi, one_mul]
  have hκκi : κ * κi = 1 := by
    rw [hκ, hκi, show alMi v * η * (ηi * alM v) = alMi v * (η * ηi) * alM v by noncomm_ring, h1, mul_one, alMi_mul_alM]
  have hκiκ : κi * κ = 1 := by
    rw [hκ, hκi, show ηi * alM v * (alMi v * η) = ηi * (alM v * alMi v) * η by noncomm_ring, alM_mul_alMi, mul_one, h2]
  have eκ : κ = !![ϖ⁻¹ * η 1 0, ϖ⁻¹ * η 1 1; η 0 0, η 0 1] := by
    rw [hκ]; ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [alMi]
  have hκO : κ ∈ intMat v := by
    rw [eκ]; intro i j; fin_cases i <;> fin_cases j <;> simp [h10, h11, hη 0 0, hη 0 1]
  have hκ10 : κ 1 0 = η 0 0 := by rw [eκ]; simp
  have hκ' : tMi v * κ * tM v ∈ intMat v := by rw [iwahori_iff v hκO, hκ10]; exact h00
  have hκdet : Valued.v κ.det = 1 := by
    have : κ.det = -(ϖ⁻¹ * η.det) := by
      rw [eκ, Matrix.det_fin_two, Matrix.det_fin_two]; simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  obtain ⟨hκiO, -⟩ := iwahori_inv_mem v hκκi hκiκ hκO hκ' hκdet
  exact ⟨κ, κi, hκO, hκiO, hκκi, hκiκ, by rw [hκ10]; exact h00, hηκ⟩

/--
@isnad1 id=and.8h3v.s14.3210c7b44aa1 from=translated src=- shape=a26f46ac vocab=5c0e3364
-/
theorem trichotomy {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v)) :
    Valued.v Y.det = Valued.v ϖ ∧
    ((∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι') ∨
     (∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tM v * ι') ∨
     (∃ κ κi : M₂, κ ∈ intMat v ∧ κi ∈ intMat v ∧ κ * κi = 1 ∧ κi * κ = 1 ∧ ϖ⁻¹ * κ 1 0 ∈ 𝓞v ∧ Y = alM v * κ)) := by
  have hdet := valued_det_eq_valued_pr v h1 h2 hY hY' hpYi hpYi' hYi hpY
  have h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v := (iwahori_iff v hY).1 hY'
  refine ⟨hdet, ?_⟩
  rcases valued_eq_one_or_pr_inv_mul_mem v (hY 1 1) with h11 | h11
  · exact Or.inl (exists_iwahori_mul_tbM_mul v hY (pr_inv_mul_apply_zero_zero_mem v hY h10 hdet h11) h10 h11 hdet)
  · rcases valued_eq_one_or_pr_inv_mul_mem v (hY 0 0) with h00 | h00
    · exact Or.inr (Or.inl (exists_iwahori_mul_tM_mul v hY h10 h11 h00 hdet))
    · exact Or.inr (Or.inr (exists_eq_alM_mul v h1 h2 hY h10 hdet h00 h11))

end Lib

section Card

/--
@isnad1 id=eq.2h2v.s7.e2e1ee4ce773 from=translated src=- shape=c9b0eafb vocab=5feb3b99
-/
theorem pr_eq_of_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) : pr v = p :=
  (Nat.prime_dvd_prime_iff_eq (pr_prime v) hp).1 ((natCast_mem_asIdeal_iff_pr_dvd v p).1 hpv)

end Card

end LevelULocal
open scoped _root_.P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal

end
open scoped _root_.P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal

end LevelULocalBlock
open scoped _root_.P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal

open IsDedekindDomain NumberField

/--
@isnad1 id=and.10h4v.s14.0a8512fb031d from=translated src=- shape=790cd922 vocab=e3570b86
-/
theorem solution
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ) (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ)) :
    Valued.v Y.det = Valued.v (p : v.adicCompletion ℚ) ∧
    ((∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![(p : v.adicCompletion ℚ), 0; 0, 1] * ι') ∨
     (∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![1, 0; 0, (p : v.adicCompletion ℚ)] * ι') ∨
     (∃ κ κi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, κ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, κi i j ∈ v.adicCompletionIntegers ℚ) ∧ κ * κi = 1 ∧ κi * κ = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * κ 1 0 ∈ v.adicCompletionIntegers ℚ ∧ Y = !![0, 1; (p : v.adicCompletion ℚ), 0] * κ)) := by
  have hpr := LevelULocal.pr_eq_of_mem p hp v hpv
  subst hpr
  have hYI : Y ∈ LevelULocal.intMat v := hY
  have hpYiI : ((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ) • Yi ∈ LevelULocal.intMat v := hpYi
  have hY' := (LevelULocal.iwahori_iff v hYI).2 hY10
  have hpYi' := (LevelULocal.iwahori_iff v hpYiI).2 hpYi10
  have hYi2 : ¬ (Yi ∈ LevelULocal.intMat v ∧ LevelULocal.tMi v * Yi * LevelULocal.tM v ∈ LevelULocal.intMat v) :=
    fun H => hYi ⟨H.1, (LevelULocal.iwahori_iff v H.1).1 H.2⟩
  have hpY2 : ¬ (((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ)⁻¹ • Y ∈ LevelULocal.intMat v ∧
      LevelULocal.tMi v * (((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ)⁻¹ • Y) * LevelULocal.tM v ∈ LevelULocal.intMat v) :=
    fun H => hpY ⟨H.1, (LevelULocal.iwahori_iff v H.1).1 H.2⟩
  exact LevelULocal.trichotomy v h1 h2 hYI hY' hpYiI hpYi' hYi2 hpY2
