import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian

set_option autoImplicit false

noncomputable section

open scoped SchwartzMap ContDiff ComplexConjugate Classical
open NumberField NumberField.InfinitePlace

namespace R4Joint

section Gauss

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def q (z : H) : ℝ := -Real.pi * ‖z‖ ^ 2

def ipB : H →L[ℝ] H →L[ℝ] ℝ :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := H)).toContinuousLinearMap

/--
@isnad1 id=eq.0h3v.s9.05fe0f7b8bcc from=translated src=- shape=44bb5c95 vocab=d7333ddd
-/
theorem ipB_apply (z y : H) : ipB z y = inner ℝ z y :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := H)).toContinuousLinearMap_apply z y

/--
@isnad1 id=le.0h2v.s9.c0a409dbe95e from=translated src=- shape=c0b5f384 vocab=6f01333a
-/
theorem norm_ipB_apply (z : H) : ‖(ipB : H →L[ℝ] H →L[ℝ] ℝ) z‖ ≤ ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z) fun y => ?_
  rw [ipB_apply]
  exact abs_real_inner_le_norm z y

def qDeriv : H →L[ℝ] (H →L[ℝ] ℝ) := (-(2 * Real.pi)) • (ipB : H →L[ℝ] H →L[ℝ] ℝ)

/--
@isnad1 id=contdiff.0h2v.s5.07914d433189 from=translated src=- shape=f7dafc7d vocab=1ae4367b
-/
theorem contDiff_q {n : WithTop ℕ∞} : ContDiff ℝ n (q : H → ℝ) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

/--
@isnad1 id=eq.0h1v.s9.6b9efa0b75f0 from=translated src=- shape=3ced8952 vocab=f4e9f6cf
-/
theorem fderiv_q : fderiv ℝ (q : H → ℝ) = ⇑(qDeriv : H →L[ℝ] (H →L[ℝ] ℝ)) := by
  funext z
  have h1 : (q : H → ℝ) = fun z => (-Real.pi) * ‖z‖ ^ 2 := rfl
  rw [h1, fderiv_const_mul ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero z),
    fderiv_norm_sq_apply]
  ext y
  rw [_root_.smul_apply, two_smul, add_apply, innerSL_apply_apply,
    qDeriv, _root_.smul_apply, _root_.smul_apply, ipB_apply, smul_eq_mul,
    smul_eq_mul]
  ring

/--
@isnad1 id=le.0h2v.s9.e2cdf8766b18 from=translated src=- shape=c88c9c0e vocab=4d1d1727
-/
theorem norm_qDeriv_apply (z : H) : ‖(qDeriv : H →L[ℝ] (H →L[ℝ] ℝ)) z‖ ≤ 2 * Real.pi * ‖z‖ := by
  rw [qDeriv, _root_.smul_apply, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_ipB_apply z) (by positivity)

/--
@isnad1 id=le.0h1v.s8.72f472eb3a0f from=translated src=- shape=59ac4318 vocab=ea016f3f
-/
theorem norm_qDeriv_le : ‖(qDeriv : H →L[ℝ] (H →L[ℝ] ℝ))‖ ≤ 2 * Real.pi := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  exact norm_qDeriv_apply z

/--
@isnad1 id=le.0h2v.s8.ad1f6cd058e3 from=translated src=- shape=ad2f6881 vocab=f55d3be5
-/
theorem norm_iteratedFDeriv_q_one (z : H) : ‖iteratedFDeriv ℝ 1 (q : H → ℝ) z‖ ≤ 2 * Real.pi * ‖z‖ := by
  rw [norm_iteratedFDeriv_one, fderiv_q]
  exact norm_qDeriv_apply z

/--
@isnad1 id=le.0h2v.s7.6b8c14b2cb52 from=translated src=- shape=2b197a92 vocab=f55d3be5
-/
theorem norm_iteratedFDeriv_q_two (z : H) : ‖iteratedFDeriv ℝ 2 (q : H → ℝ) z‖ ≤ 2 * Real.pi := by
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, fderiv_q, ContinuousLinearMap.fderiv]
  exact norm_qDeriv_le

/--
@isnad1 id=eq.0h3v.s8.43f0cc3ed8d0 from=translated src=- shape=61264725 vocab=189fc5e1
-/
theorem iteratedFDeriv_q_add_three (j : ℕ) (z : H) : ‖iteratedFDeriv ℝ (j + 3) (q : H → ℝ) z‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_q, ← norm_iteratedFDeriv_fderiv]
  have h : fderiv ℝ (⇑(qDeriv : H →L[ℝ] (H →L[ℝ] ℝ))) = fun _ => (qDeriv : H →L[ℝ] (H →L[ℝ] ℝ)) := by
    funext z; exact ContinuousLinearMap.fderiv _
  rw [h, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]

/--
@isnad1 id=le.1h3v.s8.d04a2221a12f from=translated src=- shape=5ce5aa56 vocab=7ff16fa6
-/
theorem norm_iteratedFDeriv_q_le (z : H) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (q : H → ℝ) z‖ ≤ (2 * Real.pi * ‖z‖ + 2 * Real.pi + 1) ^ i := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  rcases i with _ | _ | _ | j
  · omega
  · rw [pow_one]; refine (norm_iteratedFDeriv_q_one z).trans ?_; nlinarith
  · refine (norm_iteratedFDeriv_q_two z).trans ?_
    have h1 : (1 : ℝ) ≤ 2 * Real.pi * ‖z‖ + 2 * Real.pi + 1 := by nlinarith
    calc 2 * Real.pi ≤ 2 * Real.pi * ‖z‖ + 2 * Real.pi + 1 := by nlinarith
      _ ≤ (2 * Real.pi * ‖z‖ + 2 * Real.pi + 1) ^ (0 + 1 + 1) := by
          rw [show 0 + 1 + 1 = 2 from rfl]; nlinarith
  · rw [iteratedFDeriv_q_add_three]; positivity

/--
@isnad1 id=eq.0h2v.s7.9108ae11e812 from=translated src=- shape=3b49613c vocab=c0da5a60
-/
theorem norm_iteratedFDeriv_exp (i : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ i Real.exp t‖ = Real.exp t := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, Real.abs_exp]

def gauss (z : H) : ℝ := Real.exp (q z)

/--
@isnad1 id=eq.0h1v.s4.37f51ba0ac34 from=translated src=- shape=d8ebbe5f vocab=dec61ad0
-/
theorem gauss_eq_comp : (gauss : H → ℝ) = Real.exp ∘ q := rfl

/--
@isnad1 id=contdiff.0h2v.s5.dd2aca78b900 from=translated src=- shape=f7dafc7d vocab=96d09678
-/
theorem contDiff_gauss {n : WithTop ℕ∞} : ContDiff ℝ n (gauss : H → ℝ) :=
  Real.contDiff_exp.comp contDiff_q

/--
@isnad1 id=le.0h3v.s8.97005c9933b1 from=translated src=- shape=4d55f560 vocab=5e8caa03
-/
theorem norm_iteratedFDeriv_gauss_le (n : ℕ) (z : H) :
    ‖iteratedFDeriv ℝ n (gauss : H → ℝ) z‖
      ≤ n.factorial * Real.exp (q z) * (2 * Real.pi * ‖z‖ + 2 * Real.pi + 1) ^ n := by
  rw [gauss_eq_comp]
  exact norm_iteratedFDeriv_comp_le (N := (n : WithTop ℕ∞)) Real.contDiff_exp contDiff_q le_rfl z
    (fun i _ => (norm_iteratedFDeriv_exp i (q z)).le) (fun i hi _ => norm_iteratedFDeriv_q_le z i hi)

/--
@isnad1 id=le.1h2v.s7.a7034277d1fe from=translated src=- shape=66d75891 vocab=72e5a2bc
-/
theorem one_add_pow_mul_exp_le (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-Real.pi * r ^ 2) ≤ Real.exp ((m : ℝ) ^ 2 / (4 * Real.pi)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : (1 + r) ^ m ≤ Real.exp ((m : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) m
  have h2 : (m : ℝ) * r ≤ Real.pi * r ^ 2 + (m : ℝ) ^ 2 / (4 * Real.pi) := by
    have h3 : 0 ≤ Real.pi * (r - m / (2 * Real.pi)) ^ 2 := by positivity
    have h4 : Real.pi * (r - m / (2 * Real.pi)) ^ 2
        = Real.pi * r ^ 2 - m * r + (m : ℝ) ^ 2 / (4 * Real.pi) := by
      field_simp
      ring
    linarith
  calc (1 + r) ^ m * Real.exp (-Real.pi * r ^ 2)
      ≤ Real.exp ((m : ℝ) * r) * Real.exp (-Real.pi * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ) * r - Real.pi * r ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((m : ℝ) ^ 2 / (4 * Real.pi)) := Real.exp_le_exp.2 (by linarith)

/--
@isnad1 id=le.0h4v.s8.a8aabf84ead3 from=translated src=- shape=bc5e8bf7 vocab=375a5d94
-/
theorem decay_gauss (k n : ℕ) (z : H) :
    ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (gauss : H → ℝ) z‖
      ≤ n.factorial * (2 * Real.pi + 1) ^ n * Real.exp (((n + k : ℕ) : ℝ) ^ 2 / (4 * Real.pi)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have hD : 2 * Real.pi * r + 2 * Real.pi + 1 ≤ (2 * Real.pi + 1) * (1 + r) := by nlinarith
  have hDn : (2 * Real.pi * r + 2 * Real.pi + 1) ^ n ≤ (2 * Real.pi + 1) ^ n * (1 + r) ^ n := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hD n
  have hrk : r ^ k ≤ (1 + r) ^ k := pow_le_pow_left₀ hr0 (by linarith) k
  have key := one_add_pow_mul_exp_le (n + k) hr0
  calc r ^ k * ‖iteratedFDeriv ℝ n (gauss : H → ℝ) z‖
      ≤ r ^ k * (n.factorial * Real.exp (q z) * (2 * Real.pi * r + 2 * Real.pi + 1) ^ n) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_gauss_le n z) (by positivity)
    _ ≤ (1 + r) ^ k * (n.factorial * Real.exp (q z) * ((2 * Real.pi + 1) ^ n * (1 + r) ^ n)) := by
        gcongr
    _ = n.factorial * (2 * Real.pi + 1) ^ n * ((1 + r) ^ (n + k) * Real.exp (-Real.pi * r ^ 2)) := by
        simp only [q, pow_add]; ring
    _ ≤ n.factorial * (2 * Real.pi + 1) ^ n * Real.exp (((n + k : ℕ) : ℝ) ^ 2 / (4 * Real.pi)) :=
        mul_le_mul_of_nonneg_left key (by positivity)

variable (H) in

def gaussSchwartz : 𝓢(H, ℝ) where
  toFun := gauss
  smooth' := contDiff_gauss
  decay' k n := ⟨_, fun z => decay_gauss k n z⟩

end Gauss

section Coord

variable (F : Type) [Field F] [NumberField F]

abbrev RPl := {w : InfinitePlace F // IsReal w}

abbrev CPl := {w : InfinitePlace F // IsComplex w}

abbrev E2 := Fin 2 → mixedEmbedding.mixedSpace F

abbrev Idx := Fin 2 × (RPl F ⊕ (CPl F ⊕ CPl F))

abbrev Euc := EuclideanSpace ℝ (Idx F)

def coordFun (x : E2 F) : Idx F → ℝ := fun j =>
  match j with
  | (i, Sum.inl w) => (x i).1 w
  | (i, Sum.inr (Sum.inl w)) => ((x i).2 w).re
  | (i, Sum.inr (Sum.inr w)) => ((x i).2 w).im

def coordInv (f : Idx F → ℝ) : E2 F := fun i =>
  (fun w => f (i, Sum.inl w), fun w => ⟨f (i, Sum.inr (Sum.inl w)), f (i, Sum.inr (Sum.inr w))⟩)

def coordLinearEquiv : E2 F ≃ₗ[ℝ] (Idx F → ℝ) where
  toFun := coordFun F
  map_add' x y := by
    funext j
    rcases j with ⟨i, w | w | w⟩ <;> simp [coordFun]
  map_smul' c x := by
    funext j
    rcases j with ⟨i, w | w | w⟩ <;> simp [coordFun]
  invFun := coordInv F
  left_inv x := by
    funext i
    refine Prod.ext (funext fun w => rfl) (funext fun w => ?_)
    exact Complex.ext rfl rfl
  right_inv f := by
    funext j
    rcases j with ⟨i, w | w | w⟩ <;> rfl

def coordEquiv : E2 F ≃L[ℝ] Euc F :=
  ((coordLinearEquiv F).trans (EuclideanSpace.equiv (Idx F) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv

/--
@isnad1 id=eq.0h3v.s11.1e6d6ccc3416 from=translated src=- shape=b4da7abc vocab=d868eb97
-/
theorem coordEquiv_apply (x : E2 F) (j : Idx F) : coordEquiv F x j = coordFun F x j := rfl

/--
@isnad1 id=eq.0h2v.s11.66bd5e201f1a from=translated src=- shape=eefbde60 vocab=39364729
-/
theorem norm_coordEquiv_sq (x : E2 F) :
    ‖coordEquiv F x‖ ^ 2 = ∑ i : Fin 2, ((∑ w : RPl F, ((x i).1 w) ^ 2) + ∑ w : CPl F, ‖(x i).2 w‖ ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [coordEquiv_apply, coordFun]
  rw [← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

def cCLM (w : InfinitePlace F) (i : Fin 2) : E2 F →L[ℝ] ℂ :=
  if hw : IsReal w then
    Complex.ofRealCLM.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : RPl F => ℝ) ⟨w, hw⟩).comp
        ((ContinuousLinearMap.fst ℝ (RPl F → ℝ) (CPl F → ℂ)).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) i)))
  else
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : CPl F => ℂ) ⟨w, not_isReal_iff_isComplex.mp hw⟩).comp
      ((ContinuousLinearMap.snd ℝ (RPl F → ℝ) (CPl F → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) i))

/--
@isnad1 id=eq.1h4v.s10.2b1a471e0b47 from=translated src=- shape=f6bd951f vocab=e3b23893
-/
theorem cCLM_apply_of_isReal {w : InfinitePlace F} (hw : IsReal w) (i : Fin 2) (x : E2 F) :
    cCLM F w i x = (((x i).1 ⟨w, hw⟩ : ℝ) : ℂ) := by
  simp [cCLM, hw]

/--
@isnad1 id=eq.1h4v.s10.e6620e17afd4 from=translated src=- shape=3ad8cb4a vocab=8063a3ab
-/
theorem cCLM_apply_of_isComplex {w : InfinitePlace F} (hw : IsComplex w) (i : Fin 2) (x : E2 F) :
    cCLM F w i x = (x i).2 ⟨w, hw⟩ := by
  have hw' : ¬ IsReal w := not_isReal_iff_isComplex.mpr hw
  simp [cCLM, hw']

/--
@isnad1 id=eq.0h4v.s11.80a8e3f360a0 from=translated src=- shape=54d4b9e6 vocab=f111b55c
-/
theorem cCLM_ringEquiv (w : InfinitePlace F) (i : Fin 2) (y : Fin 2 → InfiniteAdeleRing F) :
    cCLM F w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i))
      = Completion.extensionEmbedding w (y i w) := by
  by_cases hw : IsReal w
  · rw [cCLM_apply_of_isReal F hw]
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact Completion.extensionEmbeddingOfIsReal_apply hw _
  · rw [cCLM_apply_of_isComplex F (not_isReal_iff_isComplex.mp hw)]
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

/--
@isnad1 id=eq.0h2v.s11.824698b57442 from=translated src=- shape=7947fdb7 vocab=65ce9b1a
-/
theorem norm_coordEquiv_ringEquiv_sq (y : Fin 2 → InfiniteAdeleRing F) :
    ‖coordEquiv F (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i))‖ ^ 2
      = ∑ i : Fin 2, ∑ w : InfinitePlace F, ‖y i w‖ ^ 2 := by
  rw [norm_coordEquiv_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NumberField.InfinitePlace.sum_eq_sum_add_sum (fun w : InfinitePlace F => ‖y i w‖ ^ 2)]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    rw [← (Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) (y i w.1),
      Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    rw [(Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) (y i w.1)]

end Coord

section Poly

variable (F : Type) [Field F] [NumberField F]

def evalPt (w : InfinitePlace F) (x : E2 F) : Fin 2 ⊕ Fin 2 → ℂ :=
  Sum.elim (fun i => cCLM F w i x) (fun i => conj (cCLM F w i x))

/--
@isnad1 id=hastempe.0h3v.s9.60f69bc42167 from=translated src=- shape=f0b0a7ff vocab=4dabf5e7
-/
theorem hasTemperateGrowth_evalPt (w : InfinitePlace F) (j : Fin 2 ⊕ Fin 2) :
    Function.HasTemperateGrowth (fun x : E2 F => evalPt F w x j) := by
  rcases j with i | i
  · simp only [evalPt, Sum.elim_inl]
    exact (cCLM F w i).hasTemperateGrowth
  · simp only [evalPt, Sum.elim_inr]
    exact (Complex.conjCLE.toContinuousLinearMap.comp (cCLM F w i)).hasTemperateGrowth

/--
@isnad1 id=hastempe.0h3v.s9.82a97d2b747e from=translated src=- shape=922556cf vocab=d3c7183f
-/
theorem hasTemperateGrowth_eval (w : InfinitePlace F) (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :
    Function.HasTemperateGrowth (fun x : E2 F => MvPolynomial.eval (evalPt F w x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hasTemperateGrowth_evalPt F w j)

def polyFn (P : (w : InfinitePlace F) → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (x : E2 F) : ℂ :=
  ∏ w, MvPolynomial.eval (evalPt F w x) (P w)

/--
@isnad1 id=hastempe.1h4v.s10.3c4edb296c98 from=translated src=- shape=5dd72fd5 vocab=db9e251b
-/
theorem hasTemperateGrowth_finset_prod {ι : Type*} (s : Finset ι) (f : ι → E2 F → ℂ)
    (hf : ∀ i ∈ s, Function.HasTemperateGrowth (f i)) :
    Function.HasTemperateGrowth (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Function.HasTemperateGrowth.const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/--
@isnad1 id=hastempe.0h2v.s9.dab42ddc2ffe from=translated src=- shape=db5160b2 vocab=203a23dd
-/
theorem hasTemperateGrowth_polyFn (P : (w : InfinitePlace F) → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :
    Function.HasTemperateGrowth (polyFn F P) :=
  hasTemperateGrowth_finset_prod F Finset.univ (fun w x => MvPolynomial.eval (evalPt F w x) (P w))
    fun w _ => hasTemperateGrowth_eval F w (P w)

end Poly

section Assembly

variable (F : Type) [Field F] [NumberField F]

def gaussE : 𝓢(E2 F, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (coordEquiv F) (gaussSchwartz (Euc F)))

/--
@isnad1 id=eq.0h2v.s11.ead57f386414 from=translated src=- shape=8378cc3b vocab=6c6b7901
-/
theorem gaussE_apply (x : E2 F) :
    gaussE F x = ((Real.exp (-Real.pi * ‖coordEquiv F x‖ ^ 2) : ℝ) : ℂ) := rfl

def jointS (P : (w : InfinitePlace F) → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) : 𝓢(E2 F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyFn F P) (gaussE F)

/--
@isnad1 id=eq.0h3v.s11.a23147de0ac9 from=translated src=- shape=8aad19ef vocab=ac26d82a
-/
theorem jointS_apply (P : (w : InfinitePlace F) → MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (x : E2 F) :
    jointS F P x = polyFn F P x * ((Real.exp (-Real.pi * ‖coordEquiv F x‖ ^ 2) : ℝ) : ℂ) := by
  rw [jointS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_polyFn F P), gaussE_apply,
    smul_eq_mul]

/--
@isnad1 id=ex.1h2v.s12.32e875092f80 from=translated src=- shape=64ee937d vocab=f6e4d47b
-/
theorem main (Φ : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
    (hΦ : ∀ w : InfinitePlace F, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ w y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) :
    ∃ g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ),
      ∀ y : Fin 2 → InfiniteAdeleRing F,
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φ w (fun i => y i w) := by
  choose P hP using hΦ
  refine ⟨jointS F P, fun y => ?_⟩
  rw [jointS_apply]
  simp_rw [hP]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  · unfold polyFn
    refine Finset.prod_congr rfl fun w _ => ?_
    congr 2
    funext j
    rcases j with i | i
    · simp only [evalPt, Sum.elim_inl, cCLM_ringEquiv]
    · simp only [evalPt, Sum.elim_inr, cCLM_ringEquiv]
  · rw [Complex.ofReal_exp]
    congr 1
    rw [norm_coordEquiv_ringEquiv_sq, Finset.sum_comm]
    push_cast
    rw [Finset.mul_sum]

end Assembly

end R4Joint

end

open NumberField NumberField.InfinitePlace
open scoped SchwartzMap

open scoped Classical in
/--
@isnad1 id=ex.1h2v.s12.32e875092f80 from=translated src=- shape=64ee937d vocab=f6e4d47b
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    (Φ : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
    (_hΦ : ∀ w : InfinitePlace F, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ w y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) :
    ∃ g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ),
      ∀ y : Fin 2 → InfiniteAdeleRing F,
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φ w (fun i => y i w) :=
  R4Joint.main F Φ _hΦ
