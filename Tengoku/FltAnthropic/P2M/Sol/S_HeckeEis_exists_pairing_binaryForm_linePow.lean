import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_pairing_binaryForm_linePow.lean`: wrote out 15 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 3 `p2m_open`, 9 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL linePow coe_linePow jFactor coe_smul_mul_jFactor binaryFormRepSL_linePow)
namespace PairingSol
open _root_.HeckeEis

open MvPolynomial Finset
open scoped MatrixGroups

variable (n : ℕ)

def ex (i : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 (n - i)

/--
@isnad1 id=eq.0h2v.s5.6cdafa30e9bb from=translated src=- shape=63341c4e vocab=dea80766
-/
@[scoped simp] theorem ex_apply_zero (i : ℕ) : ex n i 0 = i := by simp [ex]
/--
@isnad1 id=eq.0h2v.s6.8171d8ba4fba from=translated src=- shape=49a32e5b vocab=0f7a7d6d
-/
@[scoped simp] theorem ex_apply_one (i : ℕ) : ex n i 1 = n - i := by simp [ex]

/--
@isnad1 id=eq.1h3v.s4.6daa713f8437 from=translated src=- shape=97295d78 vocab=46b8865a
-/
theorem ex_inj {i j : ℕ} (h : ex n i = ex n j) : i = j := by
  have := congrArg (fun d => d 0) h
  simpa using this

/--
@isnad1 id=eq.1h2v.s7.b8e008f9a303 from=translated src=- shape=48540b90 vocab=6d4390c7
-/
theorem degree_ex {i : ℕ} (hi : i ≤ n) : (ex n i).degree = n := by
  rw [ex, (map_add Finsupp.degree), Finsupp.degree_single, Finsupp.degree_single]
  omega

theorem eq_ex_of_degree {d : Fin 2 →₀ ℕ} (hd : d.degree = n) : d = ex n (d 0) ∧ d 0 ≤ n := by
  have hsum : d 0 + d 1 = n := by
    rw [← hd, Finsupp.degree_eq_sum, Fin.sum_univ_two]
  refine ⟨?_, by omega⟩
  ext j
  fin_cases j
  · simp
  · simp; omega

def wt (i : ℕ) : ℂ := (-1) ^ (n - i) / (n.choose i : ℂ)

/--
@isnad1 id=ne.1h2v.s4.d71ce43aa884 from=translated src=- shape=8425c428 vocab=8ff24a01
-/
theorem choose_ne_zero {i : ℕ} (hi : i ≤ n) : (n.choose i : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.choose_pos hi).ne'

/--
@isnad1 id=ne.1h2v.s4.fa81a08a9a85 from=translated src=- shape=24220606 vocab=3ba20bff
-/
theorem wt_ne_zero {i : ℕ} (hi : i ≤ n) : wt n i ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (by norm_num)) (choose_ne_zero n hi)

/--
@isnad1 id=eq.1h2v.s5.3951cc017862 from=translated src=- shape=5cc442f3 vocab=62a60221
-/
theorem wt_mul_choose {i : ℕ} (hi : i ≤ n) : wt n i * (n.choose i : ℂ) = (-1) ^ (n - i) := by
  rw [wt, div_mul_cancel₀ _ (choose_ne_zero n hi)]

def rawPairing : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] MvPolynomial (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun P Q => ∑ i ∈ range (n + 1), wt n i * coeff (ex n i) P * coeff (ex n (n - i)) Q)
    (fun P P' Q => by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [coeff_add]; ring)
    (fun c P Q => by
      rw [smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by rw [coeff_smul, smul_eq_mul]; ring)
    (fun P Q Q' => by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [coeff_add]; ring)
    (fun c P Q => by
      rw [smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by rw [coeff_smul, smul_eq_mul]; ring)

def pairing : ↥(BinaryForm ℂ n) →ₗ[ℂ] ↥(BinaryForm ℂ n) →ₗ[ℂ] ℂ :=
  (rawPairing n).compl₁₂ (BinaryForm ℂ n).subtype (BinaryForm ℂ n).subtype

/--
@isnad1 id=eq.0h3v.s12.9643bd4bd115 from=translated src=- shape=42819e70 vocab=41250f62
-/
theorem pairing_apply (P Q : ↥(BinaryForm ℂ n)) :
    pairing n P Q = ∑ i ∈ range (n + 1),
      wt n i * coeff (ex n i) (P : MvPolynomial (Fin 2) ℂ) * coeff (ex n (n - i)) (Q : MvPolynomial (Fin 2) ℂ) := rfl

/--
@isnad1 id=eq.0h2v.s9.b3148a2b1d7c from=translated src=- shape=c39b2e7f vocab=615286f2
-/
theorem linePow_expand (τ : ℂ) :
    ((C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ)) ^ n
      = ∑ m ∈ range (n + 1), monomial (ex n m) ((n.choose m : ℂ) * τ ^ m) := by
  rw [(Commute.all (C τ * X 0) (X 1 : MvPolynomial (Fin 2) ℂ)).add_pow]
  refine sum_congr rfl fun m hm => ?_
  rw [mul_pow, ← map_pow, X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, ex]
  rw [mul_comm (monomial _ _) ((n.choose m : MvPolynomial (Fin 2) ℂ)), ← C_eq_coe_nat, C_mul_monomial]
  simp only [mul_one]

/--
@isnad1 id=eq.1h3v.s7.9335bf251600 from=translated src=- shape=afef3a98 vocab=b7085563
-/
theorem coeff_linePow {i : ℕ} (hi : i ≤ n) (τ : ℂ) :
    coeff (ex n i) ((linePow n τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = (n.choose i : ℂ) * τ ^ i := by
  rw [coe_linePow, linePow_expand, coeff_sum]
  rw [sum_eq_single i]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro m _ hmi
    rw [coeff_monomial, ite_eq_right (fun h => hmi (ex_inj n h))]
  · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hi)) h

/--
@isnad1 id=eq.0h3v.s12.9c4d1601ceb9 from=translated src=- shape=c2e2516a vocab=4a3ebb0c
-/
theorem pairing_linePow (τ σ : ℂ) : pairing n (linePow n τ) (linePow n σ) = (τ - σ) ^ n := by
  rw [pairing_apply, sub_eq_add_neg, (Commute.all τ (-σ)).add_pow]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [coeff_linePow n hi', coeff_linePow n (Nat.sub_le n i), Nat.choose_symm hi', neg_pow σ]
  have := wt_mul_choose n hi'

  calc wt n i * ((n.choose i : ℂ) * τ ^ i) * ((n.choose i : ℂ) * σ ^ (n - i))
        = (wt n i * (n.choose i : ℂ)) * τ ^ i * σ ^ (n - i) * (n.choose i : ℂ) := by ring
    _ = τ ^ i * ((-1) ^ (n - i) * σ ^ (n - i)) * (n.choose i : ℂ) := by rw [this]; ring

/--
@isnad1 id=eq.0h3v.s13.d19fb077c63a from=translated src=- shape=1b9bbaf8 vocab=c7e7b0b9
-/
theorem pairing_swap (P Q : ↥(BinaryForm ℂ n)) : pairing n Q P = (-1) ^ n * pairing n P Q := by
  rw [pairing_apply, pairing_apply, mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega, Nat.sub_sub_self hi']
  have hw : wt n (n - i) = (-1) ^ n * wt n i := by
    rw [wt, wt, Nat.sub_sub_self hi', Nat.choose_symm hi']
    rw [mul_div_assoc', ← pow_add, show n + (n - i) = 2 * (n - i) + i by omega, pow_add, pow_mul]
    norm_num
  rw [hw]; ring

/--
@isnad1 id=mem.1h2v.s8.22e2a8dac6c2 from=translated src=- shape=408a8150 vocab=8c6d7b0b
-/
theorem monomial_ex_mem {i : ℕ} (hi : i ≤ n) : monomial (ex n i) (1 : ℂ) ∈ BinaryForm ℂ n :=
  (mem_homogeneousSubmodule n _).mpr (isHomogeneous_monomial _ (degree_ex n hi))

/--
@isnad1 id=eq.1h3v.s12.6c337f7a1eb8 from=translated src=- shape=ee52d798 vocab=b3bf694a
-/
theorem pairing_monomial (P : ↥(BinaryForm ℂ n)) {i : ℕ} (hi : i ≤ n) :
    pairing n P ⟨monomial (ex n (n - i)) 1, monomial_ex_mem n (Nat.sub_le n i)⟩
      = wt n i * coeff (ex n i) (P : MvPolynomial (Fin 2) ℂ) := by
  rw [pairing_apply, sum_eq_single i]
  · simp
  · intro j hj hji
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [Subtype.coe_mk, coeff_monomial, ite_eq_right, mul_zero]
    intro h
    have := ex_inj n h
    omega
  · intro h; exact absurd (mem_range.mpr (Nat.lt_succ_of_le hi)) h

theorem eq_zero_of_pairing_eq_zero (P : ↥(BinaryForm ℂ n)) (h : ∀ Q, pairing n P Q = 0) : P = 0 := by
  have hc : ∀ i ≤ n, coeff (ex n i) (P : MvPolynomial (Fin 2) ℂ) = 0 := by
    intro i hi
    have := h ⟨monomial (ex n (n - i)) 1, monomial_ex_mem n (Nat.sub_le n i)⟩
    rw [pairing_monomial n P hi] at this
    exact (mul_eq_zero.mp this).resolve_left (wt_ne_zero n hi)
  apply Subtype.ext
  show (P : MvPolynomial (Fin 2) ℂ) = 0
  ext d
  rw [coeff_zero]
  by_contra hd
  have hP : (P : MvPolynomial (Fin 2) ℂ).IsHomogeneous n := (mem_homogeneousSubmodule n _).mp P.2
  have hdeg : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP hd
  obtain ⟨hd', hle⟩ := eq_ex_of_degree n hdeg
  rw [hd'] at hd
  exact hd (hc _ hle)

end HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis

end
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL linePow coe_linePow jFactor coe_smul_mul_jFactor binaryFormRepSL_linePow)
namespace PairingSol
open _root_.HeckeEis

open MvPolynomial Finset UpperHalfPlane
open scoped MatrixGroups

variable (n : ℕ)

/--
@isnad1 id=eq.0h1v.s8.22f991ebcb94 from=translated src=- shape=b760eac4 vocab=e383e1bc
-/
theorem det_coe_complex (g : SL(2, ℤ)) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)
      - ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/--
@isnad1 id=eq.0h3v.s8.2200cfe9f34f from=translated src=- shape=60377764 vocab=c0471366
-/
theorem jFactor_mul_jFactor_mul_sub (g : SL(2, ℤ)) (τ σ : ℍ) :
    jFactor g τ * jFactor g σ * (((g • τ : ℍ) : ℂ) - ((g • σ : ℍ) : ℂ)) = (τ : ℂ) - (σ : ℂ) := by
  have hτ := coe_smul_mul_jFactor g τ
  have hσ := coe_smul_mul_jFactor g σ
  have hdet := det_coe_complex g
  have e : jFactor g τ * jFactor g σ * (((g • τ : ℍ) : ℂ) - ((g • σ : ℍ) : ℂ))
      = jFactor g σ * (((g • τ : ℍ) : ℂ) * jFactor g τ) - jFactor g τ * (((g • σ : ℍ) : ℂ) * jFactor g σ) := by ring
  rw [e, hτ, hσ, jFactor, jFactor]
  linear_combination ((τ : ℂ) - (σ : ℂ)) * hdet

/--
@isnad1 id=eq.0h4v.s14.21fa45577734 from=translated src=- shape=214886d4 vocab=6af4bed2
-/
theorem pairing_rep_linePow (g : SL(2, ℤ)) (τ σ : ℍ) :
    pairing n (binaryFormRepSL ℂ n g (linePow n (τ : ℂ))) (binaryFormRepSL ℂ n g (linePow n (σ : ℂ)))
      = pairing n (linePow n (τ : ℂ)) (linePow n (σ : ℂ)) := by
  rw [binaryFormRepSL_linePow, binaryFormRepSL_linePow, LinearMap.map_smul₂, LinearMap.map_smul, pairing_linePow,
    pairing_linePow, smul_eq_mul, smul_eq_mul, ← mul_pow, ← mul_pow, ← mul_assoc, jFactor_mul_jFactor_mul_sub]

def node (j : Fin (n + 1)) : ℍ := ⟨(j : ℂ) + Complex.I, by simp⟩

/--
@isnad1 id=eq.0h2v.s5.6095aa8fe3ef from=translated src=- shape=074f117e vocab=e22bf76f
-/
@[scoped simp] theorem coe_node (j : Fin (n + 1)) : ((node n j : ℍ) : ℂ) = (j : ℂ) + Complex.I := rfl

/--
@isnad1 id=injectiv.0h1v.s5.f168080e769f from=translated src=- shape=4ed545fd vocab=84109833
-/
theorem node_injective : Function.Injective (fun j : Fin (n + 1) => ((node n j : ℍ) : ℂ)) := by
  intro j j' h
  simp only [coe_node, add_left_inj, Nat.cast_inj] at h
  exact Fin.ext (by exact_mod_cast h)

def lineSpan : Submodule ℂ ↥(BinaryForm ℂ n) :=
  Submodule.span ℂ (Set.range fun τ : ℍ => linePow n (τ : ℂ))

/--
@isnad1 id=mem.0h2v.s10.b4cbb4f3db81 from=translated src=- shape=7fdda805 vocab=5f12116b
-/
theorem linePow_mem_lineSpan (τ : ℍ) : linePow n (τ : ℂ) ∈ lineSpan n := Submodule.subset_span ⟨τ, rfl⟩

/--
@isnad1 id=mem.1h2v.s10.b6b98bc5431d from=translated src=- shape=327ee120 vocab=af61c17e
-/
theorem monomial_mem_lineSpan {k : ℕ} (hk : k ≤ n) :
    (⟨monomial (ex n k) 1, monomial_ex_mem n hk⟩ : ↥(BinaryForm ℂ n)) ∈ lineSpan n := by
  classical

  set v : Fin (n + 1) → ℂ := fun j => ((node n j : ℍ) : ℂ) with hv
  have hvs : Set.InjOn v (Finset.univ : Finset (Fin (n + 1))) := fun a _ b _ h => node_injective n h
  set L : Fin (n + 1) → Polynomial ℂ := fun j => Lagrange.basis Finset.univ v j with hL
  have hdeg : ∀ j, (L j).natDegree < n + 1 := by
    intro j
    rw [hL, Lagrange.natDegree_basis hvs (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega

  have heval : ∀ j m : Fin (n + 1), ∑ i : Fin (n + 1), (L j).coeff i * v m ^ (i : ℕ) = if j = m then 1 else 0 := by
    intro j m
    rw [Fin.sum_univ_eq_sum_range (fun i => (L j).coeff i * v m ^ i) (n + 1),
      ← Polynomial.eval_eq_sum_range' (hdeg j)]
    split_ifs with h
    · subst h; exact Lagrange.eval_basis_self hvs (Finset.mem_univ j)
    · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ m)

  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun j i => (L j).coeff i with hA
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun i m => v m ^ (i : ℕ) with hV
  have hAV : A * V = 1 := by
    ext j m
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact heval j m
  have hVA : V * A = 1 := mul_eq_one_comm.mp hAV
  have hcol : ∀ i k' : Fin (n + 1), ∑ j : Fin (n + 1), v j ^ (i : ℕ) * (L j).coeff k' = if i = k' then 1 else 0 := by
    intro i k'
    have := congrFun (congrFun hVA i) k'
    rwa [Matrix.mul_apply, Matrix.one_apply] at this

  set kk : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩ with hkk
  have hmem : (∑ j : Fin (n + 1), (L j).coeff k • linePow n (v j)) ∈ lineSpan n :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (linePow_mem_lineSpan n (node n j))

  have hcomb : ((∑ j : Fin (n + 1), (L j).coeff k • linePow n (v j) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = C ((n.choose k : ℂ)) * monomial (ex n k) 1 := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, coe_linePow, linePow_expand, smul_sum, smul_monomial, smul_eq_mul]
    rw [Finset.sum_comm]

    rw [← Fin.sum_univ_eq_sum_range (fun m => ∑ j : Fin (n + 1), monomial (ex n m) ((L j).coeff k * ((n.choose m : ℂ) * v j ^ m))) (n + 1)]
    have inner : ∀ m : Fin (n + 1), ∑ j : Fin (n + 1), monomial (ex n m) ((L j).coeff k * ((n.choose (m : ℕ) : ℂ) * v j ^ (m : ℕ)))
        = monomial (ex n m) ((n.choose (m : ℕ) : ℂ) * (if m = kk then 1 else 0)) := by
      intro m
      rw [← map_sum, ← hcol m kk]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [inner]
    rw [Finset.sum_eq_single kk]
    · rw [ite_eq_left rfl, mul_one, C_mul_monomial, mul_one]
    · intro m _ hm; rw [ite_eq_right hm, mul_zero, monomial_zero]
    · intro h; exact absurd (Finset.mem_univ kk) h

  have hne : (n.choose k : ℂ) ≠ 0 := choose_ne_zero n hk
  have : (⟨monomial (ex n k) 1, monomial_ex_mem n hk⟩ : ↥(BinaryForm ℂ n))
      = (n.choose k : ℂ)⁻¹ • ∑ j : Fin (n + 1), (L j).coeff k • linePow n (v j) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, hcomb, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

/--
@isnad1 id=eq.0h1v.s9.dd40a62c7e48 from=translated src=- shape=e846771f vocab=8e586dac
-/
theorem lineSpan_eq_top : lineSpan n = ⊤ := by
  classical

  have hmono : ∀ d : Fin 2 →₀ ℕ, d.degree = n →
      (monomial d (1 : ℂ)) ∈ (lineSpan n).map (BinaryForm ℂ n).subtype := by
    intro d hd
    obtain ⟨hd', hle⟩ := eq_ex_of_degree n hd
    refine ⟨⟨monomial (ex n (d 0)) 1, monomial_ex_mem n hle⟩, monomial_mem_lineSpan n hle, ?_⟩
    show monomial (ex n (d 0)) (1 : ℂ) = monomial d 1
    rw [← hd']

  have hle : (BinaryForm ℂ n : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) ≤ (lineSpan n).map (BinaryForm ℂ n).subtype := by
    intro φ hφ
    have hφ' : φ ∈ AddMonoidAlgebra.supported ℂ ℂ {d : Fin 2 →₀ ℕ | d.degree = n} := by
      rwa [← MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.supported_eq_span_single] at hφ'
    refine (Submodule.span_le.mpr ?_) hφ'
    rintro _ ⟨d, hd, rfl⟩
    exact hmono d hd
  rw [eq_top_iff]
  rintro P -
  obtain ⟨Q, hQ, hQP⟩ := hle P.2
  have : P = Q := Subtype.ext hQP.symm
  rw [this]; exact hQ

end HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol

end
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binaryFormRepSL linePow coe_linePow jFactor coe_smul_mul_jFactor binaryFormRepSL_linePow)
namespace PairingSol
open _root_.HeckeEis

open MvPolynomial Finset UpperHalfPlane
open scoped MatrixGroups

variable (n : ℕ)

/--
@isnad1 id=eq.0h4v.s14.d49dbf464c1b from=translated src=- shape=74b95e67 vocab=ef977467
-/
theorem pairing_rep (g : SL(2, ℤ)) (P Q : ↥(BinaryForm ℂ n)) :
    pairing n (binaryFormRepSL ℂ n g P) (binaryFormRepSL ℂ n g Q) = pairing n P Q := by
  set B₁ : ↥(BinaryForm ℂ n) →ₗ[ℂ] ↥(BinaryForm ℂ n) →ₗ[ℂ] ℂ :=
    (pairing n).compl₁₂ (binaryFormRepSL ℂ n g) (binaryFormRepSL ℂ n g) with hB₁
  have hspan : Submodule.span ℂ (Set.range fun τ : ℍ => linePow n (τ : ℂ)) = ⊤ := lineSpan_eq_top n
  have h1 : ∀ τ : ℍ, B₁ (linePow n (τ : ℂ)) = pairing n (linePow n (τ : ℂ)) := by
    intro τ
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨σ, rfl⟩
    exact pairing_rep_linePow n g τ σ
  have h2 : B₁ = pairing n := by
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨τ, rfl⟩
    exact h1 τ
  have := congrFun (congrArg DFunLike.coe (LinearMap.congr_fun h2 P)) Q
  exact this

end HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol

end
open scoped _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis _root_.P2MW.S_HeckeEis_exists_pairing_binaryForm_linePow.HeckeEis.PairingSol

open scoped MatrixGroups in
/--
@isnad1 id=ex.0h1v.s15.dfeed910b395 from=translated src=- shape=c5d415a5 vocab=4c0f6fc2
-/
theorem solution (n : ℕ) :
    ∃ B : ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ↥(HeckeEis.BinaryForm ℂ n) →ₗ[ℂ] ℂ,
      (∀ (g : SL(2, ℤ)) (P Q : ↥(HeckeEis.BinaryForm ℂ n)),
          B (HeckeEis.binaryFormRepSL ℂ n g P) (HeckeEis.binaryFormRepSL ℂ n g Q) = B P Q) ∧
      (∀ P Q : ↥(HeckeEis.BinaryForm ℂ n), B Q P = (-1) ^ n * B P Q) ∧
      (∀ P : ↥(HeckeEis.BinaryForm ℂ n), (∀ Q : ↥(HeckeEis.BinaryForm ℂ n), B P Q = 0) → P = 0) ∧
      (∀ τ σ : ℂ, B (HeckeEis.linePow n τ) (HeckeEis.linePow n σ) = (τ - σ) ^ n) :=
  ⟨HeckeEis.PairingSol.pairing n, HeckeEis.PairingSol.pairing_rep n, HeckeEis.PairingSol.pairing_swap n,
    HeckeEis.PairingSol.eq_zero_of_pairing_eq_zero n, HeckeEis.PairingSol.pairing_linePow n⟩

