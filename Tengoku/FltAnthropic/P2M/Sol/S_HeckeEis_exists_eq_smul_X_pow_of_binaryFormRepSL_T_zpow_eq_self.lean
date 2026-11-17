import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binarySubst_X binaryFormRepSL)
open _root_.HeckeEis

open MvPolynomial Polynomial
open scoped MatrixGroups

namespace UnipotentFixedAux

variable {R : Type*} [CommRing R] {n : ℕ}

variable (n) in

noncomputable def expo (j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 (n - j) + Finsupp.single 1 j

/--
@isnad1 id=injon.0h1v.s5.a08ce940f438 from=translated src=- shape=696d3529 vocab=0c465d73
-/
theorem expo_injOn : Set.InjOn (expo n) (Finset.range (n + 1) : Set ℕ) := by
  intro i _ j _ h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  simpa [expo, Finsupp.single_apply] using this

/--
@isnad1 id=iff.0h2v.s7.1d830ffd0387 from=translated src=- shape=f4d6a2d0 vocab=c33a86c9
-/
theorem degree_eq_iff (d : Fin 2 →₀ ℕ) : d.degree = n ↔ ∃ j ∈ Finset.range (n + 1), expo n j = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  constructor
  · intro h
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i <;> simp [expo, Finsupp.single_apply] <;> omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    simp [expo, Finsupp.single_apply]
    omega

theorem eq_sum_range {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    P = ∑ j ∈ Finset.range (n + 1), MvPolynomial.monomial (expo n j) (MvPolynomial.coeff (expo n j) P) := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · obtain ⟨j, hj, rfl⟩ := (degree_eq_iff d).mp hd
    rw [Finset.sum_eq_single j (fun i hi hne => ite_eq_right fun h => hne (expo_injOn hi hj h)) (fun h => (h hj).elim),
      ite_eq_left rfl]
  · rw [Finset.sum_eq_zero fun i hi => ite_eq_right fun h => hd ((degree_eq_iff d).mpr ⟨i, hi, h⟩)]
    exact ((MvPolynomial.mem_homogeneousSubmodule n P).mp hP).coeff_eq_zero hd

noncomputable def dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X] := MvPolynomial.aeval ![1, Polynomial.X]

/--
@isnad1 id=eq.0h4v.s9.96e2e435c6a6 from=translated src=- shape=ad334887 vocab=326c6d95
-/
theorem dehom_monomial (j : ℕ) (c : R) :
    dehom (MvPolynomial.monomial (expo n j) c) = Polynomial.C c * Polynomial.X ^ j := by
  rw [expo, MvPolynomial.monomial_eq, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  simp [dehom, Polynomial.C_mul']

/--
@isnad1 id=eq.1h3v.s9.5f8876b056cb from=translated src=- shape=0e5ca05e vocab=876710ee
-/
theorem dehom_eq_sum {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    dehom P = ∑ j ∈ Finset.range (n + 1), Polynomial.C (MvPolynomial.coeff (expo n j) P) * Polynomial.X ^ j := by
  conv_lhs => rw [eq_sum_range hP, map_sum]
  exact Finset.sum_congr rfl fun j _ => dehom_monomial j _

/--
@isnad1 id=eq.1h4v.s9.f5e3a3a89d3a from=translated src=- shape=96d9aa2e vocab=916c0856
-/
theorem coeff_dehom {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) (j : ℕ) :
    (dehom P).coeff j = if j ∈ Finset.range (n + 1) then MvPolynomial.coeff (expo n j) P else 0 := by
  rw [dehom_eq_sum hP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single j (fun i _ hne => ite_eq_right hne.symm) (fun h' => (h' h).elim), ite_eq_left rfl]
  · exact Finset.sum_eq_zero fun i hi => ite_eq_right fun h' => h (by rw [h']; exact hi)

/--
@isnad1 id=le.1h3v.s8.a730ea2dd072 from=translated src=- shape=ffce0928 vocab=3d5f14d7
-/
theorem natDegree_dehom_le {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : (dehom P).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dehom hP, ite_eq_right]
  rw [Finset.mem_range]; omega

/--
@isnad1 id=eq.0h3v.s10.514cabc8bd9a from=translated src=- shape=2a1f86b6 vocab=7b00731d
-/
theorem dehom_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) R) :
    dehom (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = (dehom P).comp (Polynomial.X + Polynomial.C (h : R)) := by

  revert P
  refine fun P => ?_
  have key : (dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X]).comp (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      = (Polynomial.aeval (Polynomial.X + Polynomial.C (h : R)) : R[X] →ₐ[R] R[X]).comp dehom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, binarySubst_X, ModularGroup.coe_T_zpow]
    fin_cases i <;> simp [dehom, Fin.sum_univ_two, add_comm]
  have := congrArg (fun φ => φ P) key
  simpa [Polynomial.aeval_X, Polynomial.comp_eq_aeval] using this

theorem eq_C_of_comp_X_add_C_eq [IsDomain R] {q : R[X]} (hq : q.natDegree ≤ n) {h : R} (hh : h ≠ 0)
    (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (hinv : q.comp (Polynomial.X + Polynomial.C h) = q) :
    q = Polynomial.C (q.eval 0) := by
  classical

  have hper : ∀ k : ℕ, q.eval ((k : R) * h) = q.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := congrArg (fun r => Polynomial.eval ((k : R) * h) r) hinv
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
      rw [← ih, ← this]
      congr 1; push_cast; ring

  set q' : R[X] := q - Polynomial.C (q.eval 0) with hq'
  have hdeg : q'.natDegree ≤ n := (Polynomial.natDegree_sub_le _ _).trans (by simpa using hq)
  have hroots : ∀ k ∈ Finset.range (n + 1), q'.eval ((k : R) * h) = 0 := fun k _ => by
    simp [hq', hper k]
  have hinj : Set.InjOn (fun k : ℕ => (k : R) * h) (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have : ((i : R) - (j : R)) * h = 0 := by rw [sub_mul]; exact sub_eq_zero.mpr hij
    rcases mul_eq_zero.mp this with h0 | h0
    ·
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := hn (j - i) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination -h0
      · have := hn (i - j) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination h0
    · exact (hh h0).elim
  have hzero : q' = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q' ((Finset.range (n + 1)).image fun k : ℕ => (k : R) * h)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact hroots k hk
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]; omega
  rw [hq', sub_eq_zero] at hzero
  exact hzero

end UnipotentFixedAux

open UnipotentFixedAux in

/--
@isnad1 id=ex.3h4v.s12.ba1f8d2354f2 from=translated src=- shape=53eb5c96 vocab=a65d26bc
-/
theorem SolMain.A2 {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) {h : ℤ}
    (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(BinaryForm R n))
    (hP : binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n := by
  classical
  have hsub : binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) = P := by
    simpa using congrArg Subtype.val hP
  have hq : (dehom (P : MvPolynomial (Fin 2) R)).comp (Polynomial.X + Polynomial.C (h : R)) = dehom (P : MvPolynomial (Fin 2) R) := by
    rw [← dehom_binarySubst_T_zpow, hsub]
  have hconst := eq_C_of_comp_X_add_C_eq (natDegree_dehom_le P.2) hh hn hq
  refine ⟨MvPolynomial.coeff (expo n 0) (P : MvPolynomial (Fin 2) R), ?_⟩

  have hcoeff : ∀ j ∈ Finset.range (n + 1), j ≠ 0 → MvPolynomial.coeff (expo n j) (P : MvPolynomial (Fin 2) R) = 0 := by
    intro j hj hj0
    have := congrArg (fun r : R[X] => r.coeff j) hconst
    simp only [Polynomial.coeff_C, ite_eq_right hj0] at this
    rwa [coeff_dehom P.2, ite_eq_left hj] at this
  conv_lhs => rw [eq_sum_range P.2]
  rw [Finset.sum_eq_single 0 (fun j hj hj0 => by rw [hcoeff j hj hj0, map_zero]) (fun h0 => (h0 (by simp)).elim)]
  rw [expo, Nat.sub_zero, Finsupp.single_zero, add_zero, ← MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.smul_eq_C_mul]

end HeckeEis

open scoped MatrixGroups in
/--
@isnad1 id=ex.3h4v.s12.ba1f8d2354f2 from=translated src=- shape=53eb5c96 vocab=a65d26bc
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(HeckeEis.BinaryForm R n))
    (hP : HeckeEis.binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n :=
  HeckeEis.SolMain.A2 n hh hn P hP

