import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero

set_option autoImplicit false

namespace ATHRVan

open MvPolynomial HeckeEis Finset

section Monomials

variable (K : Type*) [Field K]

noncomputable def e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

/--
@isnad1 id=eq.0h2v.s5.120b5a13889a from=translated src=- shape=d13958d8 vocab=faabfa03
-/
@[scoped simp] theorem e_zero (i j : ℕ) : e i j 0 = i := by simp [e]

/--
@isnad1 id=eq.0h2v.s5.51233e90d947 from=translated src=- shape=63341c4e vocab=faabfa03
-/
@[scoped simp] theorem e_one (i j : ℕ) : e i j 1 = j := by simp [e]

/--
@isnad1 id=iff.0h4v.s5.521347e2d525 from=translated src=- shape=71ada6db vocab=e4c7b69d
-/
theorem e_eq_iff {i j i' j' : ℕ} : e i j = e i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
      by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eq_e (d : Fin 2 →₀ ℕ) : d = e (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp

/--
@isnad1 id=eq.0h2v.s7.4cd45725664e from=translated src=- shape=75677755 vocab=b0010ca5
-/
theorem degree_e (i j : ℕ) : Finsupp.degree (e i j) = i + j := by
  rw [e, map_add, Finsupp.degree_single, Finsupp.degree_single]

/--
@isnad1 id=eq.0h4v.s9.f79e4c60be4f from=translated src=- shape=a5c04ca7 vocab=9c9ed9b1
-/
theorem monomial_e (i j : ℕ) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) = C c * X 0 ^ i * X 1 ^ j := by
  rw [e, mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, C_mul_monomial, one_mul, mul_one]

/--
@isnad1 id=ishomoge.0h4v.s8.cec0bd40d625 from=translated src=- shape=9cee0aae vocab=7495d319
-/
theorem isHomogeneous_monomial_e (i j : ℕ) (c : K) :
    ((monomial (e i j) c : MvPolynomial (Fin 2) K)).IsHomogeneous (i + j) :=
  isHomogeneous_monomial _ (degree_e i j)

/--
@isnad1 id=eq.2h4v.s7.c35b95e05bb2 from=translated src=- shape=4b33e789 vocab=a848fe9e
-/
theorem deg_two {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) {d : Fin 2 →₀ ℕ}
    (hd : coeff d F ≠ 0) : d 0 + d 1 = n := by
  have hdeg := hF hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hdeg
  simpa only [Pi.one_apply, smul_eq_mul, mul_one, Fin.sum_univ_two] using hdeg

theorem eq_sum_monomial {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    F = ∑ i ∈ range (n + 1), monomial (e i (n - i)) (coeff (e i (n - i)) F) := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : coeff d F = 0
  · rw [hd]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · rw [← h] at hd
      exact hd
    · rfl
  · have hdeg := deg_two K hF hd
    rw [Finset.sum_eq_single (d 0)]
    · have h : e (d 0) (n - d 0) = d := by
        conv_rhs => rw [eq_e d]
        rw [e_eq_iff]
        exact ⟨rfl, by omega⟩
      rw [ite_eq_left h, h]
    · intro i _ hne
      rw [ite_eq_right]
      intro h
      apply hne
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simpa using this
    · intro h
      exfalso
      simp only [mem_range] at h
      omega

end Monomials

section Eval

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

noncomputable def ev (F : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) : K :=
  eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F

/--
@isnad1 id=eq.0h5v.s7.6ee8ae173b1f from=translated src=- shape=36157e1a vocab=1f62c135
-/
theorem ev_add (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F + G) v = ev p K F v + ev p K G v := by
  simp [ev]

/--
@isnad1 id=eq.0h5v.s7.6010e5240a3c from=translated src=- shape=36157e1a vocab=6661135c
-/
theorem ev_mul (F G : MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (F * G) v = ev p K F v * ev p K G v := by
  simp [ev]

/--
@isnad1 id=eq.0h6v.s7.ba57476012e0 from=translated src=- shape=4dd111ab vocab=ac0f6684
-/
theorem ev_sum {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin 2) K) (v : Fin 2 → ZMod p) :
    ev p K (∑ i ∈ s, F i) v = ∑ i ∈ s, ev p K (F i) v := by
  simp [ev, map_sum]

/--
@isnad1 id=eq.0h6v.s9.c8427521a257 from=translated src=- shape=1750b5a0 vocab=a617087b
-/
theorem ev_monomial (i j : ℕ) (c : K) (v : Fin 2 → ZMod p) :
    ev p K (monomial (e i j) c) v =
      c * (ZMod.castHom (dvd_refl p) K (v 0)) ^ i * (ZMod.castHom (dvd_refl p) K (v 1)) ^ j := by
  rw [monomial_e]
  simp [ev]

/--
@isnad1 id=eq.0h3v.s7.a251693bf258 from=translated src=- shape=46364875 vocab=dffe15ed
-/
theorem castHom_pow_card (x : ZMod p) :
    (ZMod.castHom (dvd_refl p) K x) ^ p = ZMod.castHom (dvd_refl p) K x := by
  rw [← map_pow, ZMod.pow_card]

noncomputable def theta : MvPolynomial (Fin 2) K := X 0 ^ p * X 1 - X 0 * X 1 ^ p

/--
@isnad1 id=eq.0h3v.s5.71235bf83d7e from=translated src=- shape=786c0453 vocab=1016a572
-/
theorem ev_theta (v : Fin 2 → ZMod p) : ev p K (theta p K) v = 0 := by
  simp only [theta, ev, map_sub, map_mul, map_pow, eval_X, castHom_pow_card]
  ring

/--
@isnad1 id=eq.3h5v.s8.ddbf19bb43f1 from=translated src=- shape=841140ca vocab=511473df
-/
theorem coeffs_eq_zero_of_ev {n : ℕ} (c : ℕ → K)
    (hsupp : ∀ i ∈ range (n + 1), c i ≠ 0 → i = n ∨ i < p)
    (hev : ∀ x y : ZMod p, ∑ i ∈ range (n + 1),
      c i * (ZMod.castHom (dvd_refl p) K x) ^ i * (ZMod.castHom (dvd_refl p) K y) ^ (n - i) = 0) :
    ∀ i ∈ range (n + 1), c i = 0 := by
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι

  have hcn : c n = 0 := by
    have h := hev 1 0
    rw [Finset.sum_eq_single n] at h
    · simpa using h
    · intro i hi hne
      have : n - i ≠ 0 := by
        simp only [mem_range] at hi
        omega
      simp [map_zero, zero_pow this]
    · simp

  set N := min n p with hN
  set q : Polynomial K := ∑ i : Fin N, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) with hq
  have hqdeg : q.degree < N := Polynomial.degree_sum_fin_lt _
  have hvanish : ∀ i ∈ range (n + 1), N ≤ i → c i = 0 := by
    intro i hi hNi
    by_cases hin : i = n
    · rw [hin]
      exact hcn
    by_contra hne
    rcases hsupp i hi hne with h | h
    · exact hin h
    · simp only [mem_range] at hi
      omega
  have hqeval : ∀ x : ZMod p, q.eval (ι x) = 0 := by
    intro x
    have h := hev x 1
    simp only [map_one, one_pow, mul_one] at h
    rw [hq, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Fin.sum_univ_eq_sum_range (fun i => c i * ι x ^ i) N]
    have h2 : ∑ i ∈ range N, c i * ι x ^ i = ∑ i ∈ range (n + 1), c i * ι x ^ i := by
      refine Finset.sum_subset (fun i hi => ?_) (fun i hi hi' => ?_)
      · simp only [mem_range] at hi ⊢
        omega
      · rw [hvanish i hi (by simpa using hi'), zero_mul]
    rw [h2]
    exact h
  have hq0 : q = 0 := by
    by_cases hqz : q = 0
    · exact hqz
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q ι.injective hqeval ?_
    rw [ZMod.card]
    have h1 : q.natDegree < N := (Polynomial.natDegree_lt_iff_degree_lt hqz).mpr hqdeg
    omega
  intro i hi
  by_cases hiN : N ≤ i
  · exact hvanish i hi hiN
  · have hcoeff : q.coeff i = c i := by
      rw [hq, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin N)]
      · simp
      · intro b _ hb
        rw [ite_eq_right]
        intro h
        apply hb
        exact Fin.ext h.symm
      · simp
    rw [← hcoeff, hq0, Polynomial.coeff_zero]

/--
@isnad1 id=eq.2h4v.s10.b66f0167434e from=translated src=- shape=c5c3df27 vocab=be3b4987
-/
theorem monomial_sub_monomial_step {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (monomial (e (j + (p - 1)) m) (1 : K) : MvPolynomial (Fin 2) K) - monomial (e j (m + (p - 1))) 1
      = theta p K * monomial (e (j - 1) (m - 1)) 1 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp0 : p ≠ 0 := hp.out.ne_zero
  rw [monomial_e, monomial_e, monomial_e, theta, ← pow_sub_one_mul hp0 (X 0 : MvPolynomial (Fin 2) K),
    ← pow_sub_one_mul hp0 (X 1 : MvPolynomial (Fin 2) K)]
  simp only [map_one, one_mul, Nat.add_sub_cancel]
  ring

/--
@isnad1 id=ex.2h5v.s9.d0ac90111d84 from=translated src=- shape=dfd00dae vocab=5f57b6bf
-/
theorem monomial_sub_monomial_red {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ∀ {m : ℕ}, 1 ≤ m → ∃ H : MvPolynomial (Fin 2) K, H.IsHomogeneous (j + m + k * (p - 1) - (p + 1)) ∧
      (monomial (e (j + k * (p - 1)) m) (1 : K) : MvPolynomial (Fin 2) K)
        - monomial (e j (m + k * (p - 1))) 1 = theta p K * H := by
  induction k with
  | zero =>
    intro m _
    exact ⟨0, isHomogeneous_zero _ _ _, by simp⟩
  | succ k ih =>
    intro m hm
    have hp2 := hp.out.two_le
    obtain ⟨H, hH, hHeq⟩ := ih (m := m + (p - 1)) (by omega)
    refine ⟨monomial (e (j + k * (p - 1) - 1) (m - 1)) 1 + H, ?_, ?_⟩
    · refine IsHomogeneous.add ?_ ?_
      · have h : j + k * (p - 1) - 1 + (m - 1) = j + m + (k + 1) * (p - 1) - (p + 1) := by
          have : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
          omega
        rw [← h]
        exact isHomogeneous_monomial_e K _ _ 1
      · have h : j + (m + (p - 1)) + k * (p - 1) - (p + 1) = j + m + (k + 1) * (p - 1) - (p + 1) := by
          have : (k + 1) * (p - 1) = k * (p - 1) + (p - 1) := by ring
          omega
        rwa [← h]
    · have h1 : j + (k + 1) * (p - 1) = (j + k * (p - 1)) + (p - 1) := by ring
      have h2 : m + (k + 1) * (p - 1) = (m + (p - 1)) + k * (p - 1) := by ring
      rw [h1, h2, mul_add, ← hHeq, ← monomial_sub_monomial_step p K (j := j + k * (p - 1)) (by omega) hm]
      ring

def rd (i : ℕ) : ℕ := 1 + (i - 1) % (p - 1)

/--
@isnad1 id=le.0h2v.s4.39970e5ce652 from=translated src=- shape=82888bae vocab=14a87ff9
-/
theorem one_le_rd (i : ℕ) : 1 ≤ rd p i := Nat.le_add_right _ _

/--
@isnad1 id=le.0h2v.s4.9f8ade3a3d7d from=translated src=- shape=4c2307c2 vocab=5143c93e
-/
theorem rd_le (i : ℕ) : rd p i ≤ p - 1 := by
  have h1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have := Nat.mod_lt (i - 1) h1
  unfold rd
  omega

/--
@isnad1 id=le.1h2v.s4.1a7dda97d7ff from=translated src=- shape=2393d40e vocab=14a87ff9
-/
theorem rd_le_self {i : ℕ} (hi : 1 ≤ i) : rd p i ≤ i := by
  have := Nat.mod_le (i - 1) (p - 1)
  unfold rd
  omega

/--
@isnad1 id=eq.1h2v.s6.5a08bd7eae23 from=translated src=- shape=1c355347 vocab=c67b52a8
-/
theorem rd_spec {i : ℕ} (hi : 1 ≤ i) : i = rd p i + (i - 1) / (p - 1) * (p - 1) := by
  have := Nat.div_add_mod' (i - 1) (p - 1)
  unfold rd
  omega

/--
@isnad1 id=ex.2h4v.s8.b2f10a71c494 from=translated src=- shape=60fa143a vocab=745a40de
-/
theorem exists_eq_theta_mul {n : ℕ} {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous n)
    (hvan : ∀ v, ev p K F v = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H.IsHomogeneous (n - (p + 1)) ∧ F = theta p K * H := by
  classical
  set ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hι

  set g : ℕ → ℕ := fun i => if i = 0 ∨ i = n then i else rd p i with hg
  have hg_le : ∀ i, i ≤ n → g i ≤ i := by
    intro i hi
    simp only [hg]
    split_ifs with h
    · exact le_rfl
    · push_neg at h
      exact rd_le_self p (by omega)
  have key : ∀ i : ℕ, ∃ H : MvPolynomial (Fin 2) K, i ≤ n → H.IsHomogeneous (n - (p + 1)) ∧
      (monomial (e i (n - i)) (1 : K) : MvPolynomial (Fin 2) K) - monomial (e (g i) (n - g i)) 1
        = theta p K * H := by
    intro i
    by_cases h : i = 0 ∨ i = n
    · refine ⟨0, fun _ => ⟨isHomogeneous_zero _ _ _, ?_⟩⟩
      simp [hg, h]
    · push_neg at h
      by_cases hin : i ≤ n
      · have hi1 : 1 ≤ i := by omega
        obtain ⟨H, hH, hHeq⟩ := monomial_sub_monomial_red p K (j := rd p i) (one_le_rd p i)
          ((i - 1) / (p - 1)) (m := n - i) (by omega)
        refine ⟨H, fun _ => ⟨?_, ?_⟩⟩
        · have := rd_spec p hi1
          have h' : rd p i + (n - i) + (i - 1) / (p - 1) * (p - 1) - (p + 1) = n - (p + 1) := by omega
          rwa [h'] at hH
        · have hgi : g i = rd p i := by simp [hg, h.1, h.2]
          have h1 : e i (n - i) = e (rd p i + (i - 1) / (p - 1) * (p - 1)) (n - i) := by
            rw [← rd_spec p hi1]
          have h2 : e (g i) (n - g i) = e (rd p i) ((n - i) + (i - 1) / (p - 1) * (p - 1)) := by
            rw [hgi, e_eq_iff]
            have := rd_spec p hi1
            exact ⟨rfl, by omega⟩
          rw [h1, h2, hHeq]
      · exact ⟨0, fun h' => absurd h' hin⟩
  choose H hH using key
  set c : ℕ → K := fun i => coeff (e i (n - i)) F with hc

  set Fr : MvPolynomial (Fin 2) K := ∑ i ∈ range (n + 1), monomial (e (g i) (n - g i)) (c i) with hFr
  have hFdecomp : F = Fr + theta p K * ∑ i ∈ range (n + 1), C (c i) * H i := by
    conv_lhs => rw [eq_sum_monomial K hF]
    rw [hFr, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have h := (hH i hin).2
    have e1 : (monomial (e i (n - i)) (c i) : MvPolynomial (Fin 2) K) = C (c i) * monomial (e i (n - i)) 1 := by
      rw [C_mul_monomial, mul_one]
    have e2 : (monomial (e (g i) (n - g i)) (c i) : MvPolynomial (Fin 2) K)
        = C (c i) * monomial (e (g i) (n - g i)) 1 := by
      rw [C_mul_monomial, mul_one]
    rw [e1, e2]
    linear_combination (C (c i)) * h

  have hFrvan : ∀ v, ev p K Fr v = 0 := by
    intro v
    have h := hvan v
    rw [hFdecomp, ev_add, ev_mul, ev_theta, zero_mul, add_zero] at h
    exact h

  have hmaps : ∀ i ∈ range (n + 1), g i ∈ range (n + 1) := by
    intro i hi
    simp only [mem_range, Nat.lt_succ_iff] at hi ⊢
    exact (hg_le i hi).trans hi
  set d : ℕ → K := fun j => ∑ i ∈ (range (n + 1)).filter (fun i => g i = j), c i with hd
  have hFr' : Fr = ∑ j ∈ range (n + 1), monomial (e j (n - j)) (d j) := by
    rw [hFr, ← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  have hdsupp : ∀ j ∈ range (n + 1), d j ≠ 0 → j = n ∨ j < p := by
    intro j _ hj
    obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
    rw [Finset.mem_filter] at hi
    obtain ⟨hi, hgi⟩ := hi
    rw [← hgi, hg]
    dsimp only
    split_ifs with h
    · rcases h with h | h
      · right; rw [h]; exact hp.out.pos
      · left; exact h
    · right
      have := rd_le p i
      have := hp.out.one_le
      omega
  have hdev : ∀ x y : ZMod p, ∑ j ∈ range (n + 1), d j * ι x ^ j * ι y ^ (n - j) = 0 := by
    intro x y
    have h := hFrvan ![x, y]
    rw [hFr', ev_sum] at h
    simpa only [ev_monomial, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  have hd0 := coeffs_eq_zero_of_ev p K d hdsupp hdev
  have hFr0 : Fr = 0 := by
    rw [hFr']
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hd0 j hj, map_zero]
  refine ⟨∑ i ∈ range (n + 1), C (c i) * H i, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hin : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    exact ((hH i hin).1).C_mul _
  · rw [hFdecomp, hFr0, zero_add]

end Eval

end ATHRVan
open scoped _root_.P2MW.S_HeckeEis_exists_binaryForm_eq_mul_of_forall_eval_eq_zero.ATHRVan

open MvPolynomial in
/--
@isnad1 id=ex.2h4v.s10.41c1d21ce826 from=translated src=- shape=ec518cb9 vocab=3dd6ed04
-/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (n : ℕ) (F : MvPolynomial (Fin 2) K)
    (hF : F ∈ HeckeEis.BinaryForm K n)
    (hvan : ∀ v : Fin 2 → ZMod p,
      MvPolynomial.eval (fun i => ZMod.castHom (dvd_refl p) K (v i)) F = 0) :
    ∃ H : MvPolynomial (Fin 2) K, H ∈ HeckeEis.BinaryForm K (n - (p + 1)) ∧
      F = (X 0 ^ p * X 1 - X 0 * X 1 ^ p) * H := by
  obtain ⟨H, hH, hFH⟩ := ATHRVan.exists_eq_theta_mul p K
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hF) hvan
  exact ⟨H, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hH, hFH⟩
