import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_exists_algEquiv_apply_X_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_exists_algEquiv_apply_X_eq

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace FormalIFT

variable {W : Type*} [CommRing W] {σ : Type*} [Fintype σ] [DecidableEq σ]

section Order

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=le.1h6v.s6.6c43bb200e58 from=translated src=- shape=31a50fcb vocab=018378db
-/
theorem le_order_finset_sum {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ W) (n : ℕ∞)
    (h : ∀ i ∈ s, n ≤ order (F i)) : n ≤ order (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ min_order_le_add
    exact le_min (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fintype σ] [DecidableEq σ] in

/--
@isnad1 id=le.3h5v.s7.56c4a8b07f11 from=translated src=- shape=262d229d vocab=aaa2687b
-/
theorem le_order_pow_sub_pow {u v : MvPowerSeries σ W} (hu : (1 : ℕ∞) ≤ order u) (hv : (1 : ℕ∞) ≤ order v)
    (huv : (2 : ℕ∞) ≤ order (u - v)) (k : ℕ) : ((k + 1 : ℕ) : ℕ∞) ≤ order (u ^ k - v ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [← geom_sum₂_mul]

    have hs : ((k - 1 : ℕ) : ℕ∞) ≤ order (∑ i ∈ Finset.range k, u ^ i * v ^ (k - 1 - i)) := by
      refine le_order_finset_sum _ _ _ fun i hi => ?_
      rw [Finset.mem_range] at hi
      refine le_trans ?_ le_order_mul
      have h1 : ((i : ℕ) : ℕ∞) ≤ order (u ^ i) :=
        le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right hu i) (le_order_pow i))
      have h2 : ((k - 1 - i : ℕ) : ℕ∞) ≤ order (v ^ (k - 1 - i)) :=
        le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right hv (k - 1 - i)) (le_order_pow _))
      calc ((k - 1 : ℕ) : ℕ∞) = ((i : ℕ) : ℕ∞) + ((k - 1 - i : ℕ) : ℕ∞) := by
            rw [← Nat.cast_add]; congr 1; omega
        _ ≤ order (u ^ i) + order (v ^ (k - 1 - i)) := add_le_add h1 h2
    refine le_trans ?_ le_order_mul
    calc ((k + 1 : ℕ) : ℕ∞) = ((k - 1 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add]; congr 1; omega
      _ ≤ _ := add_le_add hs (by exact_mod_cast huv)

omit [Fintype σ] [DecidableEq σ] in

/--
@isnad1 id=le.3h7v.s8.526927f26237 from=translated src=- shape=66e35539 vocab=5bdf493b
-/
theorem le_order_prod_sub_prod {ι : Type*} (t : Finset ι) (A B : ι → MvPowerSeries σ W) (m : ι → ℕ)
    (hA : ∀ i ∈ t, ((m i : ℕ) : ℕ∞) ≤ order (A i)) (hB : ∀ i ∈ t, ((m i : ℕ) : ℕ∞) ≤ order (B i))
    (hAB : ∀ i ∈ t, ((m i + 1 : ℕ) : ℕ∞) ≤ order (A i - B i)) :
    ((∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) ≤ order (∏ i ∈ t, A i - ∏ i ∈ t, B i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hBt : ((∑ i ∈ t, m i : ℕ) : ℕ∞) ≤ order (∏ i ∈ t, B i) := by
      refine le_trans ?_ (le_order_prod _ _)
      push_cast
      exact Finset.sum_le_sum fun i hi => hB i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have e : A a * ∏ i ∈ t, A i - B a * ∏ i ∈ t, B i
        = A a * (∏ i ∈ t, A i - ∏ i ∈ t, B i) + (A a - B a) * ∏ i ∈ t, B i := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      calc ((m a + ∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) = ((m a : ℕ) : ℕ∞) + ((∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) := by
            push_cast; ring
        _ ≤ _ := add_le_add (hA a (Finset.mem_insert_self a t))
              (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi)) (fun i hi => hB i (Finset.mem_insert_of_mem hi))
                (fun i hi => hAB i (Finset.mem_insert_of_mem hi)))
    · refine le_trans ?_ le_order_mul
      calc ((m a + ∑ i ∈ t, m i + 1 : ℕ) : ℕ∞) = ((m a + 1 : ℕ) : ℕ∞) + ((∑ i ∈ t, m i : ℕ) : ℕ∞) := by
            push_cast; ring
        _ ≤ _ := add_le_add (hAB a (Finset.mem_insert_self a t)) hBt

omit [DecidableEq σ] in

/--
@isnad1 id=eq.0h3v.s8.402942d1e77d from=translated src=- shape=7c7a6dc0 vocab=565793cd
-/
theorem prod_X_pow_eq_monomial (d : σ →₀ ℕ) :
    ∏ s, (X s : MvPowerSeries σ W) ^ (d s) = monomial d 1 := by
  classical
  have key : ∀ t : Finset σ, ∏ s ∈ t, (X s : MvPowerSeries σ W) ^ (d s)
      = monomial (∑ s ∈ t, Finsupp.single s (d s)) 1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

/--
@isnad1 id=le.2h4v.s9.21bf6c67056e from=translated src=- shape=e558c3fc vocab=0e91cf99
-/
theorem le_order_prod_pow_sub_monomial (g : σ → MvPowerSeries σ W) (hg0 : ∀ s, constantCoeff (g s) = 0)
    (hg1 : ∀ s, (2 : ℕ∞) ≤ order (g s - X s)) (d : σ →₀ ℕ) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤ order (∏ s, g s ^ (d s) - monomial d 1) := by
  rw [← prod_X_pow_eq_monomial]
  have hX : ∀ s : σ, (1 : ℕ∞) ≤ order (X s : MvPowerSeries σ W) := fun s =>
    one_le_order_iff_constCoeff_eq_zero.mpr (constantCoeff_X _)
  have hg : ∀ s : σ, (1 : ℕ∞) ≤ order (g s) := fun s =>
    one_le_order_iff_constCoeff_eq_zero.mpr (hg0 s)
  have h := le_order_prod_sub_prod (Finset.univ : Finset σ) (fun s => g s ^ (d s)) (fun s => (X s : MvPowerSeries σ W) ^ (d s))
    (fun s => d s)
    (fun s _ => le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right (hg s) (d s)) (le_order_pow _)))
    (fun s _ => le_trans (by rw [nsmul_eq_mul, mul_one]) (le_trans (nsmul_le_nsmul_right (hX s) (d s)) (le_order_pow _)))
    (fun s _ => le_order_pow_sub_pow (hg s) (hX s) (hg1 s) (d s))
  rw [Finsupp.degree_eq_sum]
  exact h

end Order

section Unipotent

variable (g : σ → MvPowerSeries σ W) (hg0 : ∀ s, constantCoeff (g s) = 0)
  (hg1 : ∀ s, (2 : ℕ∞) ≤ order (g s - X s))

include hg0 hg1 in

/--
@isnad1 id=eq.3h5v.s9.1987dfb77fff from=translated src=- shape=2ff112aa vocab=589b7c3c
-/
theorem coeff_prod_pow (d e : σ →₀ ℕ) (hde : e.degree ≤ d.degree) :
    coeff e (∏ s, g s ^ (d s)) = if e = d then 1 else 0 := by
  have h := le_order_prod_pow_sub_monomial g hg0 hg1 d
  have hz : coeff e (∏ s, g s ^ (d s) - monomial d 1) = 0 :=
    coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hde) h)
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, coeff_monomial]

include hg0 hg1 in

/--
@isnad1 id=eq.4h6v.s9.fc38f4ac7660 from=translated src=- shape=85bea70d vocab=032220bf
-/
theorem coeff_subst_eq_coeff (F : MvPowerSeries σ W) (n : ℕ)
    (hF : ∀ d : σ →₀ ℕ, d.degree < n → coeff d F = 0) (e : σ →₀ ℕ) (he : e.degree ≤ n) :
    coeff e (subst g F) = coeff e F := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero hg0)]
  have hterm : ∀ d : σ →₀ ℕ,
      coeff d F • coeff e (d.prod fun s n => g s ^ n) = if d = e then coeff e F else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
    by_cases hde : d = e
    · subst hde
      rw [ite_eq_left rfl]
      by_cases hd : d.degree < n
      · rw [hF d hd, zero_smul]
      · push_neg at hd
        rw [coeff_prod_pow g hg0 hg1 d d le_rfl, ite_eq_left rfl, smul_eq_mul, mul_one]
    · rw [ite_eq_right hde]
      by_cases hd : d.degree < n
      · rw [hF d hd, zero_smul]
      · push_neg at hd
        rw [coeff_prod_pow g hg0 hg1 d e (le_trans he hd), ite_eq_right (Ne.symm hde), smul_zero]
  rw [finsum_congr hterm, finsum_eq_single _ e (fun d hd => ite_eq_right hd), ite_eq_left rfl]

def T (F : MvPowerSeries σ W) : MvPowerSeries σ W := F - subst g F

include hg0 in
/--
@isnad1 id=eq.1h5v.s7.0874df772dce from=translated src=- shape=0414be29 vocab=34eff08b
-/
theorem T_add (F G : MvPowerSeries σ W) : T g (F + G) = T g F + T g G := by
  simp only [T, subst_add (hasSubst_of_constantCoeff_zero hg0)]
  ring

include hg0 in
/--
@isnad1 id=eq.1h6v.s7.e4002c7e1792 from=translated src=- shape=7effa418 vocab=ed85431d
-/
theorem T_sum {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ W) :
    T g (∑ i ∈ s, F i) = ∑ i ∈ s, T g (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, T, ← coe_substAlgHom (hasSubst_of_constantCoeff_zero hg0), map_zero,
      sub_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, T_add g hg0, ih]

include hg0 hg1 in

/--
@isnad1 id=eq.3h6v.s8.9568ab22296a from=translated src=- shape=bf6447ca vocab=99e7ecd4
-/
theorem coeff_iterate_T (k : ℕ) : ∀ (G : MvPowerSeries σ W) (e : σ →₀ ℕ), e.degree < k →
    coeff e ((T g)^[k] G) = 0 := by
  induction k with
  | zero => intro G e he; exact absurd he (Nat.not_lt_zero _)
  | succ k ih =>
    intro G e he
    rw [Function.iterate_succ_apply', T, map_sub,
      coeff_subst_eq_coeff g hg0 hg1 _ k (fun d hd => ih G d hd) e (Nat.lt_succ_iff.mp he), sub_self]

include hg0 hg1 in

/--
@isnad1 id=eq.3h4v.s7.6da36ba7a52a from=translated src=- shape=8e2a40a6 vocab=07b322be
-/
theorem subst_injective_aux (F : MvPowerSeries σ W) (hF : subst g F = 0) : F = 0 := by
  have hT : T g F = F := by rw [T, hF, sub_zero]
  ext e
  rw [map_zero, ← Function.iterate_fixed hT (e.degree + 1)]
  exact coeff_iterate_T g hg0 hg1 (e.degree + 1) F e (Nat.lt_succ_self _)

def psi (G : MvPowerSeries σ W) : MvPowerSeries σ W :=
  fun e => ∑ k ∈ Finset.range (e.degree + 1), coeff e ((T g)^[k] G)

/--
@isnad1 id=eq.0h5v.s9.2443a095b1cb from=translated src=- shape=a5187bc3 vocab=4f10f9cb
-/
theorem coeff_psi (G : MvPowerSeries σ W) (e : σ →₀ ℕ) :
    coeff e (psi g G) = ∑ k ∈ Finset.range (e.degree + 1), coeff e ((T g)^[k] G) := rfl

def S (G : MvPowerSeries σ W) (m : ℕ) : MvPowerSeries σ W := ∑ k ∈ Finset.range (m + 1), (T g)^[k] G

include hg0 hg1 in
/--
@isnad1 id=eq.3h6v.s9.4fa68905cb3c from=translated src=- shape=0684b05d vocab=486843eb
-/
theorem coeff_psi_eq_coeff_S (G : MvPowerSeries σ W) (m : ℕ) (e : σ →₀ ℕ) (he : e.degree ≤ m) :
    coeff e (psi g G) = coeff e (S g G m) := by
  rw [coeff_psi, S, map_sum]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ he)) fun k _ hk' => ?_
  have hk2 : e.degree < k := by
    simp only [Finset.mem_range, not_lt] at hk'
    omega
  exact coeff_iterate_T g hg0 hg1 k G e hk2

include hg0 in

/--
@isnad1 id=eq.1h5v.s7.5dc1f5542334 from=translated src=- shape=bc9ca5b3 vocab=4606ee67
-/
theorem subst_S (G : MvPowerSeries σ W) (m : ℕ) : subst g (S g G m) = G - (T g)^[m + 1] G := by
  have e1 : subst g (S g G m) = S g G m - T g (S g G m) := by rw [T]; ring
  rw [e1, S, T_sum g hg0]
  have e2 : ∑ k ∈ Finset.range (m + 1), T g ((T g)^[k] G) = ∑ k ∈ Finset.range (m + 1), (T g)^[k + 1] G :=
    Finset.sum_congr rfl fun k _ => by rw [Function.iterate_succ_apply']
  rw [e2, ← sub_eq_zero]
  have e3 := Finset.sum_range_sub (fun k => (T g)^[k] G) (m + 1)
  rw [Function.iterate_zero_apply, Finset.sum_sub_distrib] at e3
  linear_combination -e3

include hg0 hg1 in

/--
@isnad1 id=eq.2h4v.s7.f741ee6165f0 from=translated src=- shape=6040ced9 vocab=17d6feca
-/
theorem subst_psi (G : MvPowerSeries σ W) : subst g (psi g G) = G := by
  ext e
  set m := e.degree with hm
  have hvan : ∀ d : σ →₀ ℕ, d.degree < m + 1 → coeff d (psi g G - S g G m) = 0 := by
    intro d hd
    rw [map_sub, coeff_psi_eq_coeff_S g hg0 hg1 G m d (Nat.lt_succ_iff.mp hd), sub_self]
  have h1 : coeff e (subst g (psi g G - S g G m)) = 0 := by
    rw [coeff_subst_eq_coeff g hg0 hg1 _ (m + 1) hvan e (by omega), hvan e (by omega)]
  rw [subst_sub (hasSubst_of_constantCoeff_zero hg0), map_sub, sub_eq_zero] at h1
  rw [h1, subst_S g hg0, map_sub, coeff_iterate_T g hg0 hg1 (m + 1) G e (by omega), sub_zero]

include hg0 hg1 in

/--
@isnad1 id=bijectiv.2h3v.s8.ffd3df204218 from=translated src=- shape=904f6c00 vocab=a164e3cc
-/
theorem bijective_substAlgHom : Function.Bijective (substAlgHom (hasSubst_of_constantCoeff_zero hg0) :
    MvPowerSeries σ W →ₐ[W] MvPowerSeries σ W) := by
  rw [coe_substAlgHom]
  constructor
  · intro F₁ F₂ h
    have h' : subst g (F₁ - F₂) = 0 := by
      rw [subst_sub (hasSubst_of_constantCoeff_zero hg0)]
      exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (subst_injective_aux g hg0 hg1 _ h')
  · intro G
    exact ⟨psi g G, subst_psi g hg0 hg1 G⟩

end Unipotent

section Linear

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=eq.3h5v.s8.72ab154549b5 from=translated src=- shape=bb841811 vocab=83baef77
-/
theorem substAlgHom_congr {a b : σ → MvPowerSeries σ W} (ha : HasSubst a) (hb : HasSubst b) (h : a = b)
    (F : MvPowerSeries σ W) : substAlgHom ha F = substAlgHom hb F := by
  subst h
  rfl

def lin (M : Matrix σ σ W) : σ → MvPowerSeries σ W := fun i => ∑ j, M i j • (X j : MvPowerSeries σ W)

omit [DecidableEq σ] in
/--
@isnad1 id=eq.0h4v.s6.fbffec0ed491 from=translated src=- shape=98f96a69 vocab=5aca6fa8
-/
theorem lin_apply (M : Matrix σ σ W) (i : σ) : lin M i = ∑ j, M i j • (X j : MvPowerSeries σ W) := rfl

/--
@isnad1 id=eq.0h4v.s6.90c280898422 from=translated src=- shape=bbf873d5 vocab=38e44ce2
-/
theorem constantCoeff_lin (M : Matrix σ σ W) (i : σ) : constantCoeff (lin M i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, lin_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_smul, coeff_X, ite_eq_right (Ne.symm (Finsupp.single_ne_zero.mpr one_ne_zero)), mul_zero]

/--
@isnad1 id=hassubst.0h3v.s4.8fc55fa522a6 from=translated src=- shape=1c88bcee vocab=f278fc3a
-/
theorem hasSubst_lin (M : Matrix σ σ W) : HasSubst (lin M) := hasSubst_of_constantCoeff_zero (constantCoeff_lin M)

def φL (M : Matrix σ σ W) : MvPowerSeries σ W →ₐ[W] MvPowerSeries σ W := substAlgHom (hasSubst_lin M)

/--
@isnad1 id=eq.0h4v.s7.5befdb84abfe from=translated src=- shape=ababea9d vocab=38452e17
-/
theorem φL_X (M : Matrix σ σ W) (i : σ) : φL M (X i) = lin M i := by
  rw [φL, substAlgHom_X]

/--
@isnad1 id=eq.0h5v.s7.8b041baf194e from=translated src=- shape=5ed51973 vocab=668d341f
-/
theorem φL_lin (M N : Matrix σ σ W) (i : σ) : φL N (lin M i) = lin (M * N) i := by
  simp only [lin_apply, map_sum, map_smul, φL_X]
  simp only [lin_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h5v.s8.3caabfc89cbd from=translated src=- shape=1acedb30 vocab=eef8db2d
-/
theorem φL_comp (M N : Matrix σ σ W) (F : MvPowerSeries σ W) : φL N (φL M F) = φL (M * N) F := by
  rw [φL, φL, substAlgHom_comp_substAlgHom_apply]
  refine substAlgHom_congr _ _ ?_ F
  funext i
  exact φL_lin M N i

/--
@isnad1 id=eq.0h2v.s6.843eecea4316 from=translated src=- shape=fcb16acc vocab=7d1332fd
-/
theorem lin_one : lin (1 : Matrix σ σ W) = fun s => (X s : MvPowerSeries σ W) := by
  funext i
  rw [lin_apply]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq Finset.univ i (fun j => (X j : MvPowerSeries σ W)), ite_eq_left (Finset.mem_univ i)]

/--
@isnad1 id=eq.0h3v.s7.9fd5f5f24c44 from=translated src=- shape=cf5408d8 vocab=309809f2
-/
theorem φL_one (F : MvPowerSeries σ W) : φL (1 : Matrix σ σ W) F = F := by
  rw [φL, substAlgHom_congr (hasSubst_lin 1) HasSubst.X lin_one F]
  change (⇑(substAlgHom HasSubst.X)) F = F
  rw [coe_substAlgHom, subst_self, id]

def linEquiv (M : Matrix σ σ W) (hM : IsUnit M.det) : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W :=
  AlgEquiv.ofAlgHom (φL M) (φL M⁻¹)
    (AlgHom.ext fun F => by rw [AlgHom.comp_apply, φL_comp, Matrix.nonsing_inv_mul _ hM, φL_one]; rfl)
    (AlgHom.ext fun F => by rw [AlgHom.comp_apply, φL_comp, Matrix.mul_nonsing_inv _ hM, φL_one]; rfl)

/--
@isnad1 id=eq.1h4v.s7.c9668b4c0e58 from=translated src=- shape=1c1b66b5 vocab=aecd5650
-/
theorem linEquiv_X (M : Matrix σ σ W) (hM : IsUnit M.det) (i : σ) : linEquiv M hM (X i) = lin M i :=
  φL_X M i

end Linear

section Main

omit [Fintype σ] [DecidableEq σ] in
/--
@isnad1 id=ex.1h2v.s7.744e2e49167b from=translated src=- shape=bdf8b0dd vocab=dbf5d1eb
-/
theorem exists_single_of_degree_eq_one (d : σ →₀ ℕ) (h : d.degree = 1) : ∃ k, d = Finsupp.single k 1 := by
  have hd : d ∈ {d : σ →₀ ℕ | d.degree = 1} := h
  rw [← Finsupp.range_single_one] at hd
  obtain ⟨k, hk⟩ := hd
  exact ⟨k, hk.symm⟩

/--
@isnad1 id=ex.2h3v.s9.5a4856d1418d from=translated src=- shape=ced5379f vocab=5cc3ea78
-/
theorem exists_algEquiv (f : σ → MvPowerSeries σ W) (h0 : ∀ i, constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : σ => coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W, ∀ i, e (X i) = f i := by
  set M : Matrix σ σ W := Matrix.of fun i j : σ => coeff (Finsupp.single j 1) (f i) with hMdef
  have hM : ∀ i j, M i j = coeff (Finsupp.single j 1) (f i) := fun i j => rfl

  set g : σ → MvPowerSeries σ W := fun i => ∑ j, M⁻¹ i j • f j with hgdef
  have hg0 : ∀ i, constantCoeff (g i) = 0 := by
    intro i
    rw [hgdef, ← coeff_zero_eq_constantCoeff_apply, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_smul, coeff_zero_eq_constantCoeff_apply, h0 j, mul_zero]
  have hglin : ∀ i k, coeff (Finsupp.single k 1) (g i) = if k = i then 1 else 0 := by
    intro i k
    rw [hgdef, map_sum]
    simp only [coeff_smul, ← hM]
    have e : ∑ j, M⁻¹ i j * M j k = (M⁻¹ * M) i k := (Matrix.mul_apply).symm
    rw [e, Matrix.nonsing_inv_mul _ h1, Matrix.one_apply]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right hik, ite_eq_right (Ne.symm hik)]
  have hg1 : ∀ i, (2 : ℕ∞) ≤ order (g i - X i) := by
    intro i
    refine nat_le_order fun d hd => ?_
    rw [map_sub]
    rcases Nat.lt_succ_iff.mp hd |>.lt_or_eq with hlt | heq
    ·
      have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff _).mp (Nat.lt_one_iff.mp hlt)
      subst hd0
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hg0 i, constantCoeff_X, sub_self]
    · obtain ⟨k, rfl⟩ := exists_single_of_degree_eq_one d heq
      rw [hglin i k, coeff_index_single_X, sub_self]

  let eg : MvPowerSeries σ W ≃ₐ[W] MvPowerSeries σ W :=
    AlgEquiv.ofBijective (substAlgHom (hasSubst_of_constantCoeff_zero hg0)) (bijective_substAlgHom g hg0 hg1)
  have heg : ∀ i, eg (X i) = g i := fun i => by
    show substAlgHom (hasSubst_of_constantCoeff_zero hg0) (X i) = g i
    rw [substAlgHom_X]
  refine ⟨(linEquiv M h1).trans eg, fun i => ?_⟩
  rw [AlgEquiv.trans_apply, linEquiv_X, lin_apply, map_sum]
  simp only [map_smul, heg, hgdef, Finset.smul_sum, smul_smul]

  rw [Finset.sum_comm]
  have e : ∀ l, ∑ j, (M i j * M⁻¹ j l) • f l = ((M * M⁻¹) i l) • f l := fun l => by
    rw [← Finset.sum_smul, ← Matrix.mul_apply]
  simp only [e, Matrix.mul_nonsing_inv _ h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq Finset.univ i f, ite_eq_left (Finset.mem_univ i)]

end Main

end FormalIFT

end

/--
@isnad1 id=ex.2h2v.s10.2b8d1d4a2381 from=translated src=- shape=87208842 vocab=16967e71
-/
theorem solution
    {W : Type*} [CommRing W] (f : Fin 2 → MvPowerSeries (Fin 2) W)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 => MvPowerSeries.coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W, ∀ i, e (MvPowerSeries.X i) = f i :=
  FormalIFT.exists_algEquiv f h0 h1
