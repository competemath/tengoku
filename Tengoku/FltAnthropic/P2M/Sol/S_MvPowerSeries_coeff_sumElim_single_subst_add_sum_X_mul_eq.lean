import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq

set_option autoImplicit false

namespace S17TY

open MvPowerSeries

variable {R : Type*} [CommRing R] {σ : Type*} {τ : Type*} {κ : Type*}

local notation "D" => DualNumber R

noncomputable def iota (a : MvPowerSeries τ R) : MvPowerSeries (τ ⊕ κ) R :=
  subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) a

/--
@isnad1 id=hassubst.0h3v.s5.ae76ddf00619 from=translated src=- shape=c3c1d3c7 vocab=1d9f05d0
-/
theorem hasSubst_Xinl : HasSubst (fun t : τ => (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) := by
  classical
  refine ⟨fun t => by rw [constantCoeff_X]; exact IsNilpotent.zero, fun d => ?_⟩
  apply Set.Subsingleton.finite
  intro t₁ h₁ t₂ h₂
  simp only [Set.mem_ofPred_eq, coeff_X] at h₁ h₂
  split_ifs at h₁ h₂ with e₁ e₂
  · have := e₁.symm.trans e₂
    exact Sum.inl_injective (Finsupp.single_left_injective one_ne_zero this)
  all_goals simp_all

/--
@isnad1 id=eq.1h4v.s7.30d47dc85efb from=translated src=- shape=1739bffd vocab=af9c73e4
-/
theorem constantCoeff_iota (a : MvPowerSeries τ R) (ha : constantCoeff a = 0) :
    constantCoeff (iota (κ := κ) a) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_Xinl (fun t => constantCoeff_X _) ha

variable [Fintype σ] [Fintype κ]

noncomputable def Gfam (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    MvPowerSeries (τ ⊕ κ) R :=
  iota (A i) + ∑ k' : κ, X (Sum.inr k') * iota (B i k')

omit [Fintype σ] in
/--
@isnad1 id=eq.1h7v.s7.a1000368dbec from=translated src=- shape=090032bb vocab=f78d7b92
-/
theorem constantCoeff_Gfam (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (i : σ) : constantCoeff (Gfam A B i) = 0 := by
  rw [Gfam, map_add, constantCoeff_iota _ (hA i), map_sum, zero_add]
  exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]

/--
@isnad1 id=hassubst.1h6v.s7.fd6874bb81ce from=translated src=- shape=144935b6 vocab=2b5e82d0
-/
theorem hasSubst_Gfam (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) : HasSubst (Gfam A B) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_Gfam A hA B)

open Classical in

noncomputable def ak (k : κ) : τ ⊕ κ → MvPowerSeries τ D :=
  Sum.elim (fun t => X t) (fun k' => if k' = k then C DualNumber.eps else 0)

/--
@isnad1 id=hassubst.0h4v.s5.314289418e0c from=translated src=- shape=df1bcf27 vocab=3706b531
-/
theorem hasSubst_ak (k : κ) : HasSubst (ak (R := R) (τ := τ) k) := by
  classical
  refine ⟨?_, fun d => ?_⟩
  · rintro (t | k')
    · simp only [ak, Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
    · simp only [ak, Sum.elim_inr]
      split_ifs
      · rw [constantCoeff_C]; exact ⟨2, DualNumber.eps_pow_two⟩
      · rw [map_zero]; exact IsNilpotent.zero
  · apply Set.Finite.subset ((Set.finite_range Sum.inr).union
      (Set.Subsingleton.finite (s := {u : τ ⊕ κ | ∃ t, u = Sum.inl t ∧ d = Finsupp.single t 1}) ?_))
    · rintro (t | k') hu
      · right
        refine ⟨t, rfl, ?_⟩
        simp only [Set.mem_ofPred_eq, ak, Sum.elim_inl, coeff_X] at hu
        by_contra h
        exact hu (ite_eq_right h)
      · left; exact ⟨k', rfl⟩
    · rintro u₁ ⟨t₁, rfl, h₁⟩ u₂ ⟨t₂, rfl, h₂⟩
      rw [h₁] at h₂
      rw [Finsupp.single_left_injective one_ne_zero h₂]

noncomputable def theta (k : κ) : MvPowerSeries (τ ⊕ κ) R →ₐ[R] MvPowerSeries τ D :=
  substAlgHom (hasSubst_ak k)

/--
@isnad1 id=eq.0h5v.s8.bf4f33a0b787 from=translated src=- shape=e53d6ce3 vocab=fb9816c5
-/
theorem theta_apply (k : κ) (g : MvPowerSeries (τ ⊕ κ) R) : theta k g = subst (ak k) g := by
  rw [theta, substAlgHom_apply]

open Classical in
/--
@isnad1 id=eq.0h5v.s9.2ab076ed7f44 from=translated src=- shape=88d12d88 vocab=1f8ee203
-/
theorem theta_X_inr (k k' : κ) :
    theta (R := R) (τ := τ) k (X (Sum.inr k')) = if k' = k then C DualNumber.eps else 0 := by
  classical
  rw [theta, substAlgHom_X]; rfl

/--
@isnad1 id=eq.0h5v.s9.f9f5c50ef6e1 from=translated src=- shape=ab3f6eb1 vocab=ab21d3e7
-/
theorem theta_iota (k : κ) (a : MvPowerSeries τ R) :
    theta k (iota (κ := κ) a) = map (algebraMap R D) a := by
  rw [theta_apply, iota, subst_comp_subst_apply hasSubst_Xinl (hasSubst_ak k), map_algebraMap_eq_subst_X]
  congr 1
  funext t
  rw [subst_X (hasSubst_ak k)]; rfl

/--
@isnad1 id=eq.0h8v.s10.33c74463bf2f from=translated src=- shape=d3cfb3a3 vocab=a375575a
-/
theorem theta_Gfam (k : κ) (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    theta k (Gfam A B i) = map (algebraMap R D) (A i) + C DualNumber.eps * map (algebraMap R D) (B i k) := by
  classical
  rw [Gfam, map_add, map_sum, theta_iota]
  congr 1
  simp_rw [map_mul, theta_X_inr, theta_iota, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/--
@isnad1 id=eq.0h2v.s9.4dee4f132362 from=translated src=- shape=4af36152 vocab=900c9260
-/
theorem C_eps_mul_C_eps : (C DualNumber.eps : MvPowerSeries τ D) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

/--
@isnad1 id=eq.0h8v.s11.fd6fdf8dfda2 from=translated src=- shape=8e40cbcb vocab=9d4583b4
-/
theorem aeval_dual (k : κ) (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => map (algebraMap R D) (A i) + C DualNumber.eps * map (algebraMap R D) (B i k)) P =
      map (algebraMap R D) (MvPolynomial.aeval A P) +
        C DualNumber.eps * map (algebraMap R D) (∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i P)) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, map_C, Algebra.algebraMap_self,
      RingHom.id_apply]
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X q i₀ h =>
    have hder : ∀ i, MvPolynomial.aeval A (MvPolynomial.pderiv i (q * MvPolynomial.X i₀)) =
        MvPolynomial.aeval A (MvPolynomial.pderiv i q) * A i₀ +
          (if i = i₀ then MvPolynomial.aeval A q else 0) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.pderiv_X]
      by_cases hi : i = i₀
      · subst hi
        simp only [Pi.single_eq_same, map_one, ite_true]
        ring
      · simp only [Pi.single_eq_of_ne (Ne.symm hi), map_zero, ite_eq_right hi]
        ring
    have hsum : (∑ i, B i k * (MvPolynomial.aeval A (MvPolynomial.pderiv i q) * A i₀ +
        if i = i₀ then MvPolynomial.aeval A q else 0)) =
        (∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i q)) * A i₀ + B i₀ k * MvPolynomial.aeval A q := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_mul, mul_assoc]
    simp_rw [hder]
    rw [hsum, map_mul, MvPolynomial.aeval_X, h, map_mul, MvPolynomial.aeval_X]
    simp only [map_add, map_mul]
    have hε := C_eps_mul_C_eps (R := R) (τ := τ)
    linear_combination (map (algebraMap R D) (∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i q)) *
      map (algebraMap R D) (B i₀ k)) * hε

noncomputable def a0 : τ ⊕ κ → MvPowerSeries τ R := Sum.elim (fun t => X t) (fun _ => 0)

omit [Fintype σ] [Fintype κ] in
/--
@isnad1 id=hassubst.0h3v.s4.72ca2958aad8 from=translated src=- shape=c436134a vocab=398bc624
-/
theorem hasSubst_a0 : HasSubst (a0 (R := R) (τ := τ) (κ := κ)) := by
  classical
  refine ⟨?_, fun d => ?_⟩
  · rintro (t | k')
    · simp only [a0, Sum.elim_inl, constantCoeff_X]; exact IsNilpotent.zero
    · simp only [a0, Sum.elim_inr, map_zero]; exact IsNilpotent.zero
  · apply Set.Subsingleton.finite
    rintro (t₁ | k₁) h₁ (t₂ | k₂) h₂ <;>
      simp only [Set.mem_ofPred_eq, a0, Sum.elim_inl, Sum.elim_inr, coeff_X, map_zero, ne_eq,
        not_true_eq_false] at h₁ h₂
    split_ifs at h₁ h₂ with e₁ e₂
    · rw [e₁] at e₂
      rw [Finsupp.single_left_injective one_ne_zero e₂]
    all_goals simp_all

noncomputable def theta0 : MvPowerSeries (τ ⊕ κ) R →ₐ[R] MvPowerSeries τ R := substAlgHom hasSubst_a0

omit [Fintype σ] in
/--
@isnad1 id=eq.0h3v.s9.d544a783bfb7 from=translated src=- shape=f5a998b7 vocab=6de004b9
-/
theorem prod_X_pow_eq_monomial (n : τ →₀ ℕ) :
    (n.prod fun t e => (X t : MvPowerSeries τ D) ^ e) = monomial n 1 :=
  (MvPowerSeries.monomial_one_eq n).symm

omit [Fintype σ] in
open Classical in

/--
@isnad1 id=eq.0h6v.s10.67f122ad2fc0 from=translated src=- shape=84836c54 vocab=846ff688
-/
theorem coeff_prod_ak (k : κ) (m : τ →₀ ℕ) (n : τ ⊕ κ →₀ ℕ) :
    coeff m (n.prod fun u e => ak (R := R) k u ^ e) =
      if n = m.sumElim 0 then 1 else if n = m.sumElim (Finsupp.single k 1) then DualNumber.eps else 0 := by

  set nτ : τ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
  set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
  have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
  have hsplit : ∀ (c : κ →₀ ℕ), (nτ.sumElim nκ = m.sumElim c ↔ m = nτ ∧ nκ = c) := by
    intro c
    constructor
    · intro h
      exact ⟨Eq.symm (by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
        by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  rw [hn, Finsupp.prod_sumElim]
  simp only [Function.comp_def, ak, Sum.elim_inl, Sum.elim_inr, prod_X_pow_eq_monomial]

  have hY : (nκ.prod fun k' e => ((if k' = k then C DualNumber.eps else 0 : MvPowerSeries τ D)) ^ e) =
      if nκ = 0 then 1 else if nκ = Finsupp.single k 1 then C DualNumber.eps else 0 := by
    by_cases h0 : nκ = 0
    · rw [h0, ite_eq_left rfl, Finsupp.prod_zero_index]
    rw [ite_eq_right h0]
    by_cases hsupp : nκ.support ⊆ {k}
    ·
      have hj : nκ = Finsupp.single k (nκ k) := by
        ext k'
        by_cases hk' : k' = k
        · subst hk'; rw [Finsupp.single_eq_same]
        · rw [Finsupp.single_eq_of_ne hk']
          by_contra hne
          exact hk' (Finset.mem_singleton.1 (hsupp (Finsupp.mem_support_iff.2 hne)))
      have hk0 : nκ k ≠ 0 := fun h => h0 (by rw [hj, h, Finsupp.single_zero])
      rw [hj, Finsupp.prod_single_index (by simp), ite_eq_left rfl]
      obtain ⟨j, hjj⟩ : ∃ j, nκ k = j + 1 := ⟨nκ k - 1, by omega⟩
      rw [hjj]
      rcases j with _ | j
      · simp
      · rw [ite_eq_right, pow_succ, pow_succ, mul_assoc, C_eps_mul_C_eps, mul_zero]
        intro h
        have := congrArg (fun c => c k) h
        simp at this
    ·
      obtain ⟨k', hk'mem, hk'⟩ : ∃ k' ∈ nκ.support, k' ≠ k := by
        by_contra h
        apply hsupp
        intro k' hk'
        by_contra hkk
        exact h ⟨k', hk', fun e => hkk (Finset.mem_singleton.2 e)⟩
      rw [Finsupp.prod, Finset.prod_eq_zero hk'mem (by rw [ite_eq_right hk', zero_pow (Finsupp.mem_support_iff.1 hk'mem)]),
        ite_eq_right]
      intro h
      rw [h, Finsupp.mem_support_iff, Finsupp.single_eq_of_ne hk'] at hk'mem
      exact hk'mem rfl
  rw [hY]
  simp only [hsplit]
  have hk1 : (Finsupp.single k 1 : κ →₀ ℕ) ≠ 0 := by simp
  clear_value nτ nκ
  clear hY hn hnτ hnκ hsplit
  split_ifs <;> simp_all [coeff_monomial, coeff_mul_C, eq_comm (a := (0 : κ →₀ ℕ))]

omit [Fintype σ] in

/--
@isnad1 id=eq.0h6v.s10.a2ceea481bb2 from=translated src=- shape=1459618b vocab=73c73b36
-/
theorem coeff_theta (k : κ) (g : MvPowerSeries (τ ⊕ κ) R) (m : τ →₀ ℕ) :
    coeff m (theta k g) = TrivSqZeroExt.inl (coeff (m.sumElim 0) g) +
      (coeff (m.sumElim (Finsupp.single k 1)) g) • DualNumber.eps := by
  classical
  have hne : m.sumElim (0 : κ →₀ ℕ) ≠ m.sumElim (Finsupp.single k 1) := by
    intro h
    have := congrArg (fun c => c (Sum.inr k)) h
    simp at this
  rw [theta_apply, coeff_subst (hasSubst_ak k),
    finsum_eq_sum_of_support_subset (s := {m.sumElim 0, m.sumElim (Finsupp.single k 1)})]
  · rw [Finset.sum_pair hne, coeff_prod_ak, coeff_prod_ak, ite_eq_left rfl, ite_eq_right hne.symm, ite_eq_left rfl]
    rw [Algebra.smul_def, mul_one, TrivSqZeroExt.algebraMap_eq_inl]
  · intro n hn
    rw [Function.mem_support, coeff_prod_ak] at hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    rw [not_or] at h
    rw [ite_eq_right h.1, ite_eq_right h.2, smul_zero] at hn
    exact hn rfl

omit [Fintype σ] [Fintype κ] in
/--
@isnad1 id=eq.0h5v.s8.554f0912962f from=translated src=- shape=4cdbaeb8 vocab=02456708
-/
theorem coeff_pderiv (Q : MvPolynomial σ R) (i : σ) (n : σ →₀ ℕ) :
    MvPolynomial.coeff n (MvPolynomial.pderiv i Q) = ((n i + 1 : ℕ) : R) * MvPolynomial.coeff (n + Finsupp.single i 1) Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = n + Finsupp.single i 1
    · subst hs
      rw [ite_eq_left (add_tsub_cancel_right _ _), ite_eq_left rfl, Finsupp.add_apply, Finsupp.single_eq_same, mul_comm]
    · rw [ite_eq_right hs, mul_zero]
      split_ifs with h
      · have hsi : s i = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hne))).symm
        rw [hsi, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq => simp only [map_add, MvPolynomial.coeff_add, hp, hq, mul_add]

open Classical in

noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f => Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

omit [Fintype κ] in
/--
@isnad1 id=iff.0h3v.s7.cab3be80a9dd from=translated src=- shape=ccbf4f66 vocab=27bedb89
-/
theorem mem_lowDeg {N : ℕ} (n : σ →₀ ℕ) : n ∈ lowDeg σ N ↔ n.degree ≤ N := by
  classical
  rw [lowDeg, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_image.2 ⟨fun s => n s, Fintype.mem_piFinset.2 fun s => Finset.mem_range.2
      (Nat.lt_succ_of_le ((Finsupp.le_degree s n).trans h)), ?_⟩, h⟩
    ext s; simp

noncomputable def truncTot (N : ℕ) (f : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ n ∈ lowDeg σ N, MvPolynomial.monomial n (coeff n f)

omit [Fintype κ] in
/--
@isnad1 id=eq.0h5v.s8.aeab4bc65647 from=translated src=- shape=19669241 vocab=2cf5dbfe
-/
theorem coeff_truncTot (N : ℕ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    MvPolynomial.coeff n (truncTot N f) = if n.degree ≤ N then coeff n f else 0 := by
  classical
  rw [truncTot, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [mem_lowDeg]

omit [Fintype κ] in
/--
@isnad1 id=le.0h4v.s6.f9a4df4279ea from=translated src=- shape=9f80556e vocab=beceb03b
-/
theorem le_order_sub_truncTot (N : ℕ) (f : MvPowerSeries σ R) :
    ((N + 1 : ℕ) : ℕ∞) ≤ (f - (truncTot N f : MvPowerSeries σ R)).order :=
  nat_le_order fun n hn => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTot, ite_eq_left (by omega), sub_self]

omit [Fintype κ] in
/--
@isnad1 id=le.1h6v.s9.163ea408e76d from=translated src=- shape=e3f168a8 vocab=c869a684
-/
theorem le_order_Df_sub (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ), coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (N : ℕ) (i : σ) :
    (N : ℕ∞) ≤ (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order :=
  nat_le_order fun n hn => by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_pderiv, coeff_truncTot, hDf,
      ite_eq_left (by rw [map_add, Finsupp.degree_single]; omega), sub_self]

omit [Fintype σ] in
/--
@isnad1 id=le.1h6v.s7.f5b8083e7c8f from=translated src=- shape=d2394a46 vocab=ef57eb4f
-/
theorem one_le_iInf_order (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) : (1 : ℕ∞) ≤ ⨅ i, (Gfam A B i).order := by
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, constantCoeff_Gfam A hA B]

omit [Fintype σ] [Fintype κ] in
/--
@isnad1 id=le.1h4v.s7.cfa957135bc0 from=translated src=- shape=7bde0477 vocab=83443275
-/
theorem one_le_iInf_order' (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) :
    (1 : ℕ∞) ≤ ⨅ i, (A i).order := by
  refine le_iInf fun i => nat_le_order fun d hd => ?_
  have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  rw [this, coeff_zero_eq_constantCoeff_apply, hA]

omit [Fintype σ] [Fintype κ] in
/--
@isnad1 id=eq.0h4v.s8.8e4127dd5e9e from=translated src=- shape=cf202ec5 vocab=5dd2e975
-/
theorem degree_sumElim (m : τ →₀ ℕ) (c : κ →₀ ℕ) : (m.sumElim c).degree = m.degree + c.degree := by
  rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

/--
@isnad1 id=eq.2h9v.s9.386c2b4eff7d from=translated src=- shape=1b2439e2 vocab=a5084529
-/
theorem coeff_subst_eq_coeff_aeval (f : MvPowerSeries σ R) (A : σ → MvPowerSeries τ R)
    (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R) (N : ℕ) (e : τ ⊕ κ →₀ ℕ)
    (he : e.degree ≤ N) :
    coeff e (subst (Gfam A B) f) = coeff e (MvPolynomial.aeval (Gfam A B) (truncTot N f)) := by
  have hG := hasSubst_Gfam A hA B
  have hdec : subst (Gfam A B) f = subst (Gfam A B) (truncTot N f : MvPowerSeries σ R) +
      subst (Gfam A B) (f - (truncTot N f : MvPowerSeries σ R)) := by
    rw [← subst_add hG]; congr 1; ring
  rw [hdec, subst_coe, map_add]
  convert add_zero _
  apply coeff_of_lt_order
  calc ((e.degree : ℕ) : ℕ∞) < (N + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_of_le he
    _ ≤ (f - (truncTot N f : MvPowerSeries σ R)).order := le_order_sub_truncTot N f
    _ ≤ (⨅ i, (Gfam A B i).order) * (f - (truncTot N f : MvPowerSeries σ R)).order :=
        le_mul_of_one_le_left (by simp) (one_le_iInf_order A hA B)
    _ ≤ _ := le_order_subst hG _

/--
@isnad1 id=and.3h11v.s11.4c31df9acd00 from=translated src=- shape=50ca68a7 vocab=a36aaaf4
-/
theorem coeff_theta_subst (k : κ) (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ), coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) (c : κ →₀ ℕ) (hc : c.degree ≤ 1) :
    coeff (m.sumElim c) (subst (Gfam A B) f) =
      coeff (m.sumElim c) (MvPolynomial.aeval (Gfam A B) (truncTot (m.degree + 1) f)) ∧
    coeff m (subst A f) = coeff m (MvPolynomial.aeval A (truncTot (m.degree + 1) f)) ∧
    coeff m (∑ i, B i k * subst A (Df i)) =
      coeff m (∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i (truncTot (m.degree + 1) f))) := by
  set N := m.degree + 1 with hN
  have hAs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  refine ⟨coeff_subst_eq_coeff_aeval f A hA B N _ (by rw [degree_sumElim]; omega), ?_, ?_⟩
  ·
    have hdec : subst A f = subst A (truncTot N f : MvPowerSeries σ R) +
        subst A (f - (truncTot N f : MvPowerSeries σ R)) := by
      rw [← subst_add hAs]; congr 1; ring
    rw [hdec, subst_coe, map_add]
    convert add_zero _
    apply coeff_of_lt_order
    calc ((m.degree : ℕ) : ℕ∞) < (N + 1 : ℕ) := by exact_mod_cast (by omega : m.degree < N + 1)
      _ ≤ (f - (truncTot N f : MvPowerSeries σ R)).order := le_order_sub_truncTot N f
      _ ≤ (⨅ i, (A i).order) * (f - (truncTot N f : MvPowerSeries σ R)).order :=
          le_mul_of_one_le_left (by simp) (one_le_iInf_order' A hA)
      _ ≤ _ := le_order_subst hAs _
  ·
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdec : subst A (Df i) = subst A (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R) +
        subst A (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)) := by
      rw [← subst_add hAs]; congr 1; ring
    rw [hdec, subst_coe, mul_add, map_add]
    convert add_zero _
    apply coeff_of_lt_order
    calc ((m.degree : ℕ) : ℕ∞) < N := by exact_mod_cast (by omega : m.degree < N)
      _ ≤ (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order := le_order_Df_sub f Df hDf N i
      _ ≤ (⨅ i, (A i).order) * (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R)).order :=
          le_mul_of_one_le_left (by simp) (one_le_iInf_order' A hA)
      _ ≤ (subst A (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R))).order := le_order_subst hAs _
      _ ≤ (B i k).order + (subst A (Df i - (MvPolynomial.pderiv i (truncTot N f) : MvPowerSeries σ R))).order :=
          le_add_self
      _ ≤ _ := le_order_mul

/--
@isnad1 id=eq.2h10v.s10.8a40fd3e6945 from=translated src=- shape=3aaeee82 vocab=31644051
-/
theorem main1 (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ), coeff m (Df i) = ((m i + 1 : ℕ) : R) * coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) (k : κ) :
    coeff (m.sumElim (Finsupp.single k 1)) (subst (Gfam A B) f) = coeff m (∑ i, B i k * subst A (Df i)) := by
  classical
  obtain ⟨h1, -, h3⟩ := coeff_theta_subst k f Df hDf A hA B m (Finsupp.single k 1) (by rw [Finsupp.degree_single])
  rw [h1, h3]
  set P := truncTot (m.degree + 1) f
  set W := ∑ i, B i k * MvPolynomial.aeval A (MvPolynomial.pderiv i P) with hW

  have key := coeff_theta k (MvPolynomial.aeval (Gfam A B) P : MvPowerSeries (τ ⊕ κ) R) m
  rw [MvPolynomial.comp_aeval_apply, show (fun i => theta k (Gfam A B i)) =
      fun i => map (algebraMap R D) (A i) + C DualNumber.eps * map (algebraMap R D) (B i k) from
        funext fun i => theta_Gfam k A B i, aeval_dual, ← hW, map_add, coeff_map, coeff_C_mul, coeff_map] at key
  have := congrArg TrivSqZeroExt.snd key
  simp [TrivSqZeroExt.algebraMap_eq_inl, DualNumber.snd_eps, DualNumber.fst_eps] at this
  exact this.symm

end S17TY

universe u v w x

/--
@isnad1 id=eq.2h10v.s10.6d8f97dd75b0 from=translated src=- shape=262e7bab vocab=d80c71d3
-/
theorem solution
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (Df i) = ((m i + 1 : ℕ) : R) * MvPowerSeries.coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) (k : κ) :
    MvPowerSeries.coeff (m.sumElim (Finsupp.single k 1))
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (∑ i : σ, B i k * MvPowerSeries.subst A (Df i)) :=
  S17TY.main1 f Df hDf A hA B m k
