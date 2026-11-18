import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq

set_option autoImplicit false

namespace S17TY

open MvPowerSeries

variable {R : Type*} [CommRing R] {σ : Type*} {τ : Type*} {κ : Type*}

local notation "D" => DualNumber R

noncomputable def iota (a : MvPowerSeries τ R) : MvPowerSeries (τ ⊕ κ) R :=
  subst (fun t => (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) a

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

theorem constantCoeff_iota (a : MvPowerSeries τ R) (ha : constantCoeff a = 0) :
    constantCoeff (iota (κ := κ) a) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_Xinl (fun t => constantCoeff_X _) ha

variable [Fintype σ] [Fintype κ]

noncomputable def Gfam (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    MvPowerSeries (τ ⊕ κ) R :=
  iota (A i) + ∑ k' : κ, X (Sum.inr k') * iota (B i k')

omit [Fintype σ] in
theorem constantCoeff_Gfam (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (i : σ) : constantCoeff (Gfam A B i) = 0 := by
  rw [Gfam, map_add, constantCoeff_iota _ (hA i), map_sum, zero_add]
  exact Finset.sum_eq_zero fun k' _ => by rw [map_mul, constantCoeff_X, zero_mul]

theorem hasSubst_Gfam (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) : HasSubst (Gfam A B) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_Gfam A hA B)

open Classical in

noncomputable def ak (k : κ) : τ ⊕ κ → MvPowerSeries τ D :=
  Sum.elim (fun t => X t) (fun k' => if k' = k then C DualNumber.eps else 0)

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

noncomputable def a0 : τ ⊕ κ → MvPowerSeries τ R := Sum.elim (fun t => X t) (fun _ => 0)

omit [Fintype σ] [Fintype κ] in
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

omit [Fintype σ] [Fintype κ] in
theorem theta0_apply (g : MvPowerSeries (τ ⊕ κ) R) : theta0 g = subst a0 g := by
  rw [theta0, substAlgHom_apply]

omit [Fintype σ] [Fintype κ] in
theorem theta0_iota (a : MvPowerSeries τ R) : theta0 (iota (κ := κ) a) = a := by
  rw [theta0_apply, iota, subst_comp_subst_apply hasSubst_Xinl hasSubst_a0]
  have : (fun t => subst (a0 (R := R) (κ := κ)) (X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) =
      (X : τ → MvPowerSeries τ R) := by
    funext t; rw [subst_X hasSubst_a0]; rfl
  rw [this]
  exact congrFun subst_self a

omit [Fintype σ] in
theorem theta0_Gfam (A : σ → MvPowerSeries τ R) (B : σ → κ → MvPowerSeries τ R) (i : σ) :
    theta0 (Gfam A B i) = A i := by
  rw [Gfam, map_add, map_sum, theta0_iota]
  convert add_zero _
  refine Finset.sum_eq_zero fun k' _ => ?_
  rw [map_mul, theta0, substAlgHom_X]
  simp [a0]

omit [Fintype σ] [Fintype κ] in
theorem prod_X_pow_eq_monomial' (n : τ →₀ ℕ) :
    (n.prod fun t e => (X t : MvPowerSeries τ R) ^ e) = monomial n 1 :=
  (MvPowerSeries.monomial_one_eq n).symm

open Classical in

noncomputable def lowDeg (σ : Type*) [Fintype σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  ((Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image fun f => Finsupp.equivFunOnFinite.symm f).filter
    fun n => n.degree ≤ N

noncomputable def truncTot (N : ℕ) (f : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ n ∈ lowDeg σ N, MvPolynomial.monomial n (coeff n f)

omit [Fintype σ] [Fintype κ] in
open Classical in

theorem coeff_prod_a0 (m : τ →₀ ℕ) (n : τ ⊕ κ →₀ ℕ) :
    coeff m (n.prod fun u e => a0 (R := R) (κ := κ) u ^ e) = if n = m.sumElim 0 then 1 else 0 := by
  classical
  set nτ : τ →₀ ℕ := n.comapDomain Sum.inl Sum.inl_injective.injOn with hnτ
  set nκ : κ →₀ ℕ := n.comapDomain Sum.inr Sum.inr_injective.injOn with hnκ
  have hn : n = nτ.sumElim nκ := (Finsupp.comapDomain_sumElim_comapDomain n).symm
  have hsplit : (nτ.sumElim nκ = m.sumElim 0 ↔ m = nτ ∧ nκ = 0) := by
    constructor
    · intro h
      exact ⟨Eq.symm (by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inl c Sum.inl_injective.injOn) h),
        by simpa using congrArg (fun c => Finsupp.comapDomain Sum.inr c Sum.inr_injective.injOn) h⟩
    · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  rw [hn, Finsupp.prod_sumElim]
  simp only [Function.comp_def, a0, Sum.elim_inl, Sum.elim_inr, prod_X_pow_eq_monomial']
  have hY : (nκ.prod fun _ e => ((0 : MvPowerSeries τ R)) ^ e) = if nκ = 0 then 1 else 0 := by
    by_cases h0 : nκ = 0
    · rw [h0, ite_eq_left rfl, Finsupp.prod_zero_index]
    · rw [ite_eq_right h0]
      obtain ⟨k', hk'⟩ := Finsupp.support_nonempty_iff.2 h0
      rw [Finsupp.prod, Finset.prod_eq_zero hk' (by rw [zero_pow (Finsupp.mem_support_iff.1 hk')])]
  rw [hY]
  simp only [hsplit]
  clear_value nτ nκ
  clear hY hn hnτ hnκ hsplit
  split_ifs <;> simp_all [coeff_monomial]

omit [Fintype σ] in
theorem coeff_theta0 (g : MvPowerSeries (τ ⊕ κ) R) (m : τ →₀ ℕ) :
    coeff m (theta0 g) = coeff (m.sumElim 0) g := by
  classical
  rw [theta0_apply, coeff_subst hasSubst_a0, finsum_eq_single _ (m.sumElim 0)]
  · rw [coeff_prod_a0, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro n hn
    rw [coeff_prod_a0, ite_eq_right hn, smul_zero]

theorem main0 (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, constantCoeff (A i) = 0) (B : σ → κ → MvPowerSeries τ R)
    (m : τ →₀ ℕ) :
    coeff (m.sumElim 0) (subst (Gfam A B) f) = coeff m (subst A f) := by
  rw [← coeff_theta0, theta0_apply, subst_comp_subst_apply (hasSubst_Gfam A hA B) hasSubst_a0]
  congr 2
  funext i
  rw [← theta0_apply, theta0_Gfam]

end S17TY

universe u v w x

theorem solution
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) :
    MvPowerSeries.coeff (m.sumElim 0)
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (MvPowerSeries.subst A f) :=
  S17TY.main0 f A hA B m
