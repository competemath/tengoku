import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CuspSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four

namespace KbManinAnyChar

open Module

section Orbits

variable {X : Type*} (σ : Equiv.Perm X)

abbrev Orb : Type _ := MulAction.orbitRel.Quotient (Subgroup.zpowers σ) X

def orbQ (x : X) : Orb σ := Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) x

/--
@isnad1 id=surjecti.0h2v.s3.3c2a7065797e from=translated src=- shape=101200ff vocab=dedd92fb
-/
theorem orbQ_surjective : Function.Surjective (orbQ σ) := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

/--
@isnad1 id=eq.0h3v.s5.a0d55b867c5d from=translated src=- shape=410532cd vocab=f58a6200
-/
theorem orbQ_apply_perm (x : X) : orbQ σ (σ x) = orbQ σ x := by
  apply Quotient.sound
  show σ x ∈ MulAction.orbit (Subgroup.zpowers σ) x
  exact ⟨⟨σ, Subgroup.mem_zpowers σ⟩, rfl⟩

/--
@isnad1 id=eq.0h2v.s5.ec83354539ec from=translated src=- shape=df7b1cd0 vocab=68652228
-/
theorem natCard_fixedBy_eq (τ : Equiv.Perm X) :
    Nat.card (MulAction.fixedBy X τ) = Nat.card {x // τ x = x} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [MulAction.mem_fixedBy])

/--
@isnad1 id=eq.0h1v.s5.6aae27f6f7d9 from=translated src=- shape=5ee510fe vocab=ec29d037
-/
theorem natCard_fixedBy_one : Nat.card (MulAction.fixedBy X (1 : Equiv.Perm X)) = Nat.card X := by
  rw [natCard_fixedBy_eq]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by simp)

/--
@isnad1 id=eq.0h2v.s6.0e05a970ccea from=translated src=- shape=8863df48 vocab=3223f7b9
-/
theorem sum_range_orderOf_natCard_fixedBy [Finite X] :
    ∑ i ∈ Finset.range (orderOf σ), Nat.card (MulAction.fixedBy X (σ ^ i)) =
      Nat.card (Orb σ) * orderOf σ := by
  classical
  letI := Fintype.ofFinite X
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Subgroup.zpowers σ) X
  rw [Fintype.card_zpowers] at hB
  rw [← Nat.card_eq_fintype_card] at hB
  rw [← Fin.sum_univ_eq_sum_range (fun i => Nat.card (MulAction.fixedBy X (σ ^ i))) (orderOf σ)]
  rw [← hB]
  rw [← Fintype.sum_equiv (finEquivZPowers hfin)
    (fun i : Fin (orderOf σ) => Nat.card (MulAction.fixedBy X (σ ^ (i : ℕ))))
    (fun a => Fintype.card (MulAction.fixedBy X a))]
  intro i
  rw [finEquivZPowers_apply, Nat.card_eq_fintype_card]
  rfl

/--
@isnad1 id=eq.1h2v.s6.6e4228eec825 from=translated src=- shape=e2d04be7 vocab=035d39b7
-/
theorem two_mul_natCard_orb [Finite X] (h2 : σ ^ 2 = 1) :
    2 * Nat.card (Orb σ) = Nat.card X + Nat.card {x // σ x = x} := by
  have hsum := sum_range_orderOf_natCard_fixedBy σ
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  · have hσ : σ = 1 := orderOf_eq_one_iff.mp h1
    subst hσ
    rw [h1, Finset.sum_range_one, pow_zero, natCard_fixedBy_one, mul_one] at hsum
    rw [← natCard_fixedBy_eq, natCard_fixedBy_one, hsum]; ring
  · rw [h2', Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, natCard_fixedBy_one,
      natCard_fixedBy_eq] at hsum
    omega

/--
@isnad1 id=eq.1h2v.s6.11c59b8abc53 from=translated src=- shape=ed30acff vocab=035d39b7
-/
theorem three_mul_natCard_orb [Finite X] (h3 : σ ^ 3 = 1) :
    3 * Nat.card (Orb σ) = Nat.card X + 2 * Nat.card {x // σ x = x} := by
  have hsum := sum_range_orderOf_natCard_fixedBy σ
  have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
  · have hσ : σ = 1 := orderOf_eq_one_iff.mp h1
    subst hσ
    rw [h1, Finset.sum_range_one, pow_zero, natCard_fixedBy_one, mul_one] at hsum
    rw [← natCard_fixedBy_eq, natCard_fixedBy_one, hsum]; ring
  · have hsq : Nat.card (MulAction.fixedBy X (σ ^ 2)) = Nat.card {x // σ x = x} := by
      rw [natCard_fixedBy_eq]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      constructor
      · intro hx
        have h3x : (σ ^ 3) x = x := by rw [h3]; rfl
        calc σ x = σ ((σ ^ 2) x) := by rw [hx]
          _ = (σ ^ 3) x := by simp [pow_succ]
          _ = x := h3x
      · intro hx
        simp [sq, hx]
    rw [h3', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      natCard_fixedBy_one, natCard_fixedBy_eq, hsq] at hsum
    omega

/--
@isnad1 id=eq.1h3v.s6.ff0175c092d1 from=translated src=- shape=19e59312 vocab=c2a39c44
-/
theorem apply_apply_of_sq (h2 : σ ^ 2 = 1) (x : X) : σ (σ x) = x := by
  have e := congrArg (fun τ : Equiv.Perm X => τ x) h2
  simpa [sq, Equiv.Perm.mul_apply] using e

/--
@isnad1 id=eq.1h3v.s6.d8d0c994f60a from=translated src=- shape=08abca7f vocab=c2a39c44
-/
theorem apply_three_of_cube (h3 : σ ^ 3 = 1) (x : X) : σ (σ (σ x)) = x := by
  have e := congrArg (fun τ : Equiv.Perm X => τ x) h3
  simpa [pow_succ, Equiv.Perm.mul_apply] using e

/--
@isnad1 id=iff.1h4v.s8.9b4ee31d1c14 from=translated src=- shape=a3819ade vocab=7e24cef4
-/
theorem mem_orbit_iff_of_cube (h3 : σ ^ 3 = 1) (x y : X) :
    y ∈ MulAction.orbit (Subgroup.zpowers σ) x ↔ y = x ∨ y = σ x ∨ y = σ (σ x) := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hk : σ ^ k = σ ^ (k % 3) := by exact_mod_cast zpow_eq_zpow_emod' k h3
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h1 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    show (σ ^ k) x = x ∨ (σ ^ k) x = σ x ∨ (σ ^ k) x = σ (σ x)
    rw [hk]
    interval_cases (k % 3)
    · left; simp
    · right; left; simp
    · right; right
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply]
  · rintro (h | h | h) <;> rw [h]
    · exact MulAction.mem_orbit_self x
    · exact MulAction.mem_orbit x (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ)
    · have : σ (σ x) = (⟨σ * σ, Subgroup.mul_mem _ (Subgroup.mem_zpowers σ)
          (Subgroup.mem_zpowers σ)⟩ : Subgroup.zpowers σ) • x := rfl
      rw [this]
      exact MulAction.mem_orbit x _

end Orbits

section ManinRel

variable (K : Type*) [Field K] {X : Type*} (σ₂ σ₃ : Equiv.Perm X)

def relSpace : Submodule K (X → K) where
  carrier := {m | (∀ x, m x + m (σ₂ x) = 0) ∧ (∀ x, m x + m (σ₃ x) + m (σ₃ (σ₃ x)) = 0) ∧
    (∀ x, σ₂ x = x → m x = 0) ∧ ∀ x, σ₃ x = x → m x = 0}
  zero_mem' := ⟨fun x => by simp, fun x => by simp, fun x _ => by simp, fun x _ => by simp⟩
  add_mem' := by
    rintro m n ⟨hm2, hm3, hm2', hm3'⟩ ⟨hn2, hn3, hn2', hn3'⟩
    refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Pi.add_apply]; linear_combination hm2 x + hn2 x
    · simp only [Pi.add_apply]; linear_combination hm3 x + hn3 x
    · simp only [Pi.add_apply, hm2' x hx, hn2' x hx, add_zero]
    · simp only [Pi.add_apply, hm3' x hx, hn3' x hx, add_zero]
  smul_mem' := by
    rintro c m ⟨hm2, hm3, hm2', hm3'⟩
    refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, hm2 x, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, ← mul_add, hm3 x, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, hm2' x hx, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul, hm3' x hx, mul_zero]

variable {K σ₂ σ₃} in
/--
@isnad1 id=iff.0h5v.s8.9ed70eccc40e from=translated src=- shape=8d43fdec vocab=ab00a3f7
-/
theorem mem_relSpace {m : X → K} :
    m ∈ relSpace K σ₂ σ₃ ↔
      (∀ x, m x + m (σ₂ x) = 0) ∧ (∀ x, m x + m (σ₃ x) + m (σ₃ (σ₃ x)) = 0) ∧
        (∀ x, σ₂ x = x → m x = 0) ∧ ∀ x, σ₃ x = x → m x = 0 :=
  Iff.rfl

variable [Fintype X]

noncomputable def orbFun : ((Orb σ₂ → K) × (Orb σ₃ → K)) →ₗ[K] Module.Dual K (X → K) :=
  LinearMap.mk₂ K
    (fun ab m => ∑ x, m x * (ab.1 (orbQ σ₂ x) + ab.2 (orbQ σ₃ x)))
    (fun ab ab' m => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun c ab m => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun ab m m' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun c ab m => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring)

/--
@isnad1 id=eq.0h6v.s10.ab1340f50088 from=translated src=- shape=fa636e5c vocab=391413cb
-/
theorem orbFun_apply (ab : (Orb σ₂ → K) × (Orb σ₃ → K)) (m : X → K) :
    orbFun K σ₂ σ₃ ab m = ∑ x, m x * (ab.1 (orbQ σ₂ x) + ab.2 (orbQ σ₃ x)) := rfl

/--
@isnad1 id=eq.4h5v.s7.446ff95515b3 from=translated src=- shape=00436976 vocab=d090c34e
-/
theorem sum_mul_eq_zero_of_sq (h2 : σ₂ ^ 2 = 1) (m c : X → K)
    (hrel : ∀ x, m x + m (σ₂ x) = 0) (hfix : ∀ x, σ₂ x = x → m x = 0)
    (hc : ∀ x, c (σ₂ x) = c x) : ∑ x, m x * c x = 0 := by
  refine Finset.sum_ninvolution σ₂ ?_ ?_ (fun x => Finset.mem_univ _) (apply_apply_of_sq σ₂ h2)
  · intro x; rw [hc, ← add_mul, hrel x, zero_mul]
  · intro x hx heq
    exact hx (by rw [hfix x heq, zero_mul])

/--
@isnad1 id=eq.4h5v.s8.87863103a252 from=translated src=- shape=a9653d61 vocab=d090c34e
-/
theorem sum_mul_eq_zero_of_cube (h3 : σ₃ ^ 3 = 1) (m c : X → K)
    (hrel : ∀ x, m x + m (σ₃ x) + m (σ₃ (σ₃ x)) = 0) (hfix : ∀ x, σ₃ x = x → m x = 0)
    (hc : ∀ x, c (σ₃ x) = c x) : ∑ x, m x * c x = 0 := by
  classical
  refine Finset.sum_cancels_of_partition_cancels (MulAction.orbitRel (Subgroup.zpowers σ₃) X) ?_
  intro x _
  have hset : (Finset.univ.filter fun a => (MulAction.orbitRel (Subgroup.zpowers σ₃) X) a x) =
      ({x, σ₃ x, σ₃ (σ₃ x)} : Finset X) := by
    ext a
    rw [Finset.mem_filter, MulAction.orbitRel_apply, mem_orbit_iff_of_cube σ₃ h3]
    simp
  rw [hset]
  by_cases hfx : σ₃ x = x
  · rw [hfx, hfx]
    rw [show ({x, x, x} : Finset X) = {x} by simp, Finset.sum_singleton, hfix x hfx, zero_mul]
  · have h12 : x ≠ σ₃ x := fun h => hfx h.symm
    have h23 : σ₃ x ≠ σ₃ (σ₃ x) := fun h => hfx (σ₃.injective h).symm
    have h13 : x ≠ σ₃ (σ₃ x) := by
      intro h
      apply hfx
      have := congrArg σ₃ h
      rw [apply_three_of_cube σ₃ h3 x] at this
      exact this
    rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton, hc (σ₃ x), hc x]
    linear_combination (c x) * hrel x

/--
@isnad1 id=le.2h4v.s9.837aa3d25612 from=translated src=- shape=65417024 vocab=5e676950
-/
theorem relSpace_le_dualCoannihilator (h2 : σ₂ ^ 2 = 1) (h3 : σ₃ ^ 3 = 1) :
    relSpace K σ₂ σ₃ ≤ (LinearMap.range (orbFun K σ₂ σ₃)).dualCoannihilator := by
  intro m hm
  rw [mem_relSpace] at hm
  obtain ⟨hm2, hm3, hm2', hm3'⟩ := hm
  rw [Submodule.mem_dualCoannihilator]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [orbFun_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_mul_eq_zero_of_sq K σ₂ h2 m (fun x => a (orbQ σ₂ x)) hm2 hm2'
      (fun x => by simp only [orbQ_apply_perm]),
    sum_mul_eq_zero_of_cube K σ₃ h3 m (fun x => b (orbQ σ₃ x)) hm3 hm3'
      (fun x => by simp only [orbQ_apply_perm]), add_zero]

def Connected (σ₂ σ₃ : Equiv.Perm X) (K : Type*) : Prop :=
  ∀ f : X → K, (∀ x, f (σ₂ x) = f x) → (∀ x, f (σ₃ x) = f x) → ∀ x y, f x = f y

/--
@isnad1 id=le.1h4v.s10.ed93654bacf1 from=translated src=- shape=ef877981 vocab=f5197780
-/
theorem ker_orbFun_le (hconn : Connected σ₂ σ₃ K) :
    LinearMap.ker (orbFun K σ₂ σ₃) ≤
      LinearMap.range (LinearMap.toSpanSingleton K _
        ((fun _ => (1 : K), fun _ => (-1 : K)) : (Orb σ₂ → K) × (Orb σ₃ → K))) := by
  classical
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  have hpt : ∀ x, a (orbQ σ₂ x) + b (orbQ σ₃ x) = 0 := by
    intro x₀
    have := LinearMap.congr_fun hab (fun x => if x = x₀ then 1 else 0)
    rw [orbFun_apply, LinearMap.zero_apply] at this
    simpa [ite_mul, Finset.sum_ite_eq'] using this
  have hinv2 : ∀ x, a (orbQ σ₂ (σ₂ x)) = a (orbQ σ₂ x) := fun x => by rw [orbQ_apply_perm]
  have hinv3 : ∀ x, a (orbQ σ₂ (σ₃ x)) = a (orbQ σ₂ x) := fun x => by
    have e1 := hpt x
    have e2 := hpt (σ₃ x)
    rw [orbQ_apply_perm] at e2
    linear_combination e2 - e1
  have hconst := hconn (fun x => a (orbQ σ₂ x)) hinv2 hinv3
  rw [LinearMap.mem_range]
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨0, ?_⟩
    ext y
    · exact (hX.false (orbQ_surjective σ₂ y).choose).elim
    · exact (hX.false (orbQ_surjective σ₃ y).choose).elim
  refine ⟨a (orbQ σ₂ x₀), ?_⟩
  ext y
  · obtain ⟨x, rfl⟩ := orbQ_surjective σ₂ y
    simp [LinearMap.toSpanSingleton_apply, hconst x x₀]
  · obtain ⟨x, rfl⟩ := orbQ_surjective σ₃ y
    have := hpt x
    simp only [LinearMap.toSpanSingleton_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      mul_neg, mul_one]
    have hc : a (orbQ σ₂ x₀) = a (orbQ σ₂ x) := hconst x₀ x
    rw [hc]; linear_combination (-1 : K) * this

/--
@isnad1 id=le.3h4v.s9.376e22515e39 from=translated src=- shape=802f587e vocab=0c239d54
-/
theorem relSpace_rank_bound (h2 : σ₂ ^ 2 = 1) (h3 : σ₃ ^ 3 = 1) (hconn : Connected σ₂ σ₃ K) :
    6 * Module.finrank K (relSpace K σ₂ σ₃) + 3 * Nat.card {x // σ₂ x = x}
        + 4 * Nat.card {x // σ₃ x = x} ≤ 6 + Nat.card X := by
  classical
  have hO2 := two_mul_natCard_orb σ₂ h2
  have hO3 := three_mul_natCard_orb σ₃ h3
  have hco := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (LinearMap.range (orbFun K σ₂ σ₃))
  have hV : Module.finrank K (relSpace K σ₂ σ₃) ≤
      Module.finrank K (LinearMap.range (orbFun K σ₂ σ₃)).dualCoannihilator :=
    Submodule.finrank_mono (relSpace_le_dualCoannihilator K σ₂ σ₃ h2 h3)
  have hXK : Module.finrank K (X → K) = Nat.card X := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
  have hrn := LinearMap.finrank_range_add_finrank_ker (orbFun K σ₂ σ₃)
  have hdom : Module.finrank K ((Orb σ₂ → K) × (Orb σ₃ → K)) =
      Nat.card (Orb σ₂) + Nat.card (Orb σ₃) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hker : Module.finrank K (LinearMap.ker (orbFun K σ₂ σ₃)) ≤ 1 := by
    refine (Submodule.finrank_mono (ker_orbFun_le K σ₂ σ₃ hconn)).trans ?_
    refine (LinearMap.finrank_range_le _).trans ?_
    rw [Module.finrank_self]
  omega

end ManinRel

section Potential

open Matrix Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup OnePoint
open ModularCurve
open scoped MatrixGroups

/--
@isnad1 id=iff.0h1v.s9.fad887a13a81 from=translated src=- shape=293c59ed vocab=df08b8ec
-/
theorem smul_infty_eq_iff (γ : SL(2, ℤ)) :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = ∞ ↔ γ 1 0 = 0 := by
  rw [OnePoint.smul_infty_eq_self_iff]
  simp

/--
@isnad1 id=eq.1h1v.s7.653d2259f6ca from=translated src=- shape=7853b900 vocab=5ddcb8c4
-/
theorem trace_sq_of_lower_left (γ : SL(2, ℤ)) (h : γ 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  have hdet := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [γ.det_coe, h, mul_zero, sub_zero] at hdet
  rw [Matrix.trace_fin_two]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> norm_num

/--
@isnad1 id=eq.0h2v.s8.cf74d555a17f from=translated src=- shape=302a2d1d vocab=ff003392
-/
theorem trace_conj (σ δ : SL(2, ℤ)) :
    ((σ⁻¹ * δ * σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      (δ : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

/--
@isnad1 id=le.0h0v.s6.54c3d99af40e from=translated src=- shape=75a72874 vocab=c09264ec
-/
theorem trace_S_sq_le : ((S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 := by
  rw [Matrix.trace_fin_two, ModularGroup.coe_S]
  simp

/--
@isnad1 id=le.0h0v.s7.7f096ef28277 from=translated src=- shape=6742a9ba vocab=5a117ff4
-/
theorem trace_ST_sq_le : ((S * T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 := by
  rw [Matrix.trace_fin_two, coe_mul, ModularGroup.coe_S, ModularGroup.coe_T]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h0v.s7.99ae1f1a53f0 from=translated src=- shape=f5255fcb vocab=36f00b27
-/
theorem neg_one_lower : (-1 : SL(2, ℤ)) 1 0 = 0 := by simp

/--
@isnad1 id=eq.0h0v.s7.97e2d842587a from=translated src=- shape=5fe560b9 vocab=3f90bb67
-/
theorem T_inv_lower : (T⁻¹ : SL(2, ℤ)) 1 0 = 0 := by rw [coe_T_inv]; rfl

/--
@isnad1 id=eq.0h0v.s6.4ad26957fe5c from=translated src=- shape=669cc5ff vocab=3e6f04eb
-/
theorem T_lower : (T : SL(2, ℤ)) 1 0 = 0 := by rw [coe_T]; rfl

/--
@isnad1 id=eq.0h0v.s8.3085e60fa5e2 from=translated src=- shape=5caeb2af vocab=e8357168
-/
theorem S_inv_eq : (S : SL(2, ℤ))⁻¹ = S * (-1) :=
  inv_eq_of_mul_eq_one_right (by decide)

/--
@isnad1 id=eq.0h0v.s8.2345512d3c8a from=translated src=- shape=238a76cc vocab=1284dd92
-/
theorem ST_inv_mul_S : (S * T : SL(2, ℤ))⁻¹ * S = T⁻¹ := by group

/--
@isnad1 id=eq.0h0v.s9.5bd08a6a3fa8 from=translated src=- shape=d2d4033a vocab=61b891dc
-/
theorem ST_cube : (S * T : SL(2, ℤ)) * (S * T) * (S * T) = -1 := by decide

/--
@isnad1 id=eq.0h0v.s9.48ae03f1ebc8 from=translated src=- shape=628455ea vocab=5fb1867b
-/
theorem ST_inv_mul_ST_inv : (S * T : SL(2, ℤ))⁻¹ * (S * T)⁻¹ = S * T * (-1) := by
  calc ((S * T : SL(2, ℤ))⁻¹ * (S * T)⁻¹)
      = (S * T) * ((S * T) * (S * T) * (S * T))⁻¹ := by group
    _ = S * T * (-1) := by rw [ST_cube]; simp

/--
@isnad1 id=mem.0h1v.s8.dd309ee66a53 from=translated src=- shape=47a2a55e vocab=3a18f723
-/
theorem neg_one_mem_Gamma0 (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by simp [Gamma0_mem]

variable (Γ : Subgroup SL(2, ℤ))

def IsEllParHom {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0

section EllParHoms

variable (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]

def ellParHoms : Submodule R (Additive Γ →+ A) where
  carrier := {φ | IsEllParHom Γ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ _ + ψ _ = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ _ = 0
    rw [hφ γ hγ, smul_zero]

end EllParHoms

variable {K : Type*} [Field K]

open Classical in

noncomputable def Phi (φ : Additive Γ →+ K) (g : SL(2, ℤ)) : K :=
  if h : g ∈ Γ then φ (Additive.ofMul ⟨g, h⟩) else 0

/--
@isnad1 id=eq.1h4v.s12.b7567f0b6d17 from=translated src=- shape=03ea6da7 vocab=04eeffd7
-/
theorem Phi_of_mem (φ : Additive Γ →+ K) {g : SL(2, ℤ)} (h : g ∈ Γ) :
    Phi Γ φ g = φ (Additive.ofMul ⟨g, h⟩) := dite_eq_left h

/--
@isnad1 id=eq.2h5v.s10.27a4afc090e2 from=translated src=- shape=1f70924a vocab=0beb4ed9
-/
theorem Phi_mul (φ : Additive Γ →+ K) {g h : SL(2, ℤ)} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    Phi Γ φ (g * h) = Phi Γ φ g + Phi Γ φ h := by
  rw [Phi_of_mem Γ φ (mul_mem hg hh), Phi_of_mem Γ φ hg, Phi_of_mem Γ φ hh, ← map_add]
  rfl

/--
@isnad1 id=eq.0h3v.s10.3aa697fc6ddb from=translated src=- shape=8e5ef9a9 vocab=1db5936a
-/
theorem Phi_one (φ : Additive Γ →+ K) : Phi Γ φ 1 = 0 := by
  rw [Phi_of_mem Γ φ (one_mem Γ)]
  exact map_zero φ

/--
@isnad1 id=eq.1h4v.s10.731915fa74ea from=translated src=- shape=831e5c7f vocab=9e5cc170
-/
theorem Phi_inv (φ : Additive Γ →+ K) {g : SL(2, ℤ)} (hg : g ∈ Γ) :
    Phi Γ φ g⁻¹ = -Phi Γ φ g := by
  have h := Phi_mul Γ φ (inv_mem hg) hg
  rw [inv_mul_cancel, Phi_one] at h
  linear_combination -h

/--
@isnad1 id=eq.0h5v.s13.a129891d50dc from=translated src=- shape=8c60a56b vocab=56c6cde2
-/
theorem Phi_add (φ ψ : Additive Γ →+ K) (g : SL(2, ℤ)) :
    Phi Γ (φ + ψ) g = Phi Γ φ g + Phi Γ ψ g := by
  unfold Phi
  split_ifs <;> simp

/--
@isnad1 id=eq.0h5v.s13.846dfc339ebe from=translated src=- shape=d3b40665 vocab=200ee671
-/
theorem Phi_smul (c : K) (φ : Additive Γ →+ K) (g : SL(2, ℤ)) :
    Phi Γ (c • φ) g = c * Phi Γ φ g := by
  unfold Phi
  split_ifs <;> simp

/--
@isnad1 id=eq.3h4v.s10.1f3a28a669eb from=translated src=- shape=98cab472 vocab=8fdd81db
-/
theorem Phi_ellPar {φ : Additive Γ →+ K} (hφ : IsEllParHom Γ φ) {g : SL(2, ℤ)} (hg : g ∈ Γ)
    (htr : (g : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4) : Phi Γ φ g = 0 := by
  rw [Phi_of_mem Γ φ hg]
  exact hφ ⟨g, hg⟩ htr

variable (N : ℕ)

noncomputable def rep (C : CuspSpace N) : OnePoint ℚ := (CuspSpace.mk_surjective N C).choose

/--
@isnad1 id=eq.0h2v.s3.2ffe86a96f47 from=translated src=- shape=6ddf6d3e vocab=c8b18564
-/
theorem mk_rep (C : CuspSpace N) : CuspSpace.mk N (rep N C) = C :=
  (CuspSpace.mk_surjective N C).choose_spec

/--
@isnad1 id=ex.0h2v.s9.b46f46f4e16f from=translated src=- shape=4b58ada0 vocab=b8bbb3db
-/
theorem exists_gam (a : OnePoint ℚ) :
    ∃ γ ∈ Gamma0 N, mapGL ℚ γ • rep N (CuspSpace.mk N a) = a :=
  CuspSpace.mk_eq_mk_iff.mp (mk_rep N _).symm

noncomputable def gam (a : OnePoint ℚ) : SL(2, ℤ) := (exists_gam N a).choose

/--
@isnad1 id=mem.0h2v.s7.da873378228f from=translated src=- shape=d448662b vocab=92cb30e3
-/
theorem gam_mem (a : OnePoint ℚ) : gam N a ∈ Gamma0 N := (exists_gam N a).choose_spec.1

/--
@isnad1 id=eq.0h2v.s9.3cff7e22cbcd from=translated src=- shape=5ed99e23 vocab=b86e7e13
-/
theorem gam_smul (a : OnePoint ℚ) : mapGL ℚ (gam N a) • rep N (CuspSpace.mk N a) = a :=
  (exists_gam N a).choose_spec.2

noncomputable def Gpot (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (a : OnePoint ℚ) : K :=
  Phi (Gamma0 N) φ (gam N a) + c (CuspSpace.mk N a)

variable {N}

/--
@isnad1 id=eq.3h5v.s11.76c944f9be8d from=translated src=- shape=bdc49ee2 vocab=5874e3fb
-/
theorem Phi_eq_zero_of_fix {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 N) {r : OnePoint ℚ} (hfix : mapGL ℚ δ • r = r) :
    Phi (Gamma0 N) φ δ = 0 := by
  classical
  obtain ⟨σ, rfl⟩ := OnePoint.exists_mem_SL2 ℤ r
  have h10 : (σ⁻¹ * δ * σ) 1 0 = 0 := by
    rw [← smul_infty_eq_iff, map_mul, map_mul, mul_smul, mul_smul, hfix, ← mul_smul, ← map_mul,
      inv_mul_cancel, map_one, one_smul]
  have htr := trace_sq_of_lower_left _ h10
  rw [trace_conj] at htr
  exact Phi_ellPar _ hφ hδ htr.le

/--
@isnad1 id=eq.2h6v.s11.af44e88b70ca from=translated src=- shape=cb5103e9 vocab=8e3d13c0
-/
theorem Gpot_smul {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    (c : CuspSpace N → K) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (a : OnePoint ℚ) :
    Gpot N φ c (mapGL ℚ γ • a) = Phi (Gamma0 N) φ γ + Gpot N φ c a := by
  have hmk : CuspSpace.mk N (mapGL ℚ γ • a) = CuspSpace.mk N a := CuspSpace.mk_smul hγ a
  unfold Gpot
  rw [hmk]
  have ha := gam_smul N a
  have hb := gam_smul N (mapGL ℚ γ • a)
  rw [hmk] at hb
  have hfix : mapGL ℚ ((gam N (mapGL ℚ γ • a))⁻¹ * γ * gam N a) • rep N (CuspSpace.mk N a) =
      rep N (CuspSpace.mk N a) := by
    rw [map_mul, map_mul, mul_smul, mul_smul, ha, map_inv, inv_smul_eq_iff]
    exact hb.symm
  have h0 := Phi_eq_zero_of_fix hφ
    (mul_mem (mul_mem (inv_mem (gam_mem N _)) hγ) (gam_mem N a)) hfix
  rw [Phi_mul _ _ (mul_mem (inv_mem (gam_mem N _)) hγ) (gam_mem N a),
    Phi_mul _ _ (inv_mem (gam_mem N _)) hγ, Phi_inv _ _ (gam_mem N _)] at h0
  linear_combination (-1 : K) * h0

variable (N)

noncomputable def Ppot (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (g : SL(2, ℤ)) : K :=
  Gpot N φ c (mapGL ℚ g • ∞)

variable {N}

/--
@isnad1 id=eq.2h6v.s10.e9009f8cefef from=translated src=- shape=3e3c5c34 vocab=d139c675
-/
theorem Ppot_mul_left {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    (c : CuspSpace N → K) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (g : SL(2, ℤ)) :
    Ppot N φ c (γ * g) = Phi (Gamma0 N) φ γ + Ppot N φ c g := by
  unfold Ppot
  rw [map_mul, mul_smul, Gpot_smul hφ c hγ]

/--
@isnad1 id=eq.1h6v.s10.462691c11dfd from=translated src=- shape=ff6b0f5a vocab=6fbc4636
-/
theorem Ppot_mul_right (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (g : SL(2, ℤ))
    {k : SL(2, ℤ)} (hk : k 1 0 = 0) : Ppot N φ c (g * k) = Ppot N φ c g := by
  unfold Ppot
  rw [map_mul, mul_smul, (smul_infty_eq_iff k).mpr hk]

variable (N)

noncomputable def nSL (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (g : SL(2, ℤ)) : K :=
  Ppot N φ c g⁻¹ - Ppot N φ c (g⁻¹ * S)

noncomputable def nX (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K)
    (x : SL(2, ℤ) ⧸ Gamma0 N) : K :=
  nSL N φ c (Quotient.out x)

variable {N}

/--
@isnad1 id=eq.1h5v.s10.e8fc092e6069 from=translated src=- shape=8b667c47 vocab=fc797637
-/
theorem nX_mk {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    (c : CuspSpace N → K) (g : SL(2, ℤ)) :
    nX N φ c (g : SL(2, ℤ) ⧸ Gamma0 N) = nSL N φ c g := by
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 N) g
  unfold nX
  rw [hγ]
  unfold nSL
  rw [_root_.mul_inv_rev, mul_assoc, Ppot_mul_left hφ c (inv_mem γ.2),
    Ppot_mul_left hφ c (inv_mem γ.2)]
  ring

/--
@isnad1 id=eq.0h5v.s10.5719721998d8 from=translated src=- shape=0ebb03d4 vocab=673cb657
-/
theorem nSL_two_term (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (g : SL(2, ℤ)) :
    nSL N φ c (S * g) + nSL N φ c g = 0 := by
  unfold nSL
  rw [_root_.mul_inv_rev, inv_mul_cancel_right, S_inv_eq, ← mul_assoc,
    Ppot_mul_right φ c _ neg_one_lower]
  ring

/--
@isnad1 id=eq.0h5v.s11.7c59579f9f7e from=translated src=- shape=e6ff5837 vocab=a032b746
-/
theorem nSL_three_term (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K) (g : SL(2, ℤ)) :
    nSL N φ c g + nSL N φ c (S * T * g) + nSL N φ c (S * T * (S * T * g)) = 0 := by
  unfold nSL
  have e1 : (S * T * g)⁻¹ = g⁻¹ * (S * T)⁻¹ := by group
  have e2 : (S * T * (S * T * g))⁻¹ = g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹ := by group
  have hA : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * S) = Ppot N φ c g⁻¹ := by
    rw [mul_assoc, ST_inv_mul_S, Ppot_mul_right φ c _ T_inv_lower]
  have hB : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹ * S) = Ppot N φ c (g⁻¹ * (S * T)⁻¹) := by
    rw [mul_assoc _ _ S, ST_inv_mul_S, Ppot_mul_right φ c _ T_inv_lower]
  have hC : Ppot N φ c (g⁻¹ * (S * T)⁻¹ * (S * T)⁻¹) = Ppot N φ c (g⁻¹ * S) := by
    rw [mul_assoc g⁻¹, ST_inv_mul_ST_inv, ← mul_assoc, Ppot_mul_right φ c _ neg_one_lower,
      ← mul_assoc, Ppot_mul_right φ c _ T_lower]
  rw [e1, e2, hA, hB, hC]
  ring

/--
@isnad1 id=eq.2h5v.s10.2610f16abd51 from=translated src=- shape=5dc480e8 vocab=0c492d83
-/
theorem nSL_fix_two {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    (c : CuspSpace N → K) {g : SL(2, ℤ)} (hg : g⁻¹ * S * g ∈ Gamma0 N) : nSL N φ c g = 0 := by
  unfold nSL
  have e : g⁻¹ * S = (g⁻¹ * S * g) * g⁻¹ := by group
  rw [e, Ppot_mul_left hφ c hg, Phi_ellPar _ hφ hg (by rw [trace_conj]; exact trace_S_sq_le)]
  ring

/--
@isnad1 id=eq.2h5v.s10.14d9e3758d60 from=translated src=- shape=94cab59c vocab=47c661da
-/
theorem nSL_fix_three {φ : Additive (Gamma0 N) →+ K} (hφ : IsEllParHom (Gamma0 N) φ)
    (c : CuspSpace N → K) {g : SL(2, ℤ)} (hg : g⁻¹ * (S * T) * g ∈ Gamma0 N) :
    nSL N φ c g = 0 := by
  unfold nSL
  have e : g⁻¹ * S * T = (g⁻¹ * (S * T) * g) * g⁻¹ := by group
  rw [← Ppot_mul_right φ c (g⁻¹ * S) T_lower, e, Ppot_mul_left hφ c hg,
    Phi_ellPar _ hφ hg (by rw [trace_conj]; exact trace_ST_sq_le)]
  ring

/--
@isnad1 id=eq.0h7v.s13.cb52760fc81b from=translated src=- shape=f0abb4c4 vocab=7da8d084
-/
theorem nX_add (φ ψ : Additive (Gamma0 N) →+ K) (c d : CuspSpace N → K) (x : SL(2, ℤ) ⧸ Gamma0 N) :
    nX N (φ + ψ) (c + d) x = nX N φ c x + nX N ψ d x := by
  simp only [nX, nSL, Ppot, Gpot, Phi_add, Pi.add_apply]
  ring

/--
@isnad1 id=eq.0h6v.s13.c1ebb828ccc4 from=translated src=- shape=be976647 vocab=870ba5db
-/
theorem nX_smul (r : K) (φ : Additive (Gamma0 N) →+ K) (c : CuspSpace N → K)
    (x : SL(2, ℤ) ⧸ Gamma0 N) :
    nX N (r • φ) (r • c) x = r * nX N φ c x := by
  simp only [nX, nSL, Ppot, Gpot, Phi_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable (N)

abbrev X : Type := SL(2, ℤ) ⧸ Gamma0 N

noncomputable def sig2 : Equiv.Perm (X N) := MulAction.toPerm (S : SL(2, ℤ))

noncomputable def sig3 : Equiv.Perm (X N) := MulAction.toPerm (S * T : SL(2, ℤ))

/--
@isnad1 id=eq.0h2v.s8.2ac9493bb23a from=translated src=- shape=0505a220 vocab=b885a0b9
-/
theorem sig2_apply (x : X N) : sig2 N x = (S : SL(2, ℤ)) • x := rfl

/--
@isnad1 id=eq.0h2v.s8.af6eabc79266 from=translated src=- shape=c496295e vocab=b17da3e1
-/
theorem sig3_apply (x : X N) : sig3 N x = (S * T : SL(2, ℤ)) • x := rfl

/--
@isnad1 id=eq.0h2v.s8.d737d73c6ab6 from=translated src=- shape=78a49373 vocab=cf6fc8d5
-/
theorem mk_neg_one_mul (g : SL(2, ℤ)) : ((-1 * g : SL(2, ℤ)) : X N) = (g : X N) := by
  rw [neg_one_mul, ← mul_neg_one]
  symm
  rw [QuotientGroup.eq, inv_mul_cancel_left]
  exact neg_one_mem_Gamma0 N

/--
@isnad1 id=eq.0h1v.s5.9479f0519d76 from=translated src=- shape=794702db vocab=b1bff592
-/
theorem sig2_sq : sig2 N ^ 2 = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [sq, Equiv.Perm.mul_apply, sig2_apply, sig2_apply, MulAction.Quotient.smul_mk,
      MulAction.Quotient.smul_mk, Equiv.Perm.one_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      show (S : SL(2, ℤ)) * S = -1 by decide, mk_neg_one_mul]

/--
@isnad1 id=eq.0h1v.s5.5f966d4e8850 from=translated src=- shape=794702db vocab=1cea034a
-/
theorem sig3_cube : sig3 N ^ 3 = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sig3_apply, sig3_apply, sig3_apply,
      MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk,
      Equiv.Perm.one_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
      ST_cube, mk_neg_one_mul]

omit [Field K] in

/--
@isnad1 id=connecte.0h2v.s3.95d6d58eec69 from=translated src=- shape=6486a3eb vocab=0a9ce2fe
-/
theorem connected : Connected (sig2 N) (sig3 N) K := by
  intro f h2 h3 x y
  have hS : ∀ x : X N, f ((S : SL(2, ℤ)) • x) = f x := h2
  have hSinv : ∀ x : X N, f ((S : SL(2, ℤ))⁻¹ • x) = f x := fun x => by
    rw [← hS ((S : SL(2, ℤ))⁻¹ • x), smul_inv_smul]
  have hT : ∀ x : X N, f ((T : SL(2, ℤ)) • x) = f x := fun x => by
    have : (T : SL(2, ℤ)) = S⁻¹ * (S * T) := by group
    rw [this, mul_smul, hSinv]
    exact h3 x
  have key : ∀ k : SL(2, ℤ), k ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) →
      ∀ x : X N, f (k • x) = f x := by
    intro k hk
    refine Subgroup.closure_induction (p := fun k _ => ∀ x : X N, f (k • x) = f x)
      ?_ ?_ ?_ ?_ hk
    · intro k hk x
      rcases hk with rfl | rfl
      · exact hS x
      · exact hT x
    · intro x; rw [one_smul]
    · intro a b _ _ ha hb x
      rw [mul_smul, ha, hb]
    · intro a _ ha x
      rw [← ha (a⁻¹ • x), smul_inv_smul]
  have hall : ∀ k : SL(2, ℤ), ∀ x : X N, f (k • x) = f x := fun k =>
    key k (SpecialLinearGroup.SL2Z_generators ▸ Subgroup.mem_top k)
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction y using QuotientGroup.induction_on with
    | H g' =>
      have e1 := hall g ((1 : SL(2, ℤ)) : X N)
      have e2 := hall g' ((1 : SL(2, ℤ)) : X N)
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at e1 e2
      rw [e1, e2]

variable (K)

abbrev W : Type _ := ↥(ellParHoms (Gamma0 N) K K) × (CuspSpace N → K)

noncomputable def theta : W K N →ₗ[K] (X N → K) where
  toFun w := fun x => nX N (w.1 : Additive (Gamma0 N) →+ K) w.2 x
  map_add' w w' := by
    ext x
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Pi.add_apply, nX_add]
  map_smul' r w := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, nX_smul]

/--
@isnad1 id=eq.0h4v.s17.99284d7a34eb from=translated src=- shape=5d33b0e0 vocab=8d7340b8
-/
theorem theta_apply (w : W K N) (x : X N) :
    theta K N w x = nX N (w.1 : Additive (Gamma0 N) →+ K) w.2 x := rfl

/--
@isnad1 id=mem.0h3v.s16.69705089eb29 from=translated src=- shape=dc0a549d vocab=81320188
-/
theorem theta_mem (w : W K N) : theta K N w ∈ relSpace K (sig2 N) (sig3 N) := by
  have hφ : IsEllParHom (Gamma0 N) (w.1 : Additive (Gamma0 N) →+ K) := w.1.2
  rw [mem_relSpace]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [sig2_apply, MulAction.Quotient.smul_mk, smul_eq_mul, theta_apply, theta_apply,
        nX_mk hφ, nX_mk hφ, add_comm]
      exact nSL_two_term _ _ g
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [sig3_apply, MulAction.Quotient.smul_mk, smul_eq_mul, sig3_apply,
        MulAction.Quotient.smul_mk, smul_eq_mul, theta_apply, theta_apply, theta_apply,
        nX_mk hφ, nX_mk hφ, nX_mk hφ]
      exact nSL_three_term _ _ g
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      intro hx
      rw [sig2_apply, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hx
      have hmem : g⁻¹ * S * g ∈ Gamma0 N := by
        have := inv_mem hx
        rwa [show ((S * g)⁻¹ * g)⁻¹ = g⁻¹ * S * g by group] at this
      rw [theta_apply, nX_mk hφ]
      exact nSL_fix_two hφ _ hmem
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      intro hx
      rw [sig3_apply, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hx
      have hmem : g⁻¹ * (S * T) * g ∈ Gamma0 N := by
        have := inv_mem hx
        rwa [show ((S * T * g)⁻¹ * g)⁻¹ = g⁻¹ * (S * T) * g by group] at this
      rw [theta_apply, nX_mk hφ]
      exact nSL_fix_three hφ _ hmem

noncomputable def thetaPlus : W K N →ₗ[K] ↥(relSpace K (sig2 N) (sig3 N)) × K :=
  (LinearMap.codRestrict _ (theta K N) (theta_mem K N)).prod
    ((LinearMap.proj (CuspSpace.mk N ∞)).comp (LinearMap.snd K _ _))

/--
@isnad1 id=injectiv.0h2v.s16.02bd86cc1ef1 from=translated src=- shape=f6e86d4a vocab=df20d068
-/
theorem thetaPlus_injective : Function.Injective (thetaPlus K N) := by
  classical
  rw [injective_iff_map_eq_zero]
  rintro ⟨⟨φ, hφmem⟩, c⟩ hw
  have hφ : IsEllParHom (Gamma0 N) φ := hφmem
  have hθx : ∀ x : X N, nX N φ c x = 0 := fun x =>
    congr_arg (fun p : ↥(relSpace K (sig2 N) (sig3 N)) × K => (p.1 : X N → K) x) hw
  have hcinf : c (CuspSpace.mk N ∞) = 0 :=
    congr_arg (fun p : ↥(relSpace K (sig2 N) (sig3 N)) × K => p.2) hw
  have hPS : ∀ h : SL(2, ℤ), Ppot N φ c (h * S) = Ppot N φ c h := fun h => by
    have e := hθx ((h⁻¹ : SL(2, ℤ)) : X N)
    rw [nX_mk hφ, nSL, inv_inv] at e
    linear_combination -e
  have hPT : ∀ h : SL(2, ℤ), Ppot N φ c (h * T) = Ppot N φ c h := fun h =>
    Ppot_mul_right φ c h T_lower
  have key : ∀ k : SL(2, ℤ), k ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) →
      ∀ h : SL(2, ℤ), Ppot N φ c (h * k) = Ppot N φ c h := by
    intro k hk
    refine Subgroup.closure_induction
      (p := fun k _ => ∀ h : SL(2, ℤ), Ppot N φ c (h * k) = Ppot N φ c h) ?_ ?_ ?_ ?_ hk
    · intro k hk h
      rcases hk with rfl | rfl
      · exact hPS h
      · exact hPT h
    · intro h; rw [mul_one]
    · intro a b _ _ ha hb h
      rw [← mul_assoc, hb, ha]
    · intro a _ ha h
      rw [← ha (h * a⁻¹), inv_mul_cancel_right]
  have hconst : ∀ k : SL(2, ℤ), Ppot N φ c k = Ppot N φ c 1 := fun k => by
    have := key k (SpecialLinearGroup.SL2Z_generators ▸ Subgroup.mem_top k) 1
    rwa [one_mul] at this
  have hPhi : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → Phi (Gamma0 N) φ γ = 0 := fun γ hγ => by
    have e := Ppot_mul_left hφ c hγ 1
    rw [mul_one, hconst γ] at e
    linear_combination -e
  have hφ0 : φ = 0 := AddMonoidHom.ext fun a => by
    have e := hPhi ((Additive.toMul a : Gamma0 N) : SL(2, ℤ)) (Additive.toMul a).2
    rw [Phi_of_mem] at e
    exact e
  have hcval : ∀ σ : SL(2, ℤ), c (CuspSpace.mk N (mapGL ℚ σ • ∞)) = Ppot N φ c 1 := fun σ => by
    rw [← hconst σ, Ppot, Gpot, hPhi _ (gam_mem N _), zero_add]
  have hP1 : Ppot N φ c 1 = 0 := by
    rw [← hcinf, ← hcval 1, map_one, one_smul]
  have hc0 : c = 0 := by
    funext C
    obtain ⟨a, rfl⟩ := CuspSpace.mk_surjective N C
    obtain ⟨σ, rfl⟩ := OnePoint.exists_mem_SL2 ℤ a
    rw [hcval σ, hP1, Pi.zero_apply]
  subst hφ0 hc0
  rfl

variable [NeZero N]

scoped instance : Module.Finite K (W K N) :=
  Module.Finite.of_injective (thetaPlus K N) (thetaPlus_injective K N)

scoped instance : Module.Finite K ↥(ellParHoms (Gamma0 N) K K) :=
  Module.Finite.of_injective (LinearMap.inl K _ (CuspSpace N → K)) LinearMap.inl_injective

/--
@isnad1 id=le.0h2v.s14.a02798ebffb6 from=translated src=- shape=6fd7d23c vocab=8dbcb992
-/
theorem finrank_W_le :
    Module.finrank K ↥(ellParHoms (Gamma0 N) K K) + Nat.card (CuspSpace N) ≤
      Module.finrank K ↥(relSpace K (sig2 N) (sig3 N)) + 1 := by
  classical
  letI := Fintype.ofFinite (CuspSpace N)
  have h := LinearMap.finrank_le_finrank_of_injective (thetaPlus_injective K N)
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at h
  exact h

/--
@isnad1 id=le.0h2v.s14.4e8346cb17d7 from=translated src=- shape=0c0bcc93 vocab=04f679ba
-/
theorem engine :
    6 * Module.finrank K ↥(ellParHoms (Gamma0 N) K K)
        + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by
  classical
  letI : Fintype (X N) := Fintype.ofFinite _
  have hR := relSpace_rank_bound K (sig2 N) (sig3 N) (sig2_sq N) (sig3_cube N) (connected N)
  have hW := finrank_W_le K N
  have hidx : (CongruenceSubgroup.Gamma0 N).index = Nat.card (X N) := rfl
  have e2 : Nat.card {x : X N // sig2 N x = x} =
      Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x} := rfl
  have e3 : Nat.card {x : X N // sig3 N x = x} =
      Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
        (ModularGroup.S * ModularGroup.T) • x = x} := rfl
  rw [e2, e3] at hR
  rw [hidx]
  omega

/--
@isnad1 id=le.2h4v.s14.385e825fa9d1 from=translated src=- shape=1c634a84 vocab=c8895ec3
-/
theorem card_le_finrank {ι : Type*} [Fintype ι] (φ : ι → (Additive (Gamma0 N) →+ K))
    (hli : LinearIndependent K φ) (hφ : ∀ i, IsEllParHom (Gamma0 N) (φ i)) :
    Fintype.card ι ≤ Module.finrank K ↥(ellParHoms (Gamma0 N) K K) := by
  let ψ : ι → ↥(ellParHoms (Gamma0 N) K K) := fun i => ⟨φ i, hφ i⟩
  have hψ : LinearIndependent K ψ := by
    apply LinearIndependent.of_comp (Submodule.subtype _)
    exact hli
  exact hψ.fintype_card_le_finrank

end Potential

end KbManinAnyChar
open scoped _root_.P2MW.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.KbManinAnyChar

open scoped MatrixGroups in
/--
@isnad1 id=le.2h4v.s13.d063910ef770 from=translated src=- shape=8638feba vocab=c94f8945
-/
theorem solution (N : ℕ) [NeZero N] (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (φ : ι → (Additive (CongruenceSubgroup.Gamma0 N) →+ K)) (hli : LinearIndependent K φ)
    (hφ : ∀ (i : ι) (γ : CongruenceSubgroup.Gamma0 N),
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ i (Additive.ofMul γ) = 0) :
    6 * Fintype.card ι + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by
  have h1 := KbManinAnyChar.engine K N
  have h2 := KbManinAnyChar.card_le_finrank K N φ hli hφ
  omega
