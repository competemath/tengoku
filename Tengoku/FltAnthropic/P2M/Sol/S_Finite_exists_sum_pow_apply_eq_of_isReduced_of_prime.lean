import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Finite_exists_sum_pow_apply_eq_of_isReduced_of_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Finite_exists_sum_pow_apply_eq_of_isReduced_of_prime

set_option autoImplicit false

open Finset

namespace ResidualTrace

/--
@isnad1 id=ex.4h4v.s10.d4e48a822c76 from=translated src=- shape=e3a4f86e vocab=b129196b
-/
theorem finiteField_exists_sum_pow_apply_eq {F : Type*} [Field F] [Finite F]
    (τ : F ≃+* F) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1) (hτ1 : τ ≠ 1)
    (c : F) (hτc : τ c = c) :
    ∃ t : F, ∑ i ∈ Finset.range ℓ, (τ ^ i) t = c := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hord : orderOf τ = ℓ := orderOf_eq_prime hτℓ hτ1
  have hfin : IsOfFinOrder τ := by
    rw [← orderOf_pos_iff, hord]; exact hℓ.pos
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  let G : Subgroup (F ≃+* F) := Subgroup.zpowers τ
  haveI : Fintype G := Fintype.ofFinite G
  let F₀ : Subfield F := FixedPoints.subfield G F

  have hcG : ∀ g : G, g • c = c := by
    rintro ⟨g, hg⟩
    change g c = c
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hnat : ∀ m : ℕ, (τ ^ m) c = c := fun m => by
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ']
        show τ ((τ ^ m) c) = c
        rw [ih, hτc]
    rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
    · exact_mod_cast hnat m
    · rw [zpow_neg, zpow_natCast]
      apply (τ ^ m).injective
      rw [hnat m]
      exact (τ ^ m).apply_symm_apply c
  let c₀ : F₀ := ⟨c, fun g => hcG g⟩
  haveI : Finite F₀ := Finite.of_injective (fun x : F₀ => (x : F)) Subtype.val_injective
  haveI : Algebra.IsSeparable F₀ F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨t, ht⟩ := Algebra.trace_surjective F₀ F c₀
  refine ⟨t, ?_⟩
  have h1 := trace_eq_sum_automorphisms (K := F₀) (L := F) t
  rw [ht] at h1
  change c = _ at h1
  rw [h1]

  rw [← (FixedPoints.toAlgAutMulEquiv G F).toEquiv.sum_comp]
  rw [← (finEquivZPowers hfin).sum_comp]
  rw [← hord, ← Fin.sum_univ_eq_sum_range (fun i => (τ ^ i) t) (orderOf τ)]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [finEquivZPowers_apply]
  rfl

end ResidualTrace

namespace ResidualTrace

variable {R : Type*} [CommRing R]

def pull (τ : R ≃+* R) (I : MaximalSpectrum R) : MaximalSpectrum R :=
  ⟨I.asIdeal.comap (τ : R →+* R), Ideal.comap_isMaximal_of_surjective _ τ.surjective⟩

/--
@isnad1 id=iff.0h4v.s8.36e48d9ebaae from=translated src=- shape=3d5718ca vocab=7bc6b593
-/
theorem mem_pull (τ : R ≃+* R) (I : MaximalSpectrum R) (x : R) :
    x ∈ (pull τ I).asIdeal ↔ τ x ∈ I.asIdeal := Iff.rfl

/--
@isnad1 id=iff.0h5v.s9.c20fa2b06b3c from=translated src=- shape=fafc94e1 vocab=73ac62c9
-/
theorem mem_pull_iterate (τ : R ≃+* R) (I : MaximalSpectrum R) (k : ℕ) (x : R) :
    x ∈ ((pull τ)^[k] I).asIdeal ↔ (τ ^ k) x ∈ I.asIdeal := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', mem_pull, ih, pow_succ]
    rfl

/--
@isnad1 id=eq.1h4v.s9.470b112072c6 from=translated src=- shape=5eddd063 vocab=54d5f141
-/
theorem pull_iterate_eq_self_of_pow_eq_one (τ : R ≃+* R) (ℓ : ℕ) (hτℓ : τ ^ ℓ = 1)
    (I : MaximalSpectrum R) : (pull τ)^[ℓ] I = I := by
  apply MaximalSpectrum.ext
  ext x
  rw [mem_pull_iterate, hτℓ]
  rfl

def push (τ : R ≃+* R) (I : MaximalSpectrum R) (k : ℕ) :
    R ⧸ ((pull τ)^[k] I).asIdeal →+* R ⧸ I.asIdeal :=
  Ideal.quotientMap I.asIdeal ((τ ^ k : R ≃+* R) : R →+* R) fun x hx => by
    rw [Ideal.mem_comap]
    exact (mem_pull_iterate τ I k x).1 hx

/--
@isnad1 id=eq.0h5v.s10.78efe65fc1ce from=translated src=- shape=95a3c542 vocab=e5e442b5
-/
theorem push_mk (τ : R ≃+* R) (I : MaximalSpectrum R) (k : ℕ) (x : R) :
    push τ I k (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ ((τ ^ k) x) :=
  Ideal.quotientMap_mk

def resAut (τ : R ≃+* R) (I : MaximalSpectrum R) (h : pull τ I = I) :
    R ⧸ I.asIdeal ≃+* R ⧸ I.asIdeal :=
  Ideal.quotientEquiv I.asIdeal I.asIdeal τ (by
    rw [Ideal.map_comap_of_equiv]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap]
      have : τ (τ.symm x) ∈ I.asIdeal := by rw [RingEquiv.apply_symm_apply]; exact hx
      have h2 := (mem_pull τ I (τ.symm x)).2 this
      rwa [h] at h2
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have h2 : τ.symm x ∈ (pull τ I).asIdeal := by rw [h]; exact hx
      rw [mem_pull, RingEquiv.apply_symm_apply] at h2
      exact h2)

/--
@isnad1 id=eq.1h4v.s10.fab8d398fa15 from=translated src=- shape=51dfc340 vocab=ecab9af9
-/
theorem resAut_mk (τ : R ≃+* R) (I : MaximalSpectrum R) (h : pull τ I = I) (x : R) :
    resAut τ I h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (τ x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

/--
@isnad1 id=eq.1h5v.s11.fd7d68d9d7e0 from=translated src=- shape=0b286796 vocab=06655c1d
-/
theorem resAut_pow_mk (τ : R ≃+* R) (I : MaximalSpectrum R) (h : pull τ I = I) (k : ℕ) (x : R) :
    (resAut τ I h ^ k) (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ ((τ ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    show (resAut τ I h ^ k) (resAut τ I h (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ ((τ ^ k) (τ x))
    rw [resAut_mk, ih]

/--
@isnad1 id=eq.1h4v.s9.6199b7846447 from=translated src=- shape=d7c554a8 vocab=b9e2ca6e
-/
theorem pow_apply_of_fix (τ : R ≃+* R) {c : R} (hτc : τ c = c) (k : ℕ) : (τ ^ k) c = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    show τ ((τ ^ k) c) = c
    rw [ih, hτc]

/--
@isnad1 id=eq.0h3v.s9.386237070318 from=translated src=- shape=a67cc65e vocab=533f972f
-/
theorem equivPi_apply [IsArtinianRing R] [IsReduced R] (x : R) (I : MaximalSpectrum R) :
    IsArtinianRing.equivPi R x I = Ideal.Quotient.mk I.asIdeal x := by
  have : IsArtinianRing.equivPi R x = x • (1 : (J : MaximalSpectrum R) → R ⧸ J.asIdeal) := by
    have h1 : IsArtinianRing.equivPi R x = IsArtinianRing.equivPi R (x • 1) := by
      rw [smul_eq_mul, mul_one]
    rw [h1, map_smul, map_one]
  rw [this, Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]

def orb (φ : MaximalSpectrum R → MaximalSpectrum R) (I : MaximalSpectrum R) : Set (MaximalSpectrum R) :=
  {J | ∃ i : ℕ, φ^[i] I = J}

/--
@isnad1 id=eq.2h4v.s6.4df8bdff525a from=translated src=- shape=3aa4bc17 vocab=baff063e
-/
theorem orb_apply_eq (φ : MaximalSpectrum R → MaximalSpectrum R) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hper : ∀ I, φ^[ℓ] I = I) (I : MaximalSpectrum R) : orb φ (φ I) = orb φ I := by
  ext J
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + 1, by rw [Function.iterate_succ_apply]⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i + (ℓ - 1), ?_⟩
    rw [← Function.iterate_succ_apply, show (i + (ℓ - 1)).succ = i + ℓ by omega,
      Function.iterate_add_apply, hper]

/--
@isnad1 id=eq.2h5v.s6.50c30c4eeb81 from=translated src=- shape=933669c3 vocab=baff063e
-/
theorem orb_iterate_eq (φ : MaximalSpectrum R → MaximalSpectrum R) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hper : ∀ I, φ^[ℓ] I = I) (I : MaximalSpectrum R) (k : ℕ) : orb φ (φ^[k] I) = orb φ I := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', orb_apply_eq φ ℓ hℓ hper, ih]

noncomputable def rep (φ : MaximalSpectrum R → MaximalSpectrum R) (I : MaximalSpectrum R) :
    MaximalSpectrum R :=
  @Classical.epsilon _ ⟨I⟩ (orb φ I)

/--
@isnad1 id=mem.0h3v.s5.a78537a04f11 from=translated src=- shape=a6b010ec vocab=c9959f40
-/
theorem rep_mem (φ : MaximalSpectrum R → MaximalSpectrum R) (I : MaximalSpectrum R) :
    rep φ I ∈ orb φ I :=
  @Classical.epsilon_spec _ (orb φ I) ⟨I, 0, rfl⟩

/--
@isnad1 id=eq.2h5v.s6.7257ac5f1542 from=translated src=- shape=1aeb9bb4 vocab=cc39eac6
-/
theorem rep_iterate (φ : MaximalSpectrum R → MaximalSpectrum R) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hper : ∀ I, φ^[ℓ] I = I) (I : MaximalSpectrum R) (k : ℕ) : rep φ (φ^[k] I) = rep φ I := by
  unfold rep
  have h := orb_iterate_eq φ ℓ hℓ hper I k
  simp only [h]

/--
@isnad1 id=ex.4h4v.s10.e320f3c7849d from=translated src=- shape=1b944548 vocab=d72e1dd4
-/
theorem exists_sum_pow_apply_eq_of_isReduced [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hτc : τ c = c) :
    ∃ u : R, ∑ i ∈ Finset.range ℓ, (τ ^ i) u = c := by
  classical
  let φ : MaximalSpectrum R → MaximalSpectrum R := pull τ
  have hper : ∀ I, φ^[ℓ] I = I := pull_iterate_eq_self_of_pow_eq_one τ ℓ hτℓ

  have hfixed : ∀ I : MaximalSpectrum R, (h : φ I = I) →
      ∃ t : R ⧸ I.asIdeal, ∑ i ∈ range ℓ, (resAut τ I h ^ i) t = Ideal.Quotient.mk _ c := by
    intro I h
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Finite (R ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    apply finiteField_exists_sum_pow_apply_eq (resAut τ I h) ℓ hℓ
    · apply RingEquiv.ext
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [resAut_pow_mk, hτℓ]
      rfl
    · intro h1
      have hstab : ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal := fun x hx =>
        (mem_pull τ I x).1 (by rw [show pull τ I = I from h]; exact hx)
      obtain ⟨x, hx⟩ := hmax I.asIdeal I.isMaximal hstab
      apply hx
      rw [← Ideal.Quotient.eq, ← resAut_mk τ I h, h1]
      rfl
    · rw [resAut_mk, hτc]

  let r : ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun I =>
    if h : φ I = I then Classical.choose (hfixed I h)
    else if rep φ I = I then Ideal.Quotient.mk _ c else 0
  let e := IsArtinianRing.equivPi R
  let u : R := e.symm r
  have hu : ∀ I, Ideal.Quotient.mk I.asIdeal u = r I := by
    intro I
    rw [← equivPi_apply]
    show e (e.symm r) I = r I
    rw [AlgEquiv.apply_symm_apply]
  refine ⟨u, ?_⟩

  apply e.injective
  funext I
  rw [equivPi_apply, equivPi_apply, map_sum]
  by_cases h : φ I = I
  ·
    have : ∀ i, Ideal.Quotient.mk I.asIdeal ((τ ^ i) u) = (resAut τ I h ^ i) (r I) := fun i => by
      rw [← hu I, resAut_pow_mk]
    simp_rw [this]
    have hr : r I = Classical.choose (hfixed I h) := dite_eq_left h
    rw [hr]
    exact Classical.choose_spec (hfixed I h)
  ·
    have hmin : Function.minimalPeriod φ I = ℓ := by
      have hdvd : Function.minimalPeriod φ I ∣ ℓ := Function.IsPeriodicPt.minimalPeriod_dvd (hper I)
      rcases (Nat.dvd_prime hℓ).1 hdvd with h1 | h1
      · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1) h
      · exact h1

    have hfree : ∀ i, φ (φ^[i] I) ≠ φ^[i] I := by
      intro i hi
      have hmem : I ∈ Function.periodicPts φ := Function.mk_mem_periodicPts hℓ.pos (hper I)
      have h1 : Function.minimalPeriod φ (φ^[i] I) = ℓ := by
        rw [Function.minimalPeriod_apply_iterate hmem, hmin]
      have h2 : Function.minimalPeriod φ (φ^[i] I) = 1 :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.2 hi
      rw [h2] at h1
      exact hℓ.one_lt.ne h1

    have hstep : ∀ i, Ideal.Quotient.mk I.asIdeal ((τ ^ i) u) =
        if φ^[i] I = rep φ I then Ideal.Quotient.mk I.asIdeal c else 0 := by
      intro i
      rw [← push_mk τ I i u, hu]
      have hr : r (φ^[i] I) = if rep φ (φ^[i] I) = φ^[i] I then Ideal.Quotient.mk _ c else 0 :=
        dite_eq_right (hfree i)
      rw [hr, rep_iterate φ ℓ hℓ.pos hper]
      by_cases h2 : rep φ I = φ^[i] I
      · rw [ite_eq_left h2, ite_eq_left h2.symm, push_mk, pow_apply_of_fix τ hτc]
      · rw [ite_eq_right h2, ite_eq_right (Ne.symm h2), map_zero]
    simp_rw [hstep]

    obtain ⟨j, hj⟩ := rep_mem φ I
    have hj' : φ^[j % ℓ] I = rep φ I := by
      rw [Function.IsPeriodicPt.iterate_mod_apply (hper I)]; exact hj
    rw [Finset.sum_eq_single (j % ℓ)]
    · rw [ite_eq_left hj']
    · intro i hi hne
      rw [ite_eq_right]
      intro hi'
      apply hne
      rw [← hj'] at hi'
      exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by rw [hmin]; exact Finset.mem_range.1 hi) (by rw [hmin]; exact Nat.mod_lt _ hℓ.pos)).1 hi'
    · intro hj''
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hℓ.pos)) hj''

end ResidualTrace

/--
@isnad1 id=ex.4h4v.s10.e320f3c7849d from=translated src=- shape=1b944548 vocab=d72e1dd4
-/
theorem solution
    {R : Type*} [CommRing R] [Finite R] [IsReduced R]
    (τ : R ≃+* R) (ℓ : ℕ) (hℓ : ℓ.Prime) (hτℓ : τ ^ ℓ = 1)
    (hmax : ∀ m : Ideal R, m.IsMaximal → (∀ x ∈ m, τ x ∈ m) → ∃ x, τ x - x ∉ m)
    (c : R) (hτc : τ c = c) :
    ∃ u : R, ∑ i ∈ Finset.range ℓ, (τ ^ i) u = c :=
  ResidualTrace.exists_sum_pow_apply_eq_of_isReduced τ ℓ hℓ hτℓ hmax c hτc
