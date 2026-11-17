import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_binaryFormRepSL_neg_one_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe binaryFormRepSL_neg_one_apply)
namespace UH2
open _root_.HeckeEis

open Module

section Abstract

variable (k : Type*) [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Fintype X] [DecidableEq X]

def extZero (s : Finset X) (M : Type*) [AddCommGroup M] [Module k M] : (↥s → M) →ₗ[k] (X → M) where
  toFun u x := if h : x ∈ s then u ⟨x, h⟩ else 0
  map_add' u v := by
    funext x
    by_cases h : x ∈ s <;> simp [h]
  map_smul' c u := by
    funext x
    by_cases h : x ∈ s <;> simp [h]

variable {k}

omit [Fintype X] in
/--
@isnad1 id=eq.1h6v.s8.5577c0f3fd11 from=translated src=- shape=c23f54c0 vocab=e6c6e919
-/
theorem extZero_apply_mem {s : Finset X} {M : Type*} [AddCommGroup M] [Module k M] (u : ↥s → M)
    {x : X} (h : x ∈ s) : extZero k s M u x = u ⟨x, h⟩ := by
  simp [extZero, h]

omit [Fintype X] in
/--
@isnad1 id=eq.1h6v.s8.113dca1e1d83 from=translated src=- shape=96c66454 vocab=9bc027fd
-/
theorem extZero_apply_not_mem {s : Finset X} {M : Type*} [AddCommGroup M] [Module k M] (u : ↥s → M)
    {x : X} (h : x ∉ s) : extZero k s M u x = 0 := by
  simp [extZero, h]

variable (σ : Equiv.Perm X) (A : V →ₗ[k] V) (Φ : Module.End k (X → V))

omit [Fintype X] [DecidableEq X] in

/--
@isnad1 id=eq.1h9v.s10.9e32d06fda23 from=translated src=- shape=20315484 vocab=253e2fd7
-/
theorem pow_shift_apply (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) (i : ℕ) (f : X → V) (x : X) :
    (Φ ^ i) f x = (A ^ i) (f ((σ ^ i)⁻¹ x)) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', pow_succ', pow_succ', Module.End.mul_apply, hΦ, ih, Module.End.mul_apply, mul_inv_rev,
      Equiv.Perm.mul_apply]

omit [Fintype X] [DecidableEq X] in

/--
@isnad1 id=dvd.4h5v.s6.a9c588bc0442 from=translated src=- shape=fe358452 vocab=77b45f3b
-/
theorem dvd_of_pow_apply_eq {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1) {x : X} (hx : σ x ≠ x) {i : ℕ}
    (hi : (σ ^ i) x = x) : p ∣ i := by
  by_contra hndvd
  have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd).symm
  apply hx
  have key : (σ ^ ((i : ℤ) * Nat.gcdA i p + (p : ℤ) * Nat.gcdB i p)) x = x := by
    rw [zpow_add, zpow_mul, zpow_mul, Equiv.Perm.mul_apply, zpow_natCast, zpow_natCast, hσ, one_zpow,
      Equiv.Perm.one_apply]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hi _
  have hg : ((i : ℤ) * Nat.gcdA i p + (p : ℤ) * Nat.gcdB i p) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  rw [hg, zpow_one] at key
  exact key

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=ne.1h4v.s6.d461c4d00c7a from=translated src=- shape=5cdac23e vocab=c2a39c44
-/
theorem apply_ne_of_pow_apply {x : X} (hx : σ x ≠ x) (i : ℕ) : σ ((σ ^ i) x) ≠ (σ ^ i) x := by
  intro h
  apply hx
  rw [← Equiv.Perm.mul_apply, ← pow_succ', pow_succ, Equiv.Perm.mul_apply] at h
  exact (σ ^ i).injective h

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=ne.1h4v.s6.c17d513953aa from=translated src=- shape=5cdac23e vocab=c646e60c
-/
theorem apply_ne_of_zpow_apply {x : X} (hx : σ x ≠ x) (m : ℤ) : σ ((σ ^ m) x) ≠ (σ ^ m) x := by
  intro h
  apply hx
  rw [← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm, zpow_add_one, Equiv.Perm.mul_apply] at h
  exact (σ ^ m).injective h

noncomputable def rep (x : X) : X :=
  (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers σ) X) x).out

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=ex.0h3v.s5.25b01256d376 from=translated src=- shape=d226b300 vocab=270e23b4
-/
theorem exists_zpow_apply_eq_rep (x : X) : ∃ m : ℤ, (σ ^ m) x = rep σ x := by
  have h : (MulAction.orbitRel (Subgroup.zpowers σ) X) (rep σ x) x := Quotient.mk_out x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨⟨g, hg⟩, hgx⟩ := h
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ⟨m, hgx⟩

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=eq.0h4v.s5.54a3d48de1d8 from=translated src=- shape=ff050232 vocab=270e23b4
-/
theorem rep_zpow_apply (x : X) (m : ℤ) : rep σ ((σ ^ m) x) = rep σ x := by
  unfold rep
  congr 1
  apply Quotient.sound
  change (MulAction.orbitRel (Subgroup.zpowers σ) X) ((σ ^ m) x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨σ ^ m, (Subgroup.zpowers σ).zpow_mem (Subgroup.mem_zpowers σ) m⟩, rfl⟩

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=eq.0h4v.s5.c99c9a1336e4 from=translated src=- shape=ff050232 vocab=1dba4c5c
-/
theorem rep_pow_apply (x : X) (i : ℕ) : rep σ ((σ ^ i) x) = rep σ x := by
  rw [← zpow_natCast]; exact rep_zpow_apply σ x i

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=eq.0h3v.s4.578d9fe599e4 from=translated src=- shape=ad3b2123 vocab=a45321c3
-/
theorem rep_rep (x : X) : rep σ (rep σ x) = rep σ x := by
  obtain ⟨m, hm⟩ := exists_zpow_apply_eq_rep σ x
  rw [← hm, rep_zpow_apply]
  exact hm.symm

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=ne.1h3v.s5.f3dbe708f0b0 from=translated src=- shape=b171046c vocab=b5f29900
-/
theorem apply_rep_ne {x : X} (hx : σ x ≠ x) : σ (rep σ x) ≠ rep σ x := by
  obtain ⟨m, hm⟩ := exists_zpow_apply_eq_rep σ x
  rw [← hm]
  exact apply_ne_of_zpow_apply σ hx m

def moving : Finset X := Finset.univ.filter fun x => σ x ≠ x

noncomputable def freeReps : Finset X := Finset.univ.filter fun x => σ x ≠ x ∧ rep σ x = x

def fixedPts : Finset X := Finset.univ.filter fun x => σ x = x

/--
@isnad1 id=iff.0h3v.s5.256267f91287 from=translated src=- shape=4bb9d6fa vocab=b7a30b3a
-/
theorem mem_moving {x : X} : x ∈ moving σ ↔ σ x ≠ x := by simp [moving]
/--
@isnad1 id=iff.0h3v.s5.c4c1b96ea761 from=translated src=- shape=d6127088 vocab=39ba4a1d
-/
theorem mem_freeReps {x : X} : x ∈ freeReps σ ↔ σ x ≠ x ∧ rep σ x = x := by simp [freeReps]
/--
@isnad1 id=iff.0h3v.s5.c9a145a03e27 from=translated src=- shape=4bb9d6fa vocab=ae9f2f45
-/
theorem mem_fixedPts {x : X} : x ∈ fixedPts σ ↔ σ x = x := by simp [fixedPts]

/--
@isnad1 id=eq.0h2v.s5.38725627eaea from=translated src=- shape=195de23f vocab=ea13753f
-/
theorem card_fixedPts_add_card_moving : (fixedPts σ).card + (moving σ).card = Fintype.card X := by
  rw [fixedPts, moving, Finset.card_filter_add_card_filter_not, Finset.card_univ]

/--
@isnad1 id=eq.3h4v.s6.9fb968f27dfa from=translated src=- shape=0576bc2d vocab=65e61c93
-/
theorem card_fiber {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1) {r : X} (hr : r ∈ freeReps σ) :
    ((moving σ).filter fun a => rep σ a = r).card = p := by
  rw [mem_freeReps] at hr
  have heq : ((moving σ).filter fun a => rep σ a = r) = (Finset.range p).image fun i => (σ ^ i) r := by
    ext a
    simp only [Finset.mem_filter, mem_moving, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨-, hrep⟩
      obtain ⟨m, hm⟩ := exists_zpow_apply_eq_rep σ a
      rw [hrep] at hm
      have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
      refine ⟨((-m) % (p : ℤ)).toNat, ?_, ?_⟩
      · have h1 : ((-m) % (p : ℤ)) < p := Int.emod_lt_of_pos _ hp0
        have h2 : 0 ≤ ((-m) % (p : ℤ)) := Int.emod_nonneg _ hp0.ne'
        omega
      · have h2 : 0 ≤ ((-m) % (p : ℤ)) := Int.emod_nonneg _ hp0.ne'
        rw [← zpow_natCast, Int.toNat_of_nonneg h2, ← zpow_eq_zpow_emod' _ hσ, zpow_neg, ← hm]
        simp
    · rintro ⟨i, -, rfl⟩
      exact ⟨apply_ne_of_pow_apply σ hr.1 i, by rw [rep_pow_apply, hr.2]⟩
  rw [heq, Finset.card_image_of_injOn, Finset.card_range]

  have aux : ∀ i j : ℕ, i ≤ j → j < p → (σ ^ i) r = (σ ^ j) r → i = j := by
    intro i j hij hj e
    rw [← pow_mul_pow_sub σ hij, Equiv.Perm.mul_apply] at e
    have e' : (σ ^ (j - i)) r = r := ((σ ^ i).injective e).symm
    have hdvd := dvd_of_pow_apply_eq σ hp hσ hr.1 e'
    have : j - i = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  intro i hi j hj e
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases le_total i j with h | h
  · exact aux i j h hj e
  · exact (aux j i h hi e.symm).symm

/--
@isnad1 id=eq.2h3v.s6.c63e79a4c6ff from=translated src=- shape=b698552f vocab=2d90a938
-/
theorem card_moving {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1) :
    (moving σ).card = p * (freeReps σ).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := rep σ) (t := freeReps σ)]
  · rw [Finset.sum_congr rfl fun r hr => card_fiber σ hp hσ hr, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro a ha
    rw [Finset.mem_coe, mem_moving] at ha
    rw [Finset.mem_coe, mem_freeReps]
    exact ⟨apply_rep_ne σ ha, rep_rep σ a⟩

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=eq.3h7v.s10.76045e380e62 from=translated src=- shape=25395828 vocab=253e2fd7
-/
theorem shift_pow_eq_one (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hσ : σ ^ p = 1) (hA : A ^ p = 1) :
    Φ ^ p = 1 := by
  refine LinearMap.ext fun f => funext fun x => ?_
  rw [pow_shift_apply σ A Φ hΦ, hA, hσ]
  simp

noncomputable def avg (p : ℕ) : Module.End k (X → V) := ∑ i ∈ Finset.range p, Φ ^ i

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=mem.3h8v.s10.d1a12317c5d3 from=translated src=- shape=b5510ccf vocab=50e6f69e
-/
theorem avg_mem_ker (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hσ : σ ^ p = 1) (hA : A ^ p = 1)
    (g : X → V) : avg Φ p g ∈ LinearMap.ker (Φ - 1) := by
  rw [LinearMap.mem_ker, ← Module.End.mul_apply, avg, mul_geom_sum, shift_pow_eq_one σ A Φ hΦ hσ hA, sub_self,
    LinearMap.zero_apply]

omit [Fintype X] [DecidableEq X] in
/--
@isnad1 id=eq.1h9v.s9.d09b8d0c3acf from=translated src=- shape=4239d776 vocab=4045d3d8
-/
theorem avg_apply (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) (p : ℕ) (g : X → V) (x : X) :
    avg Φ p g x = ∑ i ∈ Finset.range p, (A ^ i) (g ((σ ^ i)⁻¹ x)) := by
  rw [avg, LinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => pow_shift_apply σ A Φ hΦ i g x

/--
@isnad1 id=mem.1h7v.s11.4f6dfcfc6185 from=translated src=- shape=ab6e6e77 vocab=bfdd56ba
-/
theorem extZero_fixed_mem_ker (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x)))
    (u : ↥(fixedPts σ) → LinearMap.ker (A - 1)) :
    extZero k (fixedPts σ) V (fun y => (u y : V)) ∈ LinearMap.ker (Φ - 1) := by
  rw [LinearMap.mem_ker]
  funext x
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, hΦ, Pi.zero_apply, sub_eq_zero]
  by_cases hx : σ x = x
  · have hx' : σ⁻¹ x = x := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hx.symm
    have hmem : x ∈ fixedPts σ := (mem_fixedPts σ).mpr hx
    rw [hx', extZero_apply_mem _ hmem]
    have h2 := (u ⟨x, hmem⟩).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h2
    exact h2
  · have hx' : σ⁻¹ x ∉ fixedPts σ := by
      rw [mem_fixedPts, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      intro h
      apply hx
      calc σ x = σ (σ.symm x) := congrArg (⇑σ) h
        _ = x := Equiv.apply_symm_apply _ _
    have hx2 : x ∉ fixedPts σ := by rw [mem_fixedPts]; exact hx
    rw [extZero_apply_not_mem _ hx', extZero_apply_not_mem _ hx2, map_zero]

noncomputable def compMap (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hσ : σ ^ p = 1) (hA : A ^ p = 1) :
    ((↥(fixedPts σ) → LinearMap.ker (A - 1)) × (↥(freeReps σ) → V)) →ₗ[k] LinearMap.ker (Φ - 1) :=
  LinearMap.codRestrict (LinearMap.ker (Φ - 1))
    (LinearMap.coprod
      (extZero k (fixedPts σ) V ∘ₗ (LinearMap.ker (A - 1)).subtype.compLeft ↥(fixedPts σ))
      (avg Φ p ∘ₗ extZero k (freeReps σ) V))
    (by
      rintro ⟨u, v⟩
      rw [LinearMap.coprod_apply]
      exact Submodule.add_mem _ (extZero_fixed_mem_ker σ A Φ hΦ u) (avg_mem_ker σ A Φ hΦ hσ hA _))

/--
@isnad1 id=eq.4h9v.s10.b0aab2272305 from=translated src=- shape=16b1021d vocab=cf63abc5
-/
theorem avg_extZero_apply_rep (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1)
    (v : ↥(freeReps σ) → V) {r : X} (hr : r ∈ freeReps σ) :
    avg Φ p (extZero k (freeReps σ) V v) r = v ⟨r, hr⟩ := by
  rw [avg_apply σ A Φ hΦ, Finset.sum_eq_single 0]
  · simp [extZero_apply_mem _ hr]
  · intro i hi hi0
    rw [Finset.mem_range] at hi
    have hnot : (σ ^ i)⁻¹ r ∉ freeReps σ := by
      intro hmem
      have h1 := ((mem_freeReps σ).mp hmem).2
      rw [← zpow_natCast, ← zpow_neg, rep_zpow_apply, ((mem_freeReps σ).mp hr).2, eq_comm, zpow_neg,
        zpow_natCast, Equiv.Perm.inv_eq_iff_eq] at h1
      have hdvd := dvd_of_pow_apply_eq σ hp hσ ((mem_freeReps σ).mp hr).1 h1.symm
      exact hi0 (Nat.eq_zero_of_dvd_of_lt hdvd hi)
    rw [extZero_apply_not_mem _ hnot, map_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hp.pos) h

/--
@isnad1 id=injectiv.4h7v.s13.e36bb3e17f4e from=translated src=- shape=ed431644 vocab=27808da0
-/
theorem compMap_injective (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1)
    (hA : A ^ p = 1) : Function.Injective (compMap σ A Φ hΦ hσ hA) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨u, v⟩ huv
  have H : extZero k (fixedPts σ) V (fun y => (u y : V)) + avg Φ p (extZero k (freeReps σ) V v) = 0 := by
    have := congrArg Subtype.val huv
    simp [compMap] at this
    exact this
  have hv : v = 0 := by
    funext ⟨r, hr⟩
    have Hr := congrFun H r
    have hrF : r ∉ fixedPts σ := by rw [mem_fixedPts]; exact ((mem_freeReps σ).mp hr).1
    rw [Pi.add_apply, extZero_apply_not_mem _ hrF, zero_add, avg_extZero_apply_rep σ A Φ hΦ hp hσ v hr,
      Pi.zero_apply] at Hr
    exact Hr
  subst hv
  have hu : u = 0 := by
    funext ⟨x, hx⟩
    have Hx := congrFun H x
    rw [map_zero, map_zero, add_zero, extZero_apply_mem _ hx, Pi.zero_apply] at Hx
    exact Subtype.ext Hx
  subst hu
  rfl

variable [FiniteDimensional k V]

/--
@isnad1 id=le.4h7v.s11.b3db17d1c644 from=translated src=- shape=1a9f6f51 vocab=b0867405
-/
theorem le_finrank_ker_shift_sub_one (hΦ : ∀ f x, Φ f x = A (f (σ⁻¹ x))) {p : ℕ} (hp : p.Prime)
    (hσ : σ ^ p = 1) (hA : A ^ p = 1) :
    p * (fixedPts σ).card * finrank k (LinearMap.ker (A - 1)) +
        (Fintype.card X - (fixedPts σ).card) * finrank k V
      ≤ p * finrank k (LinearMap.ker (Φ - 1)) := by
  have hle := LinearMap.finrank_le_finrank_of_injective (compMap_injective σ A Φ hΦ hp hσ hA)
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.sum_const, smul_eq_mul, smul_eq_mul, Finset.card_univ, Finset.card_univ, Fintype.card_coe,
    Fintype.card_coe] at hle
  have hX : Fintype.card X - (fixedPts σ).card = p * (freeReps σ).card := by
    rw [← card_fixedPts_add_card_moving σ, Nat.add_sub_cancel_left, card_moving σ hp hσ]
  rw [hX]
  calc p * (fixedPts σ).card * finrank k (LinearMap.ker (A - 1)) + p * (freeReps σ).card * finrank k V
      = p * ((fixedPts σ).card * finrank k (LinearMap.ker (A - 1)) + (freeReps σ).card * finrank k V) := by
        ring
    _ ≤ p * finrank k (LinearMap.ker (Φ - 1)) := Nat.mul_le_mul_left p hle

end Abstract

section Concrete

open scoped MatrixGroups
open _root_.HeckeEis open _root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.HeckeEis open _root_.MvPolynomial

/--
@isnad1 id=eq.0h2v.s8.7b709eb455e5 from=translated src=- shape=d770c348 vocab=b34da061
-/
theorem finrank_binaryForm (K : Type*) [Field K] (n : ℕ) : Module.finrank K (BinaryForm K n) = n + 1 := by
  let S : Set (Fin 2 →₀ ℕ) := {d | d.degree = n}
  have e1 : (BinaryForm K n) ≃ₗ[K] (S →₀ K) :=
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) K n)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp S)
  have e2 : S ≃ Fin (n + 1) :=
    { toFun := fun d => ⟨d.1 0, by
        have h := d.2
        simp only [S, Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
        omega⟩
      invFun := fun i => ⟨Finsupp.single 0 i.1 + Finsupp.single 1 (n - i.1), by
        have hi := i.2
        simp only [S, Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.add_apply,
          Finsupp.single_apply]
        simp
        omega⟩
      left_inv := fun d => by
        have h := d.2
        simp only [S, Set.mem_ofPred_eq, Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
        apply Subtype.ext
        ext j
        fin_cases j <;> simp <;> omega
      right_inv := fun i => by
        apply Fin.ext
        simp }
  haveI : Fintype S := Fintype.ofEquiv _ e2.symm
  rw [e1.finrank_eq, Module.finrank_finsupp_self, Fintype.card_congr e2, Fintype.card_fin]

/--
@isnad1 id=finitedi.0h2v.s8.f2061b93e17c from=translated src=- shape=1b398890 vocab=98e40443
-/
scoped instance instFiniteDimensionalBinaryForm (K : Type*) [Field K] (n : ℕ) : FiniteDimensional K (BinaryForm K n) :=
  Module.finite_of_finrank_pos (by rw [finrank_binaryForm]; omega)

variable (N : ℕ)

/--
@isnad1 id=eq.0h2v.s10.83404c022d6c from=translated src=- shape=dfedb679 vocab=cbffb489
-/
theorem neg_one_smul_coset (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : (-1 : SL(2, ℤ)) • x = x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, neg_one_mul, ← mul_neg_one]
    apply QuotientGroup.mk_mul_of_mem
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [Matrix.SpecialLinearGroup.coe_neg]

/--
@isnad1 id=eq.1h3v.s10.b65e3ec8a3a2 from=translated src=- shape=9348b440 vocab=d653b4c7
-/
theorem toPerm_coset_pow_eq_one {g : SL(2, ℤ)} {p : ℕ} (hg : g ^ p = -1) :
    (MulAction.toPerm g : Equiv.Perm (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)) ^ p = 1 := by
  rw [← MulAction.toPermHom_apply, ← map_pow, hg, MulAction.toPermHom_apply]
  ext x
  rw [MulAction.toPerm_apply, neg_one_smul_coset]
  rfl

/--
@isnad1 id=eq.0h0v.s8.44beaf9a967c from=translated src=- shape=323e5004 vocab=d7d6fd83
-/
theorem S_sq : ModularGroup.S ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_S, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.0h0v.s8.0d563df832ed from=translated src=- shape=abdbf034 vocab=2328d14f
-/
theorem ST_cube : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/--
@isnad1 id=eq.2h3v.s13.2ce4a1a6a75a from=translated src=- shape=560a4638 vocab=319cd65d
-/
theorem binaryFormRepSL_pow_eq_one (n : ℕ) (hn : Even n) {g : SL(2, ℤ)} {p : ℕ} (hg : g ^ p = -1) :
    (binaryFormRepSL ℂ n g) ^ p = 1 := by
  rw [← map_pow, hg]
  refine LinearMap.ext fun P => ?_
  rw [HeckeEis.binaryFormRepSL_neg_one_apply, hn.neg_one_pow, one_smul, Module.End.one_apply]

noncomputable def xPow (n : ℕ) : BinaryForm ℂ n :=
  ⟨X 0 ^ n, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow 0 n)⟩

/--
@isnad1 id=ne.0h1v.s9.012f7106bb07 from=translated src=- shape=32e22d1d vocab=a52409cf
-/
theorem xPow_ne_zero (n : ℕ) : xPow n ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  exact pow_ne_zero n (MvPolynomial.X_ne_zero (0 : Fin 2)) this

/--
@isnad1 id=eq.0h1v.s12.6288948c5481 from=translated src=- shape=4e651e1a vocab=9892acf1
-/
theorem binaryFormRepSL_T_xPow (n : ℕ) : binaryFormRepSL ℂ n ModularGroup.T (xPow n) = xPow n := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe]
  simp [xPow, map_pow, binarySubst_X, ModularGroup.coe_T, Fin.sum_univ_two]

end Concrete

section Assembly

open scoped MatrixGroups
open _root_.HeckeEis open _root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.HeckeEis

variable (N : ℕ) (n : ℕ)

/--
@isnad1 id=eq.0h2v.s10.1a9f4d7f54ef from=translated src=- shape=ff7f20e2 vocab=8344ec74
-/
theorem finrank_coset_fun [NeZero N] :
    Module.finrank ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → BinaryForm ℂ n)
      = (n + 1) * (CongruenceSubgroup.Gamma0 N).index := by
  classical
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, finrank_binaryForm,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card, mul_comm]

/--
@isnad1 id=le.4h5v.s16.067b89c48b2a from=translated src=- shape=ea898d2d vocab=39920153
-/
theorem prime_conjunct [NeZero N] (hn : Even n) {g : SL(2, ℤ)}
    (Φ : Module.End ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → BinaryForm ℂ n))
    (hW : ∀ f x, Φ f x = binaryFormRepSL ℂ n g (f (g⁻¹ • x)))
    {p : ℕ} (hp : p.Prime) (hg : g ^ p = -1) :
    p * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // g • x = x}
        * Module.finrank ℂ (LinearMap.ker (binaryFormRepSL ℂ n g - 1))) +
      ((CongruenceSubgroup.Gamma0 N).index
        - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // g • x = x}) * (n + 1)
      ≤ p * Module.finrank ℂ (LinearMap.ker (Φ - 1)) := by
  classical
  letI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) := Fintype.ofFinite _
  have hΦ : ∀ f x, Φ f x = binaryFormRepSL ℂ n g (f ((MulAction.toPerm g)⁻¹ x)) := by
    intro f x
    rw [hW, Equiv.Perm.inv_def, MulAction.toPerm_symm_apply]
  have key := le_finrank_ker_shift_sub_one (k := ℂ) (MulAction.toPerm g) (binaryFormRepSL ℂ n g) Φ hΦ hp
    (toPerm_coset_pow_eq_one N hg) (binaryFormRepSL_pow_eq_one n hn hg)
  have h1 : (fixedPts (MulAction.toPerm g : Equiv.Perm (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))).card
      = Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // g • x = x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, fixedPts]
    simp only [MulAction.toPerm_apply]
  have h2 : Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) = (CongruenceSubgroup.Gamma0 N).index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  rw [h1, h2, finrank_binaryForm, mul_assoc] at key
  exact key

/--
@isnad1 id=le.1h3v.s16.644f16d70b83 from=translated src=- shape=16ed087f vocab=39b909bd
-/
theorem T_conjunct [NeZero N]
    (Φ : Module.End ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → BinaryForm ℂ n))
    (hW : ∀ f x, Φ f x = binaryFormRepSL ℂ n ModularGroup.T (f (ModularGroup.T⁻¹ • x))) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
      ≤ Module.finrank ℂ (LinearMap.ker (Φ - 1)) := by
  classical
  let Cos := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N
  let Q := MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) Cos
  let π : Cos → Q := Quotient.mk''
  haveI : Finite Q := Finite.of_surjective π Quotient.mk''_surjective
  letI : Fintype Q := Fintype.ofFinite Q
  let L0 : (Q → ℂ) →ₗ[ℂ] (Cos → BinaryForm ℂ n) :=
    (LinearMap.toSpanSingleton ℂ (BinaryForm ℂ n) (xPow n)).compLeft Cos ∘ₗ LinearMap.funLeft ℂ ℂ π
  have hL0 : ∀ c x, L0 c x = c (π x) • xPow n := fun c x => rfl
  have hπ : ∀ x : Cos, π (ModularGroup.T⁻¹ • x) = π x := by
    intro x
    apply Quotient.sound
    change (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) Cos) (ModularGroup.T⁻¹ • x) x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨ModularGroup.T⁻¹, (Subgroup.zpowers _).inv_mem (Subgroup.mem_zpowers _)⟩, rfl⟩
  have hmem : ∀ c, L0 c ∈ LinearMap.ker (Φ - 1) := by
    intro c
    rw [LinearMap.mem_ker]
    funext x
    rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, hW, hL0, hL0, map_smul,
      binaryFormRepSL_T_xPow, hπ, Pi.zero_apply, sub_self]
  have hinj : Function.Injective (LinearMap.codRestrict _ L0 hmem) := by
    intro c d h
    have h' : L0 c = L0 d := congrArg Subtype.val h
    funext q
    induction q using Quotient.inductionOn' with
    | h x =>
      have hx := congrFun h' x
      rw [hL0, hL0] at hx
      exact smul_left_injective ℂ (xPow_ne_zero n) hx
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi ℂ, ← Nat.card_eq_fintype_card] at this

end Assembly

end HeckeEis.UH2
open scoped _root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.HeckeEis _root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.HeckeEis.UH2
open scoped _root_.P2MW.S_HeckeEis_le_finrank_fixed_induced_binaryFormRepSL.HeckeEis

open scoped MatrixGroups

/--
@isnad1 id=and.2h3v.s18.acbadf545b6b from=translated src=- shape=cf174e24 vocab=030aa7d4
-/
theorem solution (N : ℕ) [NeZero N] (n : ℕ) (hn : Even n)
    (W : Representation ℂ (⊤ : Subgroup SL(2, ℤ)) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)))
    (hW : ∀ (g : (⊤ : Subgroup SL(2, ℤ))) (f : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N),
      W g f x = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (f (((g : SL(2, ℤ))⁻¹) • x))) :
    Module.finrank ℂ (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) = (n + 1) * (CongruenceSubgroup.Gamma0 N).index ∧
    2 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n ModularGroup.S - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}) * (n + 1)
      ≤ 2 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S, Subgroup.mem_top _⟩ - 1)) ∧
    3 * (Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}
        * Module.finrank ℂ ↥(LinearMap.ker (HeckeEis.binaryFormRepSL ℂ n (ModularGroup.S * ModularGroup.T) - 1)))
      + ((CongruenceSubgroup.Gamma0 N).index - Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // (ModularGroup.S * ModularGroup.T) • x = x}) * (n + 1)
      ≤ 3 * Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩ - 1)) ∧
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N))
      ≤ Module.finrank ℂ ↥(LinearMap.ker (W ⟨ModularGroup.T, Subgroup.mem_top _⟩ - 1)) :=
  ⟨HeckeEis.UH2.finrank_coset_fun N n,
    HeckeEis.UH2.prime_conjunct N n hn _ (hW ⟨ModularGroup.S, Subgroup.mem_top _⟩) Nat.prime_two
      HeckeEis.UH2.S_sq,
    HeckeEis.UH2.prime_conjunct N n hn _ (hW ⟨ModularGroup.S * ModularGroup.T, Subgroup.mem_top _⟩)
      Nat.prime_three HeckeEis.UH2.ST_cube,
    HeckeEis.UH2.T_conjunct N n _ (hW ⟨ModularGroup.T, Subgroup.mem_top _⟩)⟩
