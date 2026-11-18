import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_NegV2
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_CartierModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost

set_option autoImplicit false

universe u

open MvPowerSeries Filter MvPowerSeries.WithPiTopology

noncomputable section

namespace GWAddBody

open Classical

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R]

/--
@isnad1 id=eq.0h5v.s9.a665be642c91 from=translated src=- shape=9414692b vocab=a9baead6
-/
theorem subst_coe_coe {σ τ : Type*} (g : σ → MvPolynomial τ ℤ) (P : MvPolynomial σ ℤ) :
    subst (fun s => ((MvPolynomial.map (Int.castRingHom R) (g s) : MvPolynomial τ R) :
      MvPowerSeries τ R)) ((MvPolynomial.map (Int.castRingHom R) P : MvPolynomial σ R) :
        MvPowerSeries σ R) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval g P) : MvPolynomial τ R) :
        MvPowerSeries τ R) := by
  rw [subst_coe]
  set G : σ → MvPowerSeries τ R := fun s =>
    ((MvPolynomial.map (Int.castRingHom R) (g s) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial σ ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial σ ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun s => ?_)
    · have h1 := RingHom.ext_int (ψ₁.comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
        (ψ₂.comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      exact RingHom.congr_fun h1 r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ P

def wS (N : ℕ) : MvPowerSeries ℕ R :=
  ((MvPolynomial.map (Int.castRingHom R) (wittPolynomial p ℤ N) : MvPolynomial ℕ R) :
    MvPowerSeries ℕ R)

/--
@isnad1 id=eq.0h4v.s8.117793d1a874 from=translated src=- shape=166469d7 vocab=4ac4a848
-/
theorem coeff_wS (N : ℕ) (e : ℕ →₀ ℕ) :
    coeff e (wS p R N) = ∑ k ∈ Finset.range (N + 1),
      if e = Finsupp.single k (p ^ (N - k)) then (p : R) ^ k else 0 := by
  rw [wS, map_wittPolynomial, MvPolynomial.coeff_coe, wittPolynomial, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.coeff_monomial]
  by_cases h : e = Finsupp.single k (p ^ (N - k))
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h h'.symm), ite_eq_right h]

/--
@isnad1 id=eq.0h5v.s8.5cd27f33de63 from=translated src=- shape=06148b27 vocab=aec495b3
-/
theorem coeff_wS_single (N k n : ℕ) :
    coeff (Finsupp.single k (p ^ n)) (wS p R N) = if k + n = N then (p : R) ^ k else 0 := by
  rw [coeff_wS]
  by_cases hkn : k + n = N
  · rw [ite_eq_left hkn, Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]
    · rw [ite_eq_left]; congr 2; omega
    · intro k' hk' hne
      rw [ite_eq_right]
      intro h
      rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hk, _⟩ | ⟨h0, _⟩
      · exact hne hk.symm
      · exact pow_ne_zero _ hp.out.ne_zero h0
  · rw [ite_eq_right hkn]
    refine Finset.sum_eq_zero fun k' hk' => ?_
    rw [ite_eq_right]
    intro h
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hk, hpn⟩ | ⟨h0, _⟩
    · have := Nat.pow_right_injective hp.out.two_le hpn
      have hk'' := Finset.mem_range.mp hk'
      omega
    · exact pow_ne_zero _ hp.out.ne_zero h0

/--
@isnad1 id=eq.1h4v.s7.fd2313c827b5 from=translated src=- shape=95d0a174 vocab=e430f5bd
-/
theorem coeff_wS_of_ne (N : ℕ) (e : ℕ →₀ ℕ) (he : ∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) :
    coeff e (wS p R N) = 0 := by
  rw [coeff_wS]
  exact Finset.sum_eq_zero fun k _ => ite_eq_right (he k (N - k))

variable {R}

def GM (c : ℕ → R) (M : ℕ) : MvPowerSeries ℕ R := ∑ N ∈ Finset.range M, c N • wS p R N

variable (c : ℕ → R) (G : MvPowerSeries ℕ R)
  (hG : ∀ k n : ℕ, (coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
  (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (coeff e G : R) = 0)

include hG hG' in
/--
@isnad1 id=ex.2h5v.s9.c3d05fd5dee4 from=translated src=- shape=30ee2b3b vocab=fda67b99
-/
theorem coeff_GM_eventually (e : ℕ →₀ ℕ) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, coeff e (GM p c M) = coeff e G := by
  by_cases he : ∃ k n : ℕ, e = Finsupp.single k (p ^ n)
  · obtain ⟨k, n, rfl⟩ := he
    refine ⟨k + n + 1, fun M hM => ?_⟩
    rw [GM, map_sum, hG]
    simp only [map_smul, coeff_wS_single, smul_eq_mul]
    rw [Finset.sum_eq_single_of_mem (k + n) (Finset.mem_range.mpr (by omega))]
    · rw [ite_eq_left rfl, mul_comm]
    · intro N _ hN; rw [ite_eq_right (fun h => hN h.symm), mul_zero]
  · push Not at he
    refine ⟨0, fun M _ => ?_⟩
    rw [GM, map_sum, hG' e he]
    refine Finset.sum_eq_zero fun N _ => ?_
    rw [map_smul, coeff_wS_of_ne p R N e he, smul_zero]

include hG hG' in
/--
@isnad1 id=tendsto.2h4v.s9.d4a905c21be1 from=translated src=- shape=5977bcb7 vocab=0d691f9a
-/
theorem tendsto_GM :
    @Tendsto ℕ (MvPowerSeries ℕ R) (GM p c) atTop
      (@nhds _ (@MvPowerSeries.WithPiTopology.instTopologicalSpace ℕ R ⊥) G) := by
  letI : TopologicalSpace R := ⊥
  rw [tendsto_iff_coeff_tendsto]
  intro e
  obtain ⟨M₀, hM₀⟩ := coeff_GM_eventually p c G hG hG' e
  exact tendsto_atTop_of_eventually_const hM₀

/--
@isnad1 id=eq.0h3v.s8.2f94e1ae3607 from=translated src=- shape=2f468e92 vocab=d8c19f88
-/
theorem subst_addFam_wS (N : ℕ) :
    subst (MvFormalGroup.WittLaw.addFam p R) (wS p R N) =
      subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (wS p R N) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (wS p R N) := by

  have hadd : MvFormalGroup.WittLaw.addFam p R = fun k =>
      ((MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p k) : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := rfl
  have hblk : ∀ i : Fin 2, (fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) = fun m =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.X (i, m) : MvPolynomial (Fin 2 × ℕ) ℤ) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    intro i; funext m; simp
  rw [hadd, hblk 0, hblk 1, wS, subst_coe_coe, subst_coe_coe, subst_coe_coe,
    ← MvPolynomial.coe_add, ← map_add]
  congr 2
  rw [MvPolynomial.aeval_eq_bind₁, WittVector.wittAdd, wittStructureInt_prop, map_add,
    MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right, MvPolynomial.rename_eq_aeval,
    MvPolynomial.rename_eq_aeval]
  rfl

/--
@isnad1 id=eq.0h4v.s8.a36623d88640 from=translated src=- shape=a3d5e004 vocab=f35d0881
-/
theorem subst_addFam_GM (M : ℕ) :
    subst (MvFormalGroup.WittLaw.addFam p R) (GM p c M) =
      subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M) := by
  have hA := MvFormalGroup.WittLaw.hasSubst_addFam p R
  have hB0 : HasSubst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := R) 0
  have hB1 : HasSubst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := R) 1
  simp only [GM, ← coe_substAlgHom hA, ← coe_substAlgHom hB0, ← coe_substAlgHom hB1,
    map_sum, map_smul, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [coe_substAlgHom hA, coe_substAlgHom hB0, coe_substAlgHom hB1, subst_addFam_wS]

end GWAddBody

open GWAddBody Filter MvPowerSeries.WithPiTopology in
/--
@isnad1 id=eq.2h4v.s9.b2f5117aaf11 from=translated src=- shape=6ad829b3 vocab=46b7a08c
-/
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) G =
      MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) G +
        MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) G := by
  letI uR : UniformSpace R := ⊥
  have hA := MvFormalGroup.WittLaw.hasSubst_addFam p R
  have hB0 : HasSubst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := R) 0
  have hB1 : HasSubst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := R) 1
  have hT := tendsto_GM p c G hG hG'

  have h1 : Tendsto (fun M => subst (MvFormalGroup.WittLaw.addFam p R) (GM p c M)) atTop
      (nhds (subst (MvFormalGroup.WittLaw.addFam p R) G)) :=
    ((continuous_subst hA).tendsto G).comp hT
  have h2 : Tendsto (fun M => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M) +
      subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M)) atTop
      (nhds (subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) G +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) G)) :=
    (((continuous_subst hB0).tendsto G).comp hT).add (((continuous_subst hB1).tendsto G).comp hT)
  have heq : (fun M => subst (MvFormalGroup.WittLaw.addFam p R) (GM p c M)) =
      fun M => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (GM p c M) :=
    funext (subst_addFam_GM p c)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
