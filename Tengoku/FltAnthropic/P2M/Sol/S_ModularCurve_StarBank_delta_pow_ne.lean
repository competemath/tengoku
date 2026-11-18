import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_StarBank_delta_pow_ne.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`, 2 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_StarBank_delta_pow_ne

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open _root_.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_one_apply qExpand_congr qExpand_qExpand etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg map_intCast_pow_char_eq_qExpand)
namespace W1
open _root_.ModularCurve

local notation "𝓔[" K "]" =>
  HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)

/--
@isnad1 id=eq.0h3v.s9.e7ea2f5bcbe2 from=translated src=- shape=79cfe7bf vocab=70b23fe5
-/
theorem coeff_one_mul {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    PowerSeries.coeff 1 (φ * ψ) =
      PowerSeries.coeff 0 φ * PowerSeries.coeff 1 ψ + PowerSeries.coeff 1 φ * PowerSeries.coeff 0 ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton]

/--
@isnad1 id=eq.0h0v.s6.1a40e294acc6 from=translated src=- shape=972ef9b2 vocab=7f803c97
-/
theorem coeff_one_etaProd : PowerSeries.coeff 1 etaProd = -1 := by
  have hmul := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have ht : Filter.Tendsto
      (fun s : Finset ℕ => PowerSeries.coeff 1
        (∏ i ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1))))
      Filter.atTop (nhds (PowerSeries.coeff 1 etaProd)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ 1).tendsto _).comp hmul.hasProd
  rw [nhds_discrete ℤ, Filter.tendsto_pure] at ht
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp ht
  have hsub : s₀ ⊆ insert 0 (s₀.erase 0) := Finset.subset_insert_iff.mpr (subset_refl _)
  have key : PowerSeries.coeff 1
      (∏ i ∈ insert 0 (s₀.erase 0), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1))) =
        PowerSeries.coeff 1 etaProd := hs₀ _ hsub
  rw [← key, Finset.prod_insert (Finset.notMem_erase 0 s₀)]

  obtain ⟨r, hr⟩ : ∃ r : PowerSeries ℤ,
      ∏ i ∈ s₀.erase 0, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (i + 1)) =
        1 + PowerSeries.X ^ 2 * r := by
    refine Finset.prod_induction _ (fun Q => ∃ r : PowerSeries ℤ, Q = 1 + PowerSeries.X ^ 2 * r)
      ?_ ?_ ?_
    · rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u + v + PowerSeries.X ^ 2 * u * v, by ring⟩
    · exact ⟨0, by ring⟩
    · intro i hi
      cases i with
      | zero => exact absurd hi (Finset.notMem_erase 0 s₀)
      | succ k => exact ⟨-PowerSeries.X ^ k, by ring⟩
  have hexp : ((1 : PowerSeries ℤ) - PowerSeries.X ^ (0 + 1)) * (1 + PowerSeries.X ^ 2 * r) =
      1 - PowerSeries.X + PowerSeries.X ^ 2 * (r - PowerSeries.X * r) := by
    ring
  rw [hr, hexp, map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_one_X,
    PowerSeries.coeff_X_pow_mul']
  simp

/--
@isnad1 id=eq.0h1v.s7.5669883c5d37 from=translated src=- shape=3f75c59f vocab=38a0d7d1
-/
theorem constantCoeff_etaProd_map (K : Type*) [CommRing K] :
    PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom K) etaProd) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_etaProd, map_one]

/--
@isnad1 id=eq.0h1v.s8.4d02314d8525 from=translated src=- shape=ff58e36b vocab=fd0eb0ce
-/
theorem coeff_one_etaProd_map (K : Type*) [CommRing K] :
    PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom K) etaProd) = -1 := by
  rw [PowerSeries.coeff_map, coeff_one_etaProd, map_neg, map_one]

/--
@isnad1 id=eq.2h3v.s8.c28ef7dad6ec from=translated src=- shape=854e013e vocab=e649733b
-/
theorem coeff_one_pow_of_shape {R : Type*} [CommRing R] (e : PowerSeries R)
    (h0 : PowerSeries.constantCoeff e = 1) (h1 : PowerSeries.coeff 1 e = -1) (N : ℕ) :
    PowerSeries.coeff 1 (e ^ N) = -(N : R) := by
  induction N with
  | zero => simp [PowerSeries.coeff_one]
  | succ N ih =>
    rw [pow_succ, coeff_one_mul, ih, h1, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      h0, one_pow, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    push_cast
    ring

/--
@isnad1 id=eq.0h2v.s8.8dd2aca22be2 from=translated src=- shape=de87b79e vocab=1bc6331a
-/
theorem coeff_one_etaC_pow (K : Type*) [CommRing K] (N : ℕ) :
    (𝓔[K] ^ N).coeff 1 = -(N : K) := by
  rw [← map_pow]
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ)
    (PowerSeries.map (Int.castRingHom K) etaProd ^ N) 1
  rw [Nat.cast_one] at h
  rw [h]
  exact coeff_one_pow_of_shape _ (constantCoeff_etaProd_map K) (coeff_one_etaProd_map K) N

/--
@isnad1 id=eq.0h4v.s8.e0ed444bd634 from=translated src=- shape=23929d0b vocab=c57ef02a
-/
theorem ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u).map f = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext k
  rw [HahnSeries.map_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

/--
@isnad1 id=eq.0h4v.s8.950266f77b74 from=translated src=- shape=ece44e1c vocab=edc7eb7d
-/
theorem map_intCast_pow_char_pow_eq_qExpand (K : Type*) [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP K ℓ] (s : LaurentSeries ℤ) (c : ℕ) :
    (s.map (Int.castRingHom K)) ^ (ℓ ^ c) = qExpand K (ℓ ^ c) (s.map (Int.castRingHom K)) := by
  induction c with
  | zero => rw [qExpand_congr (pow_zero ℓ), qExpand_one_apply, pow_zero, pow_one]
  | succ c ih =>
    calc (s.map (Int.castRingHom K)) ^ (ℓ ^ (c + 1))
        = ((s.map (Int.castRingHom K)) ^ ℓ) ^ (ℓ ^ c) := by rw [← pow_mul, ← pow_succ']
      _ = qExpand K ℓ ((s.map (Int.castRingHom K)) ^ (ℓ ^ c)) := by
          rw [map_intCast_pow_char_eq_qExpand ℓ s, ← map_pow]
      _ = qExpand K (ℓ ^ (c + 1)) (s.map (Int.castRingHom K)) := by
          rw [ih, qExpand_qExpand, qExpand_congr (pow_succ' ℓ c).symm]

/--
@isnad1 id=eq.0h3v.s9.403fd88fba5a from=translated src=- shape=932e1fc8 vocab=1acf1da9
-/
theorem etaC_pow_char_pow (K : Type*) [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (c : ℕ) :
    𝓔[K] ^ (ℓ ^ c) = qExpand K (ℓ ^ c) 𝓔[K] := by
  rw [← ofPowerSeries_map]
  exact map_intCast_pow_char_pow_eq_qExpand K ℓ _ c

end ModularCurve.W1

namespace ModularCurve export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_one_apply qExpand_congr qExpand_qExpand etaProd constantCoeff_etaProd ofPowerSeries_coeff_of_neg map_intCast_pow_char_eq_qExpand) namespace StarBank end ModularCurve.StarBank
open scoped _root_.ModularCurve in

/--
@isnad1 id=ne.2h4v.s10.49aee52a4a1d from=translated src=- shape=55ba98ec vocab=de4f255d
-/
theorem ModularCurve.StarBank.etaProd_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (p : ℕ) [NeZero p] (hp : (p : K) ≠ 0) (hp1 : p ≠ 1) (γ : K) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p) ≠
      HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓp : ¬ ℓ ∣ p := fun h => hp ((CharP.cast_eq_zero_iff K ℓ p).2 h)
  obtain ⟨c, m, hm, h24⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show (24 : ℕ) ≠ 0 by decide) ℓ hℓ.one_lt.ne'
  intro h
  have key : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) =
      (HahnSeries.C γ * qExpand K p
        (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
          ((ℓ ^ c : ℕ) : ℤ) := by
    rw [h]

  have hL : (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
        (24 * p)).coeff ((ℓ ^ c : ℕ) : ℤ) = -((m * p : ℕ) : K) := by
    have e1 : HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
          (24 * p) =
        qExpand K (ℓ ^ c)
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^
            (m * p)) := by
      rw [h24, show ℓ ^ c * m * p = ℓ ^ c * (m * p) by ring, pow_mul,
        ModularCurve.W1.etaC_pow_char_pow K ℓ c, map_pow]
    have e2 := qExpand_coeff_mul (R := K) (ℓ ^ c)
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (m * p)) 1
    rw [mul_one] at e2
    rw [e1, e2, ModularCurve.W1.coeff_one_etaC_pow]

  have hR : (HahnSeries.C γ * qExpand K p
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)).coeff
        ((ℓ ^ c : ℕ) : ℤ) = 0 := by
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, qExpand_coeff_of_not_dvd, smul_zero]
    rw [Int.natCast_dvd_natCast]
    intro hd
    obtain ⟨k, -, hpk⟩ := (Nat.dvd_prime_pow hℓ).1 hd
    cases k with
    | zero => exact hp1 (by simpa using hpk)
    | succ k =>
      rw [hpk] at hℓp
      exact hℓp (dvd_pow_self ℓ (Nat.succ_ne_zero k))
  rw [hL, hR, neg_eq_zero] at key
  rcases (Nat.Prime.dvd_mul hℓ).1 ((CharP.cast_eq_zero_iff K ℓ (m * p)).1 key) with h1 | h2
  · exact hm h1
  · exact hℓp h2

open scoped _root_.ModularCurve in

private theorem ModularCurve.StarBank.delta_pow_ne (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
  have hp : p.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hpK : (p : K) ≠ 0 := fun h0 =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 ((CharP.cast_eq_zero_iff K ℓ p).1 h0)).symm
  intro h
  apply ModularCurve.StarBank.etaProd_pow_ne K p hpK hp.ne_one γ
  have hu : HahnSeries.single (-(p : ℤ)) (1 : K) * HahnSeries.single (p : ℤ) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one, HahnSeries.single_zero_one]
  have hsp : HahnSeries.single (1 : ℤ) (1 : K) ^ p = HahnSeries.single (p : ℤ) (1 : K) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  calc HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ (24 * p)
      = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p := by
        rw [mul_pow, hsp, ← mul_assoc, hu, one_mul, pow_mul]
    _ = HahnSeries.single (-(p : ℤ)) (1 : K) * (HahnSeries.C γ * qExpand K p
          (HahnSeries.single (1 : ℤ) (1 : K) *
            HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) := by
        rw [h]
    _ = HahnSeries.C γ * qExpand K p
          (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) := by
        rw [map_mul, qExpand_single, mul_one, mul_left_comm,
          ← mul_assoc (HahnSeries.single (-(p : ℤ)) (1 : K)), hu, one_mul]

section Falsifier

variable (K : Type*) [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

end Falsifier

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_StarBank_delta_pow_ne.ModularCurve in

/--
@isnad1 id=ne.1h4v.s10.e74121beb567 from=translated src=- shape=5d21740c vocab=c65a5a89
-/
theorem solution (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] {p : ℕ} [Fact p.Prime] (hpℓ : p ≠ ℓ) (γ : K) :
    (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ p ≠
      HahnSeries.C γ * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) :=
  ModularCurve.StarBank.delta_pow_ne K hpℓ γ

