import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_gaussPresentation_qExpand_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_gaussPresentation_qExpand_iff

set_option autoImplicit false

namespace GaussQExpand

open PowerSeries HahnSeries ModularCurve

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.1h3v.s7.9b4d307ff527 from=translated src=- shape=8a4291ab vocab=6ca2f719
-/
theorem ofPowerSeries_coeff_neg (u : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (ofPowerSeries ℤ R u).coeff k = 0 := by
  rw [ofPowerSeries_apply]
  refine embDomain_of_notMem_range ?_
  rintro ⟨m, hm⟩
  change (m : ℤ) = k at hm
  omega

/--
@isnad1 id=eq.0h3v.s9.59c44386f30d from=translated src=- shape=d05b2b85 vocab=9f6a54b0
-/
theorem qExpand_ofPowerSeries (N : ℕ) [NeZero N] (u : PowerSeries R) :
    qExpand R N (ofPowerSeries ℤ R u) = ofPowerSeries ℤ R (expand N (NeZero.ne N) u) := by
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  ext k
  by_cases hNk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hNk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · rw [ofPowerSeries_coeff_neg _ hm, ofPowerSeries_coeff_neg _ (mul_neg_of_pos_of_neg hN0 hm)]
    · lift m to ℕ using hm with m
      have hcast : ((N : ℤ) * (m : ℤ)) = ((N * m : ℕ) : ℤ) := by push_cast; ring
      rw [ofPowerSeries_apply_coeff, hcast, ofPowerSeries_apply_coeff, coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hNk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [ofPowerSeries_apply_coeff, coeff_expand_of_not_dvd]
      intro h
      exact hNk (by exact_mod_cast h)

/--
@isnad1 id=injectiv.1h2v.s7.f70dc0f728cc from=translated src=- shape=3ff4978e vocab=a660e2cf
-/
theorem expand_injective (N : ℕ) (hN : N ≠ 0) : Function.Injective (expand N hN (R := R)) := by
  intro a b h
  ext m
  rw [← coeff_expand_mul N hN a m, ← coeff_expand_mul N hN b m, h]

noncomputable def slice (N r : ℕ) (a : PowerSeries R) : PowerSeries R := PowerSeries.mk fun k => coeff (N * k + r) a

/--
@isnad1 id=eq.0h5v.s8.e0c216551bfe from=translated src=- shape=0056f810 vocab=062ea23a
-/
@[scoped simp] theorem coeff_slice (N r : ℕ) (a : PowerSeries R) (k : ℕ) : coeff k (slice N r a) = coeff (N * k + r) a := by
  rw [slice, coeff_mk]

/--
@isnad1 id=eq.0h6v.s7.53f961541061 from=translated src=- shape=fd1976fe vocab=04febb3f
-/
theorem map_slice {S : Type*} [CommRing S] (f : R →+* S) (N r : ℕ) (a : PowerSeries R) :
    map f (slice N r a) = slice N r (map f a) := by
  ext k; simp [coeff_map]

/--
@isnad1 id=eq.1h3v.s7.ded294786ec1 from=translated src=- shape=3225d5a8 vocab=6585ddcd
-/
theorem sum_X_pow_mul_expand_slice (N : ℕ) (hN : N ≠ 0) (a : PowerSeries R) :
    ∑ r ∈ Finset.range N, (X : PowerSeries R) ^ r * expand N hN (slice N r a) = a := by
  ext n
  rw [map_sum]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [Finset.sum_eq_single_of_mem (n % N) (Finset.mem_range.mpr (Nat.mod_lt n hNpos))]
  · rw [coeff_X_pow_mul', ite_eq_left (Nat.mod_le n N), coeff_expand]
    have hdvd : N ∣ n - n % N := Nat.dvd_sub_mod n
    rw [ite_eq_left hdvd, coeff_slice]
    congr 1
    have h2 : N * ((n - n % N) / N) = n - n % N := Nat.mul_div_cancel' hdvd
    rw [h2, Nat.sub_add_cancel (Nat.mod_le n N)]
  · intro r hr hrne
    rw [coeff_X_pow_mul']
    split_ifs with hrn
    · rw [coeff_expand, ite_eq_right]
      intro hdvd
      apply hrne
      have hr' : r < N := Finset.mem_range.mp hr
      obtain ⟨c, hc⟩ := hdvd
      have : n = N * c + r := by rw [← hc]; exact (Nat.sub_add_cancel hrn).symm
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hr']
    · rfl

theorem eq_zero_of_sum_single_mul_qExpand (N : ℕ) [NeZero N] (h : ℕ → LaurentSeries R)
    (H : ∑ r ∈ Finset.range N, single (r : ℤ) (1 : R) * qExpand R N (h r) = 0) :
    ∀ r < N, h r = 0 := by
  intro r hr
  ext k
  have hk := congrArg (fun f : LaurentSeries R => f.coeff ((N : ℤ) * k + r)) H
  simp only [coeff_zero, coeff_sum] at hk
  rw [Finset.sum_eq_single_of_mem r (Finset.mem_range.mpr hr)] at hk
  · rw [coeff_single_mul, one_mul, add_sub_cancel_right, qExpand_coeff_mul] at hk
    rw [coeff_zero]; exact hk
  · intro r' hr' hne
    rw [coeff_single_mul, one_mul]
    apply qExpand_coeff_of_not_dvd
    intro hd
    apply hne
    have hr'N : r' < N := Finset.mem_range.mp hr'
    have hd' : (N : ℤ) ∣ (r : ℤ) - (r' : ℤ) := by
      have : (N : ℤ) * k + r - r' = (N : ℤ) * k + ((r : ℤ) - r') := by ring
      rw [this] at hd
      have h3 := dvd_sub hd (dvd_mul_right (N : ℤ) k)
      rwa [add_sub_cancel_left] at h3
    have hmod : (r' : ℤ) % N = (r : ℤ) % N := Int.modEq_iff_dvd.mpr hd'
    have h1 : (r' : ℤ) % N = r' := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr'N)
    have h2 : (r : ℤ) % N = r := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)
    have : (r' : ℤ) = r := by rw [← h1, ← h2]; exact hmod
    exact_mod_cast this

/--
@isnad1 id=eq.0h3v.s9.a2e88e9990d6 from=translated src=- shape=90ffec65 vocab=7a47c471
-/
theorem ofPowerSeries_eq_sum (N : ℕ) [NeZero N] (a : PowerSeries R) :
    ofPowerSeries ℤ R a = ∑ r ∈ Finset.range N, single (r : ℤ) (1 : R) * qExpand R N (ofPowerSeries ℤ R (slice N r a)) := by
  conv_lhs => rw [← sum_X_pow_mul_expand_slice N (NeZero.ne N) a]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_mul, map_pow, ofPowerSeries_X, single_pow, qExpand_ofPowerSeries]
  simp

end GaussQExpand
open scoped _root_.P2MW.S_ModularCurve_exists_gaussPresentation_qExpand_iff.GaussQExpand

open GaussQExpand PowerSeries HahnSeries ModularCurve in
/--
@isnad1 id=iff.0h4v.s10.042b0d39fc12 from=translated src=- shape=8557f62c vocab=124891d1
-/
theorem solution
    (A : Type) [CommRing A] [IsLocalRing A] (L : Type) [Field L] [Algebra A L]
    (N : ℕ) [NeZero N] (g : LaurentSeries L) :
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ModularCurve.qExpand L N g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ↔
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  constructor
  · rintro ⟨x, y, hy, hxy⟩

    have hex : ∃ r, r < N ∧ (slice N r y).map (IsLocalRing.residue A) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hy
      rw [← sum_X_pow_mul_expand_slice N hN (y.map (IsLocalRing.residue A))]
      refine Finset.sum_eq_zero (fun r hr => ?_)
      rw [← map_slice, hall r (Finset.mem_range.mp hr), map_zero, mul_zero]
    obtain ⟨r, hr, hyr⟩ := hex
    refine ⟨slice N r x, slice N r y, hyr, ?_⟩

    have key : ∑ r' ∈ Finset.range N, single (r' : ℤ) (1 : L) *
        qExpand L N (g * ofPowerSeries ℤ L ((slice N r' y).map (algebraMap A L)) - ofPowerSeries ℤ L ((slice N r' x).map (algebraMap A L))) = 0 := by
      have hy' := ofPowerSeries_eq_sum N (y.map (algebraMap A L))
      have hx' := ofPowerSeries_eq_sum N (x.map (algebraMap A L))
      simp only [← map_slice] at hy' hx'
      have : qExpand L N g * ofPowerSeries ℤ L (y.map (algebraMap A L)) - ofPowerSeries ℤ L (x.map (algebraMap A L)) = 0 :=
        sub_eq_zero.mpr hxy
      rw [hy', hx', Finset.mul_sum, ← Finset.sum_sub_distrib] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun r' _ => ?_)
      rw [map_sub, map_mul, mul_sub]
      ring
    have := eq_zero_of_sum_single_mul_qExpand N _ key r hr
    exact sub_eq_zero.mp this
  · rintro ⟨x, y, hy, hxy⟩
    refine ⟨expand N hN x, expand N hN y, ?_, ?_⟩
    · rw [map_expand]
      intro h0
      exact hy (expand_injective N hN (by rw [h0, map_zero]))
    · rw [map_expand, map_expand, ← qExpand_ofPowerSeries, ← qExpand_ofPowerSeries, ← map_mul, hxy]
