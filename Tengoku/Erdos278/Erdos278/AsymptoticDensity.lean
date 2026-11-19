import Tengoku.Erdos278.Erdos278.Density
import Tengoku.Seed.Data.Nat.Periodic
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/AsymptoticDensity.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace Erdos278


open Finset Filter Topology

/--
@isnad1 id=eq.1h3v.s5.385e9d4eaa7c from=translated src=- shape=aa739d58 vocab=cf63c460
-/
theorem periodic_count_mul (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : Function.Periodic p L) (k : ℕ) :
    Nat.count p (k * L) = k * Nat.count p L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.count_add']
    simp only [hp.funext, ih]
    ring

/--
@isnad1 id=eq.1h3v.s6.ff313e8c1f8b from=translated src=- shape=42570455 vocab=8375496f
-/
theorem periodic_count_decomposition (p : ℕ → Prop) [DecidablePred p] (L N : ℕ)
    (hp : Function.Periodic p L) :
    Nat.count p N = (N / L) * Nat.count p L + Nat.count p (N % L) := by
  have hshift : (fun k => p (N / L * L + k)) = p := by
    funext k
    rw [add_comm]
    simpa using hp.nsmul (N / L) k
  conv_lhs => rw [← Nat.div_add_mod N L, Nat.mul_comm L (N / L)]
  rw [Nat.count_add, periodic_count_mul p L hp]
  simp only [hshift]

/--
@isnad1 id=le.3h3v.s6.7b8bbcfea882 from=translated src=- shape=48438ede vocab=329a24f8
-/
theorem periodic_density_error (p : ℕ → Prop) [DecidablePred p]
    (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) (N : ℕ) (hN : 0 < N) :
    |(Nat.count p N : ℝ) / N - (Nat.count p L : ℝ) / L| ≤ (L : ℝ) / N := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (Nat.count p N : ℝ) =
      (N / L : ℕ) * (Nat.count p L : ℝ) + (Nat.count p (N % L) : ℝ) := by
    exact_mod_cast periodic_count_decomposition p L N hp
  have hn : (N : ℝ) = (N / L : ℕ) * (L : ℝ) + (N % L : ℕ) := by
    exact_mod_cast (show N = N / L * L + N % L by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N L).symm)
  have hC0 : (0 : ℝ) ≤ Nat.count p L := by positivity
  have hCL : (Nat.count p L : ℝ) ≤ L := by exact_mod_cast Nat.count_le p (n := L)
  have hR0 : (0 : ℝ) ≤ Nat.count p (N % L) := by positivity
  have hr0 : (0 : ℝ) ≤ (N % L : ℕ) := by positivity
  have hrL : ((N % L : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.mod_lt N hL).le
  have hRr : (Nat.count p (N % L) : ℝ) ≤ (N % L : ℕ) := by
    exact_mod_cast Nat.count_le p (n := N % L)
  have heq : (Nat.count p N : ℝ) / N - (Nat.count p L : ℝ) / L =
      ((L : ℝ) * Nat.count p (N % L) - (N % L : ℕ) * (Nat.count p L : ℝ)) /
        ((N : ℝ) * L) := by
    field_simp
    nlinarith
  have hb : |(L : ℝ) * Nat.count p (N % L) -
      (N % L : ℕ) * (Nat.count p L : ℝ)| ≤ (L : ℝ) ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [heq, abs_div, abs_of_pos (mul_pos hNR hLR)]
  calc
    _ ≤ (L : ℝ)^2 / ((N : ℝ) * L) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = (L : ℝ) / N := by field_simp

/-- The finite-period fraction is the ordinary one-sided natural density.
@isnad1 id=tendsto.2h2v.s6.aa37c0e8d4e2 from=translated src=- shape=01293969 vocab=e63a8fe6
-/
theorem periodic_density_tendsto (p : ℕ → Prop) [DecidablePred p]
    (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) :
    Tendsto (fun N : ℕ => (Nat.count p N : ℝ) / N) atTop
      (𝓝 ((Nat.count p L : ℝ) / L)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((L : ℝ) / ε)
  refine ⟨max N 1, fun k hk => ?_⟩
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast (le_trans (le_max_left N 1) hk)
  have hbound : (L : ℝ) / k < ε := by
    apply (div_lt_iff₀ hkR).mpr
    have := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hN hNk)
    nlinarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (periodic_density_error p L hL hp k hkpos) hbound

variable {ι : Type*} [DecidableEq ι]

def CoveredNat (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) (k : ℕ) : Prop :=
  ∃ i ∈ s, (k : ℤ) ≡ a i [ZMOD n i]

instance coveredNatDecidable (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) :
    DecidablePred (CoveredNat s n a) := by
  intro k
  unfold CoveredNat
  infer_instance

/--
@isnad1 id=periodic.0h4v.s5.4a61cd8f0ccd from=translated src=- shape=627cd45e vocab=a122abeb
-/
theorem coveredNat_periodic (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) :
    Function.Periodic (CoveredNat s n a) (s.lcm n) := by
  intro k
  apply propext
  have hc (i : ι) (hi : i ∈ s) :
      ((k + s.lcm n : ℕ) : ℤ) ≡ (k : ℤ) [ZMOD n i] := by
    apply Int.modEq_iff_dvd.mpr
    have hd : (n i : ℤ) ∣ (s.lcm n : ℕ) :=
      Int.natCast_dvd_natCast.mpr (Finset.dvd_lcm hi)
    simpa using dvd_neg.mpr hd
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, (hc i hi).symm.trans h⟩,
    fun ⟨i, hi, h⟩ => ⟨i, hi, (hc i hi).trans h⟩⟩

/--
@isnad1 id=eq.0h4v.s5.c4a11fd79bf0 from=translated src=- shape=7b7ff8c6 vocab=9e297656
-/
theorem count_coveredNat_period (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) :
    Nat.count (CoveredNat s n a) (s.lcm n) = (coveredFinset s n a).card := by
  rw [Nat.count_eq_card_filter_range]
  have heq : ((range (s.lcm n)).filter (CoveredNat s n a)).map Nat.castEmbedding =
      coveredFinset s n a := by
    ext z
    simp only [Finset.mem_map, mem_filter, mem_range, Nat.castEmbedding_apply,
      coveredFinset, mem_biUnion, residueFinset, mem_Ico, CoveredNat]
    constructor
    · rintro ⟨k, ⟨hk, i, hi, hc⟩, rfl⟩
      exact ⟨i, hi, ⟨Int.natCast_nonneg k, by exact_mod_cast hk⟩, hc⟩
    · rintro ⟨i, hi, ⟨hz0, hzL⟩, hc⟩
      lift z to ℕ using hz0
      exact ⟨z, ⟨by exact_mod_cast hzL, i, hi, hc⟩, rfl⟩
  rw [← heq, card_map]

/-- Density in `Density.lean` is not merely a definition chosen to match the
graph formula: the ordinary counting ratios converge to it.
@isnad1 id=tendsto.1h4v.s6.72d9c38e10bc from=translated src=- shape=725d6995 vocab=b712002a
-/
theorem density_is_natural_density (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    Tendsto (fun N : ℕ => (Nat.count (CoveredNat s n a) N : ℝ) / N) atTop
      (𝓝 (density s n a : ℝ)) := by
  have hL : 0 < s.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i hi).ne'))
  simpa only [count_coveredNat_period, density, Rat.cast_div, Rat.cast_natCast] using
    periodic_density_tendsto (CoveredNat s n a) (s.lcm n) hL (coveredNat_periodic s n a)

end Erdos278
