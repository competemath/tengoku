/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.GroupTheory.Index
public import Tengoku.Seed.Data.Nat.Prime.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Odd-primary subgroup index comparison

This file contains the abstract group-index arithmetic needed to compare the
normalized cyclotomic-unit subgroup with the squared-family subgroup.  If
`H ≤ K ≤ G` and the relative index `[K : H]` is a power-of-two divisor, then
an odd prime `p` divides `[G : H]` exactly when it divides `[G : K]`.
-/

@[expose] public section

namespace BernoulliRegular

/--
@isnad1 id=not.3h3v.s5.baf96e9e4a12 from=translated src=- shape=27736b5b vocab=a799fb17
-/
theorem prime_not_dvd_of_dvd_two_pow {p n r : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hn : n ∣ 2 ^ r) : ¬ p ∣ n := by
  intro hpn
  have hp_dvd_two_pow : p ∣ 2 ^ r := hpn.trans hn
  have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hp_dvd_two_pow
  have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd_two
  exact hp_odd (le_antisymm hp_le_two hp.two_le)

/--
@isnad1 id=iff.3h4v.s6.850d4188844d from=translated src=- shape=21f262ab vocab=93abe03f
-/
theorem subgroup_index_prime_dvd_iff_of_not_dvd_relIndex {G : Type*} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K) {p : ℕ} (hp : Nat.Prime p)
    (hrel : ¬ p ∣ H.relIndex K) :
    p ∣ H.index ↔ p ∣ K.index := by
  constructor
  · intro hH
    have hmul : p ∣ H.relIndex K * K.index := by
      rw [Subgroup.relIndex_mul_index hHK]
      exact hH
    rcases hp.dvd_mul.mp hmul with hp_rel | hp_K
    · exact (hrel hp_rel).elim
    · exact hp_K
  · intro hK
    rw [← Subgroup.relIndex_mul_index hHK]
    exact dvd_mul_of_dvd_right hK (H.relIndex K)

/--
@isnad1 id=iff.4h5v.s6.bebbe6d97495 from=translated src=- shape=d7015ecb vocab=4451cf85
-/
theorem subgroup_index_prime_dvd_iff_of_relIndex_dvd_two_pow {G : Type*} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K) {p r : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2)
    (hrel : H.relIndex K ∣ 2 ^ r) :
    p ∣ H.index ↔ p ∣ K.index :=
  subgroup_index_prime_dvd_iff_of_not_dvd_relIndex hHK hp
    (prime_not_dvd_of_dvd_two_pow hp hp_odd hrel)

end BernoulliRegular
