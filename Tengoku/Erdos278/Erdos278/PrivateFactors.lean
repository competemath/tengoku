import Tengoku.Erdos278.Erdos278.Core
import Tengoku.Seed.Data.Nat.Factorial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- Multiplying each modulus by a factor private to that modulus preserves
all pairwise gcds. The factors need not be prime.-/
theorem private_factors_gcd (a b u v : ℕ)
    (hub : u.Coprime b) (hva : v.Coprime a) (huv : u.Coprime v) :
    (a * u).gcd (b * v) = a.gcd b := by
  rw [Nat.Coprime.gcd_mul_right_cancel a (hub.mul_right huv),
    Nat.Coprime.gcd_mul_right_cancel_right b hva]

theorem private_factors_compatibility {ι : Type*} (n t : ι → ℕ)
    (hbase : ∀ i j, (t i).Coprime (n j))
    (htags : ∀ i j, i ≠ j → (t i).Coprime (t j))
    (a : ι → ℤ) (i j : ι) :
    Compatible (fun k => n k * t k) a i j ↔ Compatible n a i j := by
  by_cases hij : i = j
  · subst j
    exact ⟨fun _ => Int.ModEq.refl _, fun _ => Int.ModEq.refl _⟩
  · unfold Compatible
    rw [private_factors_gcd (n i) (n j) (t i) (t j)
      (hbase i j) (hbase j i) (htags i j hij)]

theorem private_factors_injective {ι : Type*} (n t : ι → ℕ)
    (hbase : ∀ i j, (t i).Coprime (n j))
    (htags : ∀ i j, i ≠ j → (t i).Coprime (t j)) (ht : ∀ i, 1 < t i) :
    Function.Injective (fun i => n i * t i) := by
  intro i j heq
  change n i * t i = n j * t j at heq
  by_contra hij
  have hc : (t i).Coprime (n j * t j) := (hbase i j).mul_right (htags i j hij)
  have hd : t i ∣ n j * t j := by
    rw [← heq]
    exact dvd_mul_left _ _
  have := hc.eq_one_of_dvd hd
  have := ht i
  omega

/-- An elementary way to generate private factors, without prime search.-/
def taggingScale {r : ℕ} (n : Fin r → ℕ) : ℕ := r.factorial * ∏ i, n i

def separationTag {r : ℕ} (n : Fin r → ℕ) (i : Fin r) : ℕ :=
  1 + (i.val + 1) * taggingScale n

theorem affine_tags_coprime (K i j : ℕ) (hdiff : j - i ∣ K) :
    (1 + i * K).Coprime (1 + j * K) := by
  let a := 1 + i * K
  let b := 1 + j * K
  let d := a.gcd b
  have haK : a.Coprime K := by simp [a]
  have hda : d ∣ a := Nat.gcd_dvd_left a b
  have hdb : d ∣ b := Nat.gcd_dvd_right a b
  have hdK : d.Coprime K := Nat.Coprime.of_dvd_left hda haK
  have hdiff' : d ∣ (j - i) * K := by
    have h := Nat.dvd_sub hdb hda
    change d ∣ 1 + j * K - (1 + i * K) at h
    have heq : 1 + j * K - (1 + i * K) = j * K - i * K := by omega
    simpa only [heq, Nat.sub_mul] using h
  have hsmall : d ∣ j - i := hdK.dvd_of_dvd_mul_right hdiff'
  exact Nat.eq_one_of_dvd_coprimes haK hda (hsmall.trans hdiff)

theorem separation_tags_coprime {r : ℕ} (n : Fin r → ℕ) (i j : Fin r) (hij : i ≠ j) :
    (separationTag n i).Coprime (separationTag n j) := by
  have hlt (i j : Fin r) (hij : i < j) :
      (separationTag n i).Coprime (separationTag n j) := by
    apply affine_tags_coprime
    have hd : j.val + 1 - (i.val + 1) ∣ r.factorial :=
      Nat.dvd_factorial (by omega) (by omega)
    exact dvd_mul_of_dvd_left hd _
  rcases lt_trichotomy i j with h | h | h
  · exact hlt i j h
  · exact (hij h).elim
  · exact (hlt j i h).symm

theorem separation_tags_avoid_moduli {r : ℕ} (n : Fin r → ℕ) (i j : Fin r) :
    (separationTag n i).Coprime (n j) := by
  have hprod : n j ∣ ∏ k, n k := Finset.dvd_prod_of_mem n (mem_univ j)
  have hd : n j ∣ taggingScale n := dvd_mul_of_dvd_right hprod _
  apply Nat.Coprime.of_dvd_right hd
  simp [separationTag]

theorem separation_tags_gt_one {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) (i : Fin r) :
    1 < separationTag n i := by
  have hK : 0 < taggingScale n :=
    Nat.mul_pos (Nat.factorial_pos r)
      (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => (hn j).ne')))
  have hp : 0 < (i.val + 1) * taggingScale n := Nat.mul_pos (by omega) hK
  unfold separationTag
  omega

/-- Every positive list can be replaced by positive, pairwise distinct moduli
with exactly the same intersection graph for every integer residue tuple.
The explicit factors are 1+(i+1)*r!*product(n). This does not preserve densities,
but it does preserve pairwise-disjoint feasibility.-/
theorem distinct_moduli_preserving_compatibility {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) :
    ∃ m : Fin r → ℕ, (∀ i, 0 < m i) ∧ Function.Injective m ∧
      ∀ a : Fin r → ℤ, ∀ i j, Compatible m a i j ↔ Compatible n a i j := by
  let t := separationTag n
  refine ⟨fun i => n i * t i, ?_, ?_, ?_⟩
  · intro i
    exact Nat.mul_pos (hn i) (Nat.lt_trans Nat.zero_lt_one (separation_tags_gt_one n hn i))
  · exact private_factors_injective n t (separation_tags_avoid_moduli n)
      (separation_tags_coprime n) (separation_tags_gt_one n hn)
  · exact private_factors_compatibility n t (separation_tags_avoid_moduli n)
      (separation_tags_coprime n)

end Erdos278
