import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ

set_option autoImplicit false

namespace EsymmCongAux

/--
@isnad1 id=mem.1h5v.s7.90185f31807b from=translated src=- shape=4c906099 vocab=0a0a35f4
-/
theorem prod_mem_pow {A : Type} [CommRing A] (I : Ideal A) {ι : Type} (t : Finset ι) (y : ι → A)
    (hy : ∀ i ∈ t, y i ∈ I) : (∏ i ∈ t, y i) ∈ I ^ t.card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact Ideal.mul_mem_mul (hy a (Finset.mem_insert_self a t))
      (ih fun i hi => hy i (Finset.mem_insert_of_mem hi))

/--
@isnad1 id=mem.2h6v.s8.7bb682b898de from=translated src=- shape=230e3467 vocab=469dcc50
-/
theorem prod_sub_prod_mem_pow_succ {A : Type} [CommRing A] (I : Ideal A) {ι : Type} (t : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ t, z i ∈ I) (hyz : ∀ i ∈ t, y i - z i ∈ I ^ 2) :
    (∏ i ∈ t, y i) - (∏ i ∈ t, z i) ∈ I ^ (t.card + 1) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hy : ∀ i ∈ insert a t, y i ∈ I := by
      intro i hi
      have e : y i = (y i - z i) + z i := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hyz i hi)) (hz i hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have e : y a * ∏ i ∈ t, y i - z a * ∏ i ∈ t, z i =
        (y a - z a) * ∏ i ∈ t, y i + z a * (∏ i ∈ t, y i - ∏ i ∈ t, z i) := by ring
    rw [e, show t.card + 1 + 1 = 2 + t.card by ring]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_add]
      exact Ideal.mul_mem_mul (hyz a (Finset.mem_insert_self a t))
        (prod_mem_pow I t y fun i hi => hy i (Finset.mem_insert_of_mem hi))
    · rw [show 2 + t.card = 1 + (t.card + 1) by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul (hz a (Finset.mem_insert_self a t))
        (ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) (fun i hi => hyz i (Finset.mem_insert_of_mem hi)))

end EsymmCongAux

open EsymmCongAux in
/--
@isnad1 id=mem.2h7v.s8.8193a5aebe6e from=translated src=- shape=39b952a8 vocab=ee6ace69
-/
theorem solution
    (A : Type) [CommRing A] (I : Ideal A) (ι : Type) (s : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ s, z i ∈ I) (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) (k : ℕ) :
    (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1) := by
  classical
  rw [Finset.esymm_map_val, Finset.esymm_map_val, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htk⟩ := ht
  rw [← htk]
  exact prod_sub_prod_mem_pow_succ I t y z (fun i hi => hz i (hts hi)) (fun i hi => hyz i (hts hi))
