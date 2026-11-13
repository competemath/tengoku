import Tengoku.Seed.Combinatorics.Pigeonhole

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent coordinates selected from symmetric rows

Selecting one entry per row of a symmetric matrix can duplicate each
unordered coordinate at most twice. The canonical lower-triangular
coordinates therefore retain at least half as many distinct entries.
This is the elementary counting step in Latała--van Handel--Youssef,
arXiv:1711.00807v2, Section 3.1.
-/

namespace Finset

/-- One selected unordered entry per distinct row gives at least half as
many distinct canonical coordinates. Diagonal entries need no exception.
@isnad1 id=le.0h3v.s6.f35085603796 from=translated src=- shape=ae54436d vocab=7c756060
-/
theorem card_le_two_mul_card_image_canonicalPair {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (j : ι → ι) :
    s.card ≤ 2 * (s.image (fun i => (max i (j i), min i (j i)))).card := by
  classical
  let f : ι → ι × ι := fun i => (max i (j i), min i (j i))
  change s.card ≤ 2 * (s.image f).card
  by_contra h
  have hlt : (s.image f).card * 2 < s.card := by omega
  obtain ⟨e, _, he⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun i hi => mem_image_of_mem f hi) hlt
  have hsub : s.filter (fun i => f i = e) ⊆ {e.1, e.2} := by
    intro i hi
    have hfi := (mem_filter.mp hi).2
    apply mem_insert.mpr
    by_cases hij : j i ≤ i
    · left
      have hfst := congrArg Prod.fst hfi
      simpa only [f, max_eq_left hij] using hfst
    · right
      apply mem_singleton.mpr
      have hsnd := congrArg Prod.snd hfi
      simpa only [f, min_eq_left (le_of_not_ge hij)] using hsnd
  have hc : (s.filter (fun i => f i = e)).card ≤ 2 :=
    (card_le_card hsub).trans (by by_cases heq : e.1 = e.2 <;> simp [heq])
  omega

end Finset
