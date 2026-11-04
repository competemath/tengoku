import Tengoku.ErdosLean.ErdosLean.Erdos956.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #956 — Part 11: `|triples k| = M_k`

Fibre over `i`: `r ∈ [0, k-i]` (`k+1-i` values) and `s ∈ [i², k²]` (`k²+1-i²` values).

-/

namespace Erdos956

open Finset

/--
@isnad1 id=eq.0h2v.s6.e0a83f64fe0f from=translated src=- shape=56873488 vocab=9e7784a1
-/
lemma altTriplesCard_card_r (k i : ℕ) :
    ((range (k + 1)).filter fun r => r + i ≤ k).card = k + 1 - i := by
  have : (range (k + 1)).filter (fun r => r + i ≤ k) = range (k + 1 - i) := by
    ext r; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

/--
@isnad1 id=eq.0h2v.s7.f34b30db669e from=translated src=- shape=dc986259 vocab=42219842
-/
lemma altTriplesCard_card_s (k i : ℕ) :
    ((range (k ^ 2 + 1)).filter fun s => i ^ 2 ≤ s).card = k ^ 2 + 1 - i ^ 2 := by
  have : (range (k ^ 2 + 1)).filter (fun s => i ^ 2 ≤ s) = Ico (i ^ 2) (k ^ 2 + 1) := by
    ext s; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

/--
@isnad1 id=eq.0h1v.s3.d692a1809714 from=translated src=- shape=614426fb vocab=e96e1cfc
-/
theorem card_triples (k : ℕ) : (triples k).card = Mk k := by
  unfold triples Mk
  rw [card_filter, sum_product]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter]
  have : ((range (k + 1) ×ˢ range (k ^ 2 + 1)).filter
      fun x : ℕ × ℕ => x.1 + i ≤ k ∧ i ^ 2 ≤ x.2) =
      ((range (k + 1)).filter fun r => r + i ≤ k) ×ˢ
        ((range (k ^ 2 + 1)).filter fun s => i ^ 2 ≤ s) := by
    ext ⟨r, s⟩; simp only [mem_filter, mem_product]; tauto
  rw [this, card_product, altTriplesCard_card_r, altTriplesCard_card_s]

end Erdos956
