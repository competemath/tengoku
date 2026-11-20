/-
A307917: directed paths in the crown graph correspond bijectively to pairs
(side of the first vertex, sequence of indices).
-/
import Tengoku.OeisLean.OeisLean.A307917.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A307917.card_dirPaths` (it only prints; the queue checks the axioms of every declaration). -/

namespace A307917
namespace Paths

variable {n L : ℕ}

/-- The path with first side `p.1` and index sequence `p.2`: sides alternate.-/
def Φ (p : Bool × (Fin L → Fin n)) : Fin L → V n :=
  fun i => (xor p.1 (decide (i.val % 2 = 1)), p.2 i)

/--
@isnad1 id=injectiv.1h2v.s4.019da8b67ba6 from=translated src=- shape=c439d944 vocab=68d4878d
-/
theorem Φ_injective (hL : 1 ≤ L) :
    Function.Injective (Φ : Bool × (Fin L → Fin n) → (Fin L → V n)) := by
  rintro ⟨s, z⟩ ⟨t, w⟩ h
  have h0 : xor s (decide ((0 : ℕ) % 2 = 1)) = xor t (decide ((0 : ℕ) % 2 = 1)) :=
    congrArg Prod.fst (congrFun h ⟨0, hL⟩)
  have hz : z = w := by
    funext i
    exact congrArg Prod.snd (congrFun h i)
  have hs : s = t := by simpa using h0
  rw [hs, hz]

/--
@isnad1 id=ne.1h3v.s6.b01d9adabbb2 from=translated src=- shape=91ad264c vocab=b1397754
-/
theorem side_ne (s : Bool) (a b : ℕ) (h : a % 2 ≠ b % 2) :
    xor s (decide (a % 2 = 1)) ≠ xor s (decide (b % 2 = 1)) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · rw [ha, hb]; cases s <;> simp
  · rw [ha, hb]; cases s <;> simp
  · omega

/--
@isnad1 id=iff.0h4v.s6.80a0944889ba from=translated src=- shape=72ce6721 vocab=5555eaff
-/
theorem Φ_mem_iff (s : Bool) (z : Fin L → Fin n) :
    Φ (s, z) ∈ dirPaths n L ↔
      Sp z ∧ ∀ i j : Fin L, i.val + 1 = j.val → i.val < L - 1 → z i ≠ z j := by
  simp only [dirPaths, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hinj, hadj⟩
    refine ⟨?_, ?_⟩
    · intro i j hij hpar heq
      apply hij
      apply hinj
      show (xor s (decide (i.val % 2 = 1)), z i) = (xor s (decide (j.val % 2 = 1)), z j)
      rw [hpar, heq]
    · intro i j hij _
      exact (hadj i j hij).2
  · rintro ⟨hsp, hne⟩
    refine ⟨?_, ?_⟩
    · intro i j h
      by_contra hij
      have h1 : xor s (decide (i.val % 2 = 1)) = xor s (decide (j.val % 2 = 1)) :=
        congrArg Prod.fst h
      have h2 : z i = z j := congrArg Prod.snd h
      by_cases hpar : i.val % 2 = j.val % 2
      · exact hsp i j hij hpar h2
      · exact side_ne s _ _ hpar h1
    · intro i j hij
      refine ⟨?_, ?_⟩
      · exact side_ne s _ _ (by omega)
      · exact hne i j hij (by have := j.isLt; omega)

/--
@isnad1 id=eq.2h4v.s7.434cf7ef4bd6 from=translated src=- shape=5a140ac6 vocab=b5d3831c
-/
theorem step (a b c : Bool) (k : ℕ) (h1 : a ≠ b) (h2 : a = xor c (decide (k % 2 = 1))) :
    b = xor c (decide ((k + 1) % 2 = 1)) := by
  subst h2
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk
  · have hk' : (k + 1) % 2 = 1 := by omega
    rw [hk] at h1; rw [hk']
    revert h1; cases b <;> cases c <;> simp
  · have hk' : (k + 1) % 2 = 0 := by omega
    rw [hk] at h1; rw [hk']
    revert h1; cases b <;> cases c <;> simp

/--
@isnad1 id=eq.3h4v.s7.c7095c17fe91 from=translated src=- shape=0df30d65 vocab=267d9ec4
-/
theorem side_eq {f : Fin L → V n} (hf : f ∈ dirPaths n L) (hL : 1 ≤ L) :
    ∀ k (h : k < L), (f ⟨k, h⟩).1 = xor (f ⟨0, hL⟩).1 (decide (k % 2 = 1)) := by
  simp only [dirPaths, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  intro k
  induction k with
  | zero => intro h; simp
  | succ k ih =>
    intro h
    exact step _ _ _ k (hf.2 ⟨k, by omega⟩ ⟨k + 1, h⟩ rfl).1 (ih (by omega))

end Paths

/--
@isnad1 id=eq.1h2v.s5.6477f2dab7bc from=translated src=- shape=f91d1de1 vocab=eb2dfa1b
-/
theorem card_dirPaths (n L : ℕ) (hL : 1 ≤ L) : (dirPaths n L).card = 2 * B n L (L - 1) := by
  have key : dirPaths n L =
      (Finset.univ ×ˢ (Finset.univ.filter fun z : Fin L → Fin n =>
        Sp z ∧ ∀ i j : Fin L, i.val + 1 = j.val → i.val < L - 1 → z i ≠ z j)).image
        Paths.Φ := by
    ext f
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.exists]
    constructor
    · intro hf
      have e : Paths.Φ ((f ⟨0, hL⟩).1, fun i => (f i).2) = f := by
        funext i
        exact Prod.ext (Paths.side_eq hf hL i.val i.isLt).symm rfl
      refine ⟨_, _, ?_, e⟩
      rw [← Paths.Φ_mem_iff, e]
      exact hf
    · rintro ⟨s, z, hz, rfl⟩
      exact (Paths.Φ_mem_iff s z).2 hz
  rw [key, Finset.card_image_of_injective _ (Paths.Φ_injective hL), Finset.card_product,
    Finset.card_univ, Fintype.card_bool]
  rfl

end A307917

