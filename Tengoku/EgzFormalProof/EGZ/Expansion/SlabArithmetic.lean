import Tengoku.EgzFormalProof.EGZ.Expansion.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace EGZ.HasBoundedRepresentative

/--
@isnad1 id=hasbound.0h2v.s4.bb2d7bcd4035 from=translated src=- shape=5eda6d4b vocab=adef3400
-/
theorem zero (p K : ℕ) : HasBoundedRepresentative p K 0 := ⟨0, by simp, by simp⟩

/--
@isnad1 id=hasbound.2h4v.s4.5ebc378124b3 from=translated src=- shape=f03ddca1 vocab=da461cad
-/
theorem mono {p K L : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a)
    (hKL : K ≤ L) : HasBoundedRepresentative p L a := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨z, hz.trans hKL, rfl⟩

/--
@isnad1 id=hasbound.1h3v.s5.bd8732c275e6 from=translated src=- shape=a5522ebe vocab=6dd5285d
-/
theorem neg {p K : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a) :
    HasBoundedRepresentative p K (-a) := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨-z, by simpa using hz, by simp⟩

/--
@isnad1 id=hasbound.2h5v.s5.815a1bc0ae34 from=translated src=- shape=d2dddefd vocab=f30312af
-/
theorem add {p K L : ℕ} {a b : ZMod p}
    (ha : HasBoundedRepresentative p K a) (hb : HasBoundedRepresentative p L b) :
    HasBoundedRepresentative p (K + L) (a + b) := by
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  exact ⟨z + w, (Int.natAbs_add_le z w).trans (Nat.add_le_add hz hw), by simp⟩

/--
@isnad1 id=hasbound.2h5v.s5.d0d23f7ccc72 from=translated src=- shape=d2dddefd vocab=9367419f
-/
theorem sub {p K L : ℕ} {a b : ZMod p}
    (ha : HasBoundedRepresentative p K a) (hb : HasBoundedRepresentative p L b) :
    HasBoundedRepresentative p (K + L) (a - b) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

/--
@isnad1 id=hasbound.1h4v.s6.f991f4dbbccf from=translated src=- shape=2291db9d vocab=bff04aab
-/
theorem int_mul {p K : ℕ} {a : ZMod p} (ha : HasBoundedRepresentative p K a) (n : ℤ) :
    HasBoundedRepresentative p (n.natAbs * K) ((n : ZMod p) * a) := by
  obtain ⟨z, hz, rfl⟩ := ha
  exact ⟨n * z, by rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ hz, by simp⟩

/--
@isnad1 id=hasbound.1h5v.s6.382f074ac9af from=translated src=- shape=2d80578b vocab=369ec1de
-/
theorem sum {p : ℕ} {I : Type*} (s : Finset I) (K : I → ℕ) (a : I → ZMod p)
    (h : ∀ i ∈ s, HasBoundedRepresentative p (K i) (a i)) :
    HasBoundedRepresentative p (∑ i ∈ s, K i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero p 0
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (by simp)).add (ih (fun j hj ↦ h j (by simp [hj])))

end EGZ.HasBoundedRepresentative
