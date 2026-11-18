import Tengoku.EgzFormalProof.EGZ.Expansion.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selecting submultisets with prescribed fibre masses

All selections are made in natural multiplicities, so coincident vector
values are still allowed to occupy distinct positions.
-/

open scoped BigOperators

namespace EGZ.Expansion

/--
@isnad1 id=ex.1h3v.s5.5b479fa0a2ef from=translated src=- shape=06e75905 vocab=7e465f3f
-/
theorem exists_subweight_of_mass_le {A : Type*} [Fintype A]
    (w : A → ℕ) {n : ℕ} (hn : n ≤ natMass w) :
    ∃ u : A → ℕ, u ≤ w ∧ natMass u = n := by
  classical
  let Slots := Σ a : A, Fin (w a)
  have hcard : Fintype.card Slots = natMass w := by
    simp [Slots, natMass, Fintype.card_sigma]
  obtain ⟨I, _hI, hIn⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset Slots)) (by simpa only [Finset.card_univ, hcard] using hn)
  let selected : Slots → ℕ := fun i ↦ if i ∈ I then 1 else 0
  refine ⟨pushWeight Sigma.fst selected, ?_, ?_⟩
  · have hle : selected ≤ fun _ ↦ 1 := by intro i; dsimp [selected]; split_ifs <;> omega
    apply (pushWeight_mono Sigma.fst hle).trans
    intro a
    change (∑ x : (Σ a : A, Fin (w a)), if x.1 = a then (1 : ℕ) else 0) ≤ w a
    rw [Fintype.sum_sigma]
    calc
      (∑ x, ∑ _i : Fin (w x), if x = a then (1 : ℕ) else 0) =
          ∑ x, if x = a then w x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = a <;> simp [hx]
      _ = w a := by simp
      _ ≤ w a := le_rfl
  · rw [natMass_pushWeight]
    simpa [natMass, selected] using hIn

/-- Every collection of fibre counts dominated by the available counts
can be realized by a submultiset.
@isnad1 id=ex.1h5v.s6.b174d9d1de1d from=translated src=- shape=99430db0 vocab=d28f4c02
-/
theorem exists_subweight_pushWeight {A B : Type*} [Fintype A]
    (π : A → B) (w : A → ℕ) (a : B → ℕ) (ha : a ≤ pushWeight π w) :
    ∃ u : A → ℕ, u ≤ w ∧ pushWeight π u = a := by
  classical
  let fibre (b : B) (x : A) := if π x = b then w x else 0
  have hex (b : B) : ∃ u : A → ℕ, u ≤ fibre b ∧ natMass u = a b :=
    exists_subweight_of_mass_le (fibre b) (ha b)
  choose u hu hm using hex
  have hzero (b : B) (x : A) (hx : π x ≠ b) : u b x = 0 := by
    have h := hu b x
    simp only [fibre, ite_eq_right hx, Nat.le_zero] at h
    exact h
  refine ⟨fun x ↦ u (π x) x, ?_, ?_⟩
  · intro x
    simpa only [fibre, ite_eq_left rfl] using hu (π x) x
  · funext b
    calc
      pushWeight π (fun x ↦ u (π x) x) b = natMass (u b) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : π x = b
        · simp [hx]
        · simp [hx, hzero b x hx]
      _ = a b := hm b

/--
@isnad1 id=eq.0h5v.s6.0f93e1b18417 from=translated src=- shape=6b1661e0 vocab=974d3351
-/
theorem pushWeight_add {A B : Type*} [Fintype A]
    (π : A → B) (u w : A → ℕ) :
    pushWeight π (u + w) = pushWeight π u + pushWeight π w := by
  classical
  funext b
  simp only [pushWeight, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/--
@isnad1 id=eq.1h5v.s6.4411ea6f3676 from=translated src=- shape=d7eb0f29 vocab=7c253f46
-/
theorem pushWeight_sub {A B : Type*} [Fintype A]
    (π : A → B) {u w : A → ℕ} (hu : u ≤ w) :
    pushWeight π (w - u) = pushWeight π w - pushWeight π u := by
  classical
  funext b
  simp only [pushWeight, Pi.sub_apply]
  rw [← Finset.sum_tsub_distrib]
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  · intro x _
    split_ifs
    · exact hu x
    · exact le_rfl

/--
@isnad1 id=eq.0h6v.s6.21d795f15d2f from=translated src=- shape=cee0daf4 vocab=3d8d2ec5
-/
theorem pushWeight_sum {A B I : Type*} [Fintype A]
    (π : A → B) (s : Finset I) (w : I → A → ℕ) :
    pushWeight π (∑ i ∈ s, w i) = ∑ i ∈ s, pushWeight π (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext b; simp [pushWeight]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, pushWeight_add, ih]

end EGZ.Expansion
