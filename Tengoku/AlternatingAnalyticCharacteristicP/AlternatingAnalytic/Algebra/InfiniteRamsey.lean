import Tengoku.Seed.Data.Fintype.Pigeonhole
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Finset.Range
import Tengoku.Seed.Data.Set.Finite.Basic
import Tengoku.Seed.Order.Monotone.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Infinite Ramsey theorem for fixed-size subsets

Every finite coloring of the `n`-element subsets of an infinite set of natural
numbers has an infinite homogeneous subset. This is the form of Ramsey's theorem used
in Lemma B.10.
-/

namespace InfiniteRamsey

/-- Infinite Ramsey's theorem inside any prescribed infinite subset of `ℕ`.
@isnad1 id=ex.1h4v.s6.bfaae1e2594c from=translated src=- shape=976b84a0 vocab=00410216
-/
theorem exists_infinite_homogeneous_subset {C : Type*} [Finite C] (n : ℕ)
    (f : Finset ℕ → C) (A : Set ℕ) (hA : A.Infinite) :
    ∃ H : Set ℕ, H ⊆ A ∧ H.Infinite ∧
      ∃ c : C, ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ H → s.card = n → f s = c := by
  classical
  induction n generalizing f A with
  | zero =>
      refine ⟨A, Set.Subset.rfl, hA, f ∅, ?_⟩
      intro s _ hs
      have : s = ∅ := Finset.card_eq_zero.mp hs
      simp [this]
  | succ n ih =>
      let State := {X : Set ℕ // X.Infinite ∧ X ⊆ A}
      have step : ∀ X : State, ∃ a : ℕ, ∃ c : C, ∃ Y : State,
          a ∈ X.val ∧ Y.val ⊆ X.val ∧ (∀ b ∈ Y.val, a < b) ∧
            ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ Y.val → s.card = n →
              f (insert a s) = c := by
        intro X
        obtain ⟨a, ha⟩ := X.property.1.nonempty
        have htail : (X.val \ (Finset.range (a + 1) : Set ℕ)).Infinite :=
          X.property.1.sdiff (Finset.finite_toSet _)
        obtain ⟨Y, hYsub, hYinf, c, hYcolor⟩ :=
          ih (fun s => f (insert a s)) (X.val \ (Finset.range (a + 1) : Set ℕ)) htail
        refine ⟨a, c, ⟨Y, hYinf, ?_⟩, ha, ?_, ?_, hYcolor⟩
        · exact fun b hb => X.property.2 (hYsub hb).1
        · exact fun b hb => (hYsub hb).1
        · intro b hb
          have hbnot := (hYsub hb).2
          simp only [Finset.mem_coe, Finset.mem_range, not_lt] at hbnot
          omega
      choose a color next ha hnext hlt hcolor using step
      let q : ℕ → State := Nat.rec ⟨A, hA, Set.Subset.rfl⟩ (fun _ X => next X)
      let u : ℕ → ℕ := fun i => a (q i)
      have hqnext (i : ℕ) : (q (i + 1)).val ⊆ (q i).val := hnext (q i)
      have hq : Antitone (fun i => (q i).val) := antitone_nat_of_succ_le hqnext
      have hu_mem {i j : ℕ} (hij : i ≤ j) : u j ∈ (q i).val :=
        hq hij (ha (q j))
      have hu_strict : StrictMono u := by
        apply strictMono_nat_of_lt_succ
        intro i
        exact hlt (q i) (u (i + 1)) (ha (q (i + 1)))
      obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber (fun i : ℕ => color (q i))
      let I : Set ℕ := {i | color (q i) = c}
      have hI : I.Infinite := by
        exact Set.infinite_coe_iff.mp hc
      refine ⟨u '' I, ?_, hI.image hu_strict.injective.injOn, c, ?_⟩
      · rintro b ⟨i, _, rfl⟩
        exact (q i).property.2 (ha (q i))
      · intro s hs hcard
        have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
        let b := s.min' hsne
        have hb : b ∈ s := Finset.min'_mem s hsne
        obtain ⟨i, hi, hui⟩ := hs hb
        have hrest : (↑(s.erase b) : Set ℕ) ⊆ (next (q i)).val := by
          intro x hx
          have hxmem := Finset.mem_erase.mp hx
          obtain ⟨j, _, huj⟩ := hs hxmem.2
          have hbx : b < x := lt_of_le_of_ne (Finset.min'_le s x hxmem.2) hxmem.1.symm
          have hij : i < j := hu_strict.lt_iff_lt.mp (by simpa [hui, huj] using hbx)
          exact huj ▸ hu_mem (Nat.succ_le_of_lt hij)
        have hrestcard : (s.erase b).card = n := by
          have := Finset.card_erase_add_one hb
          omega
        have h := hcolor (q i) (s.erase b) hrest hrestcard
        change f (insert (u i) (s.erase b)) = color (q i) at h
        rw [hui, Finset.insert_erase hb] at h
        exact h.trans hi

/-- Every finite coloring of fixed-size subsets of `ℕ` has an infinite homogeneous set.
@isnad1 id=ex.0h3v.s5.102eed3c5227 from=translated src=- shape=947d9654 vocab=00410216
-/
theorem exists_infinite_homogeneous {C : Type*} [Finite C] (n : ℕ)
    (f : Finset ℕ → C) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∃ c : C, ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ H → s.card = n → f s = c := by
  obtain ⟨H, _, hH, c, hc⟩ := exists_infinite_homogeneous_subset n f Set.univ Set.infinite_univ
  exact ⟨H, hH, c, hc⟩

end InfiniteRamsey
