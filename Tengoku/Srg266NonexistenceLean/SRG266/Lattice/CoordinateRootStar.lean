/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanARootEndpoints
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=eq.0h4v.s9.1f65e3e5bb90 from=translated src=- shape=2c31e329 vocab=5281ff78
-/
theorem coordinate_root_pair {n : ℕ} (p q : Fin n) (x : Fin n → ℚ) :
    standardRatForm n (Pi.single p 1-Pi.single q 1) x = x p-x q := by
  classical
  simp [standardRatForm_apply, Pi.single_apply, ite_mul]

/--
@isnad1 id=or.1h5v.s9.2a1f1063acbd from=translated src=- shape=d824315f vocab=5281ff78
-/
theorem coordinate_root_pair_one {n : ℕ} (p q r s : Fin n)
    (h : standardRatForm n (Pi.single p 1-Pi.single q 1)
      (Pi.single r 1-Pi.single s 1) = 1) :
    (p = r ∧ q ≠ s) ∨ (q = s ∧ p ≠ r) := by
  classical
  rw [coordinate_root_pair] at h
  simp only [Pi.sub_apply, Pi.single_apply] at h
  split_ifs at h <;> norm_num at h <;> aesop

/--
@isnad1 id=or.2h6v.s6.f0f2ac82a7c6 from=translated src=- shape=b2b90d6b vocab=775246a5
-/
theorem pairwise_endpoints_star {ι κ : Type*} (p q : ι → κ) (a b : ι)
    (hab : a ≠ b)
    (hpq : ∀ i j, i ≠ j → (p i = p j ∧ q i ≠ q j) ∨ (q i = q j ∧ p i ≠ p j)) :
    ((∀ i, p i = p a) ∧ Function.Injective q) ∨
      ((∀ i, q i = q a) ∧ Function.Injective p) := by
  classical
  have common (p q : ι → κ)
      (hpair : ∀ i j, i ≠ j → (p i = p j ∧ q i ≠ q j) ∨
        (q i = q j ∧ p i ≠ p j))
      (hp : p a = p b) (hq : q a ≠ q b) :
      (∀ i, p i = p a) ∧ Function.Injective q := by
    have hall (i : ι) : p i = p a := by
      by_contra hi
      have hia : i ≠ a := fun h => hi (congrArg p h)
      have hib : i ≠ b := fun h => hi ((congrArg p h).trans hp.symm)
      have hqa : q i = q a := (hpair i a hia).resolve_left (fun h => hi h.1) |>.1
      have hqb : q i = q b := (hpair i b hib).resolve_left
        (fun h => hi (h.1.trans hp.symm)) |>.1
      exact hq (hqa.symm.trans hqb)
    refine ⟨hall, fun i j hij => ?_⟩
    by_contra hne
    rcases hpair i j hne with h | h
    · exact h.2 hij
    · exact h.2 ((hall i).trans (hall j).symm)
  rcases hpq a b hab with h | h
  · exact Or.inl (common p q hpq h.1 h.2)
  · exact Or.inr (common q p (fun i j hij => (hpq i j hij).symm) h.1 h.2)

/--
@isnad1 id=ex.3h6v.s10.6bd5db71ef9e from=translated src=- shape=767e47e7 vocab=8fdf4fe2
-/
theorem coordinate_root_star_equal_coordinates {m n : ℕ}
    (p q : Fin m → Fin n) (a b : Fin m) (hab : a ≠ b)
    (hne : ∀ i, p i ≠ q i)
    (hpair : ∀ i j, i ≠ j → standardRatForm n
      (Pi.single (p i) 1-Pi.single (q i) 1)
      (Pi.single (p j) 1-Pi.single (q j) 1) = 1) :
    ∃ f : Fin (m+1) ↪ Fin n, ∀ x : Fin n → ℚ,
      (∀ i, standardRatForm n (Pi.single (p i) 1-Pi.single (q i) 1) x = 0) →
      ∀ j, x (f j) = x (f 0) := by
  classical
  have build (p q : Fin m → Fin n) (hneq : ∀ i, p i ≠ q i)
      (hp : ∀ i, p i = p a) (hq : Function.Injective q) :
      ∃ f : Fin (m+1) ↪ Fin n, ∀ x : Fin n → ℚ,
        (∀ i, x (p i) = x (q i)) → ∀ j, x (f j) = x (f 0) := by
    have hout : p a ∉ Set.range q := by
      rintro ⟨i, hi⟩
      exact hneq i ((hp i).trans hi.symm)
    refine ⟨⟨Fin.cons (p a) q, Fin.cons_injective_of_injective hout hq⟩, ?_⟩
    intro x hx j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · change x (q i) = x (p a)
      rw [← hx i, hp i]
  have hstar := pairwise_endpoints_star p q a b hab
    (fun i j hij => coordinate_root_pair_one _ _ _ _ (hpair i j hij))
  rcases hstar with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · obtain ⟨f, hf⟩ := build p q hne hp hq
    refine ⟨f, fun x hx => hf x (fun i => ?_)⟩
    exact sub_eq_zero.mp ((coordinate_root_pair _ _ _).symm.trans (hx i))
  · obtain ⟨f, hf⟩ := build q p (fun i => (hne i).symm) hq hp
    refine ⟨f, fun x hx => hf x (fun i => ?_)⟩
    exact (sub_eq_zero.mp ((coordinate_root_pair _ _ _).symm.trans (hx i))).symm

end SRG266.Lattice
