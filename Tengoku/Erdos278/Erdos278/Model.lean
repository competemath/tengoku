import Tengoku.Erdos278.Erdos278.MILP
import Tengoku.Erdos278.Erdos278.Maximization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

abbrev PairIndex (r : ℕ) := {ij : Fin r × Fin r // ij.1 < ij.2}
abbrev CliqueIndex (r : ℕ) := ↥((univ : Finset (Fin r)).powerset.filter (·.Nonempty))
abbrev InternalPair {r : ℕ} (s : Finset (Fin r)) :=
  {e : PairIndex r // e.1.1 ∈ s ∧ e.1.2 ∈ s}

theorem clique_iff_internal_pairs {r : ℕ} (s : Finset (Fin r))
    (n : Fin r → ℕ) (x : Fin r → ℤ) :
    IsClique n x s ↔ ∀ e : InternalPair s, Compatible n x e.1.1.1 e.1.1.2 := by
  constructor
  · intro h e
    exact h _ e.2.1 _ e.2.2
  · intro h i hi j hj
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact h ⟨⟨(i, j), hij⟩, hi, hj⟩
    · exact Int.ModEq.refl _
    · have hc := (h ⟨⟨(j, i), hji⟩, hj, hi⟩).symm
      simpa only [Compatible, Nat.gcd_comm] using hc

/-- A redundant continuous indicator is included for every nonempty subset.
For singletons it is forced to 1, and for pairs it is forced to the corresponding
binary edge variable, so these extra continuous variables can be eliminated.
This leaves exactly the formulation in section 8. No extra integer variables
are introduced by this uniform indexing.-/
def ModelFeasible {r : ℕ} (n : Fin r → ℕ) (i₀ : Fin r)
    (x : Fin r → ℤ) (q y : PairIndex r → ℤ) (z : CliqueIndex r → ℝ) : Prop :=
  x i₀ = 0 ∧
  (∀ i, 0 ≤ x i ∧ x i < interactionModulus n i) ∧
  (∀ e, y e = 0 ∨ y e = 1) ∧
  (∀ e, pairConstraint ((n e.1.1).gcd (n e.1.2)) (x e.1.1 - x e.1.2) (q e) (y e)) ∧
  (∀ S, andConstraints (fun e : InternalPair S.1 => (y e.1 : ℝ)) (z S))

noncomputable def modelObjective {r : ℕ} (n : Fin r → ℕ) (z : CliqueIndex r → ℝ) : ℝ :=
  ∑ S, ((-1 : ℝ) ^ (S.1.card + 1) / (S.1.lcm n : ℕ)) * z S

theorem model_pair_correct {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (x : Fin r → ℤ) (q y : PairIndex r → ℤ)
    (hy : ∀ e, y e = 0 ∨ y e = 1)
    (hq : ∀ e, pairConstraint ((n e.1.1).gcd (n e.1.2))
      (x e.1.1 - x e.1.2) (q e) (y e)) (e : PairIndex r) :
    y e = 1 ↔ Compatible n x e.1.1 e.1.2 := by
  have hd : (0 : ℤ) < (n e.1.1).gcd (n e.1.2) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left (n e.1.2) (hn e.1.1)
  exact ((pair_constraint_exact _ _ _ hd (hy e)).mp ⟨q e, hq e⟩).trans
    (compatible_iff_dvd n x e.1.1 e.1.2).symm

theorem internal_edges_iff_clique {r : ℕ} (s : Finset (Fin r))
    (n : Fin r → ℕ) (x : Fin r → ℤ) (y : PairIndex r → ℤ)
    (hy : ∀ e, y e = 1 ↔ Compatible n x e.1.1 e.1.2) :
    (∀ e : InternalPair s, (y e.1 : ℝ) = 1) ↔ IsClique n x s := by
  rw [clique_iff_internal_pairs]
  constructor
  · intro h e
    apply (hy e.1).mp
    exact_mod_cast h e
  · intro h e
    exact_mod_cast (hy e.1).mpr (h e)

end Erdos278
