import Tengoku.Erdos278.Erdos278.Maximization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/CommonGCD.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace Erdos278


open Finset
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- In the common pairwise-gcd case, no information beyond the assignment
to g fibers can affect the union density.-/
theorem common_gcd_density_depends_on_partition (n : ι → ℕ)
    (hn : ∀ i, 0 < n i) (g : ℕ)
    (hg : ∀ i j, i ≠ j → (n i).gcd (n j) = g)
    (a b : ι → ℤ) (hp : ∀ i, a i ≡ b i [ZMOD g]) :
    density univ n a = density univ n b := by
  apply density_eq_of_compatible univ n (fun i _ => hn i)
  intro i j
  by_cases hij : i = j
  · subst j; simp [Compatible]
  · unfold Compatible
    rw [hg i j hij]
    exact ⟨fun h => (hp i).symm.trans (h.trans (hp j)),
      fun h => (hp i).trans (h.trans (hp j).symm)⟩

/-- Every partition into g labeled parts occurs, and the entire set of
attainable densities equals the set obtained from those assignments.-/
theorem common_gcd_partition_optimization (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (g : ℕ) (hg0 : 0 < g) (hg : ∀ i j, i ≠ j → (n i).gcd (n j) = g) (d : ℚ) :
    (∃ a : ι → ℤ, density univ n a = d) ↔
      ∃ part : ι → Fin g, density univ n (fun i => (part i : ℤ)) = d := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨part, hp⟩ := canonical_representatives (fun _ : ι => g) (fun _ => hg0) a
    refine ⟨part, common_gcd_density_depends_on_partition n hn g hg _ a ?_⟩
    intro i
    rw [hp i]
    exact Int.mod_modEq _ _
  · rintro ⟨part, hp⟩
    exact ⟨fun i => (part i : ℤ), hp⟩

/-- Dividing out a common pairwise gcd really leaves pairwise coprime factors.
It does not require g to be coprime to any of those factors.-/
theorem common_gcd_factors_coprime (g : ℕ) (hg : 0 < g) (b : ι → ℕ)
    (h : ∀ i j, i ≠ j → (g * b i).gcd (g * b j) = g) :
    ∀ i j, i ≠ j → (b i).Coprime (b j) := by
  intro i j hij
  have heq := h i j hij
  rw [Nat.gcd_mul_left] at heq
  apply Nat.coprime_iff_gcd_eq_one.mpr
  nlinarith

/-- Coprimality of g and each factor is genuinely unnecessary, as g=2,
factors 2 and 3 demonstrate.-/
theorem common_gcd_need_not_be_coprime_to_factors :
    Nat.gcd 4 6 = 2 ∧ Nat.Coprime 2 3 ∧ ¬Nat.Coprime 2 2 := by decide

end Erdos278
