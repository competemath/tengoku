import Tengoku.Erdos278.Erdos278.Density

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/yoshiyoyoyo44/erdos278@66ff46ad30c3, `Erdos278/Maximization.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace Erdos278


open Finset
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/--
@isnad1 id=ex.1h3v.s6.3d66fffda146 from=translated src=- shape=5bb595ca vocab=ab4fa750
-/
theorem canonical_representatives (n : ι → ℕ) (hn : ∀ i, 0 < n i) (a : ι → ℤ) :
    ∃ b : (i : ι) → Fin (n i), ∀ i, (b i : ℤ) = a i % n i := by
  let b : (i : ι) → Fin (n i) := fun i => ⟨(a i % n i).toNat, by
    have hnonneg : 0 ≤ a i % (n i : ℤ) :=
      Int.emod_nonneg (a i) (by exact_mod_cast (hn i).ne')
    have hcast : ((a i % n i).toNat : ℤ) = a i % n i := Int.toNat_of_nonneg hnonneg
    have hlt : ((a i % n i).toNat : ℤ) < n i := by
      rw [hcast]
      exact Int.emod_lt_of_pos _ (by exact_mod_cast hn i)
    exact_mod_cast hlt⟩
  refine ⟨b, fun i => ?_⟩
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (hn i).ne'))

/-- An optimal residue tuple exists. This is an existence theorem over all
integer representatives, proved by reduction to a finite search space.
@isnad1 id=ex.1h2v.s5.a024bd315e38 from=translated src=- shape=5810639e vocab=59f58e10
-/
theorem maximum_attained (n : ι → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ a : ι → ℤ, ∀ b : ι → ℤ, density univ n b ≤ density univ n a := by
  classical
  let f : ((i : ι) → Fin (n i)) → ℚ := fun b => density univ n (fun i => (b i : ℤ))
  have hnonempty : (univ : Finset ((i : ι) → Fin (n i))).Nonempty :=
    ⟨fun i => ⟨0, hn i⟩, mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image univ f hnonempty
  refine ⟨fun i => (a i : ℤ), fun b => ?_⟩
  obtain ⟨c, hc⟩ := canonical_representatives n hn b
  have heq : density univ n (fun i => (c i : ℤ)) = density univ n b := by
    apply density_eq_of_compatible univ n (fun i _ => hn i)
    intro i j
    simp_rw [hc]
    exact reduce_preserves_compatibility n b i j
  rw [← heq]
  exact ha c (mem_univ _)

/-- Translation symmetry and minimal interaction compression can be imposed
simultaneously, including x i₀ = 0 and all bounds 0 ≤ x i < M i.
@isnad1 id=ex.1h4v.s6.75913e91bf5f from=translated src=- shape=d7c354ff vocab=dbb3387f
-/
theorem normalized_compressed_witness (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (a : ι → ℤ) (i₀ : ι) :
    ∃ x : ι → ℤ, x i₀ = 0 ∧
      (∀ i, 0 ≤ x i ∧ x i < interactionModulus n i) ∧
      (∀ i j, Compatible n x i j ↔ Compatible n a i j) := by
  let x : ι → ℤ := fun i => (a i - a i₀) % interactionModulus n i
  refine ⟨x, by simp [x], ?_, ?_⟩
  · intro i
    have hp : (0 : ℤ) < interactionModulus n i := by exact_mod_cast interaction_pos n hn i
    exact ⟨Int.emod_nonneg _ hp.ne', Int.emod_lt_of_pos _ hp⟩
  · intro i j
    exact (interaction_compression n x (fun i => a i - a i₀)
      (fun i => Int.mod_modEq _ _) i j).trans
        (translate_preserves_compatibility n a (a i₀) i j)

end Erdos278
