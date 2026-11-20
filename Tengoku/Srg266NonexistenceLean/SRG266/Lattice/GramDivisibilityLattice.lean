/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.GramDivisibility
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue
import Tengoku.Seed.Algebra.Module.Torsion.Free

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

/--
@isnad1 id=mem.6h9v.s11.7b70f58e88fb from=translated src=- shape=f75e81bc vocab=fc0e37a7
-/
theorem mem_of_gramDivisibilityDescent
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℚ E]
    (F : LinearMap.BilinForm ℚ E) (L : Submodule ℤ E)
    (φ : (ι → ℤ) →ₗ[ℤ] E) (hmem : ∀ z, φ z ∈ L)
    (A : Matrix ι ι ℤ)
    (hpair : ∀ z w, F (φ z) (φ w) = (Matrix.toBilin' A z w : ℚ))
    {p : ℤ} (hp : p ≠ 0) (hd : GramDivisibilityDescent p A)
    (q : E) (z : ι → ℤ) (hz : φ z = (p : ℚ) • q)
    (hq : ∀ i, ∃ k : ℤ, F (φ (Pi.single i 1)) q = (k : ℚ)) :
    q ∈ L := by
  have hdiv (i : ι) : p ∣ (A *ᵥ z) i := by
    obtain ⟨k, hk⟩ := hq i
    have hi := hpair (Pi.single i 1) z
    have hrow : Matrix.toBilin' A (Pi.single i 1) z = (A *ᵥ z) i := by
      simp [Matrix.toBilin'_apply', dotProduct, Pi.single_apply, ite_mul]
    rw [hrow, hz, map_smul, smul_eq_mul, hk] at hi
    refine ⟨k, ?_⟩
    exact_mod_cast hi.symm
  choose w hw using hd z hdiv
  have hzw : z = p • w := by
    funext i
    exact hw i
  have hφ : (p : ℚ) • φ w = (p : ℚ) • q := by
    calc
      _ = φ (p • w) := by simp only [Int.cast_smul_eq_zsmul, map_zsmul]
      _ = φ z := congrArg φ hzw.symm
      _ = _ := hz
  have heq : φ w = q :=
    smul_right_injective E (by exact_mod_cast hp : (p : ℚ) ≠ 0) hφ
  exact heq ▸ hmem w

end SRG266.Lattice
