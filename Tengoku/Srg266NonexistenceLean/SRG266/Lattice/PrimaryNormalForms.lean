/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BinaryPrimaryNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

def HasPrimaryNormalForm (B : LinearMap.BilinForm ℚ W) (N : Submodule ℤ W)
    (p : ℕ) (binaryNumerator : ℤ) : Prop :=
  torsionPart B N p = N ∨
  (∃ u : W, ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧
    torsionPart B N p = N ⊔ Submodule.span ℤ {u} ∧
    B u u = (r : ℚ) / (p : ℚ) + 2 * (k : ℚ)) ∨
  (∃ u v : W, torsionPart B N p = N ⊔ Submodule.span ℤ {u, v} ∧
    B u v ∈ (1 : Submodule ℤ ℚ) ∧
    (∃ k : ℤ, B u u = 2 / (p : ℚ) + 2 * (k : ℚ)) ∧
    (∃ k : ℤ, B v v = (binaryNumerator : ℚ) / (p : ℚ) + 2 * (k : ℚ)))

theorem GlueBasis.normalForm_three (S : GlueBasis B N 3)
    (hs : B.IsSymm) (hmax : IsMaximalIntegral B N) (he : IsEven B N) :
    HasPrimaryNormalForm B N 3 2 := by
  have hR : S.rank = 0 ∨ S.rank = 1 ∨ S.rank = 2 := by
    have := S.rank_le
    omega
  rcases hR with hR | hR | hR
  · apply Or.inl
    rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
    dsimp at hR
    subst rank
    simpa using hspan
  · apply Or.inr ∘ Or.inl
    rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
    dsimp at hR
    subst rank
    obtain ⟨m, hm, hmq⟩ := hdiag 0
    have heven : Even m := even_numerator_of_odd_multiple (by decide : Odd (3 : ℤ)) he
      (mem_torsionPart.mp (hmem 0)).2 hmq
    obtain ⟨r, k, hr, hk⟩ := norm_mod_two_three heven hm hmq
    exact ⟨vec 0, r, k, hr, by simpa only [range_fin_one_eq_singleton] using hspan, hk⟩
  · exact Or.inr (Or.inr (S.normalized_binary_three hR hs hmax he))

theorem GlueBasis.normalForm_five (S : GlueBasis B N 5)
    (hs : B.IsSymm) (hmax : IsMaximalIntegral B N) (he : IsEven B N) :
    HasPrimaryNormalForm B N 5 4 := by
  have hR : S.rank = 0 ∨ S.rank = 1 ∨ S.rank = 2 := by
    have := S.rank_le
    omega
  rcases hR with hR | hR | hR
  · apply Or.inl
    rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
    dsimp at hR
    subst rank
    simpa using hspan
  · apply Or.inr ∘ Or.inl
    rcases S with ⟨rank, hle, vec, hmem, hspan, hortho, hdiag, hind⟩
    dsimp at hR
    subst rank
    obtain ⟨m, hm, hmq⟩ := hdiag 0
    have hp : (5 : ℤ) • vec 0 ∈ N := (mem_torsionPart.mp (hmem 0)).2
    have heven : Even m := even_numerator_of_odd_multiple (by decide : Odd (5 : ℤ)) he hp hmq
    obtain ⟨a, r, k, ha, hr, hk⟩ := normalized_norm_five heven hm hmq
    have hsp : N ⊔ Submodule.span ℤ {a • vec 0} = N ⊔ Submodule.span ℤ {vec 0} := by
      rcases ha with rfl | rfl
      · simp
      · exact sup_span_smul_eq_of_bezout (p := 5) (b := 3) (k := -1) hp (by norm_num)
    refine ⟨a • vec 0, r, k, hr, ?_, ?_⟩
    · rw [hsp]
      simpa only [range_fin_one_eq_singleton] using hspan
    · have heq : a • vec 0 = (a : ℚ) • vec 0 := by module
      rw [heq]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      nlinarith [hk]
  · exact Or.inr (Or.inr (S.normalized_binary_five hR hs hmax he))

end SRG266.Lattice
