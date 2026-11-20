/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimaryNormalForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}
variable {N : Submodule ℤ W} {M : Submodule ℤ U}

theorem torsionPart_eq_sup_map_of_dual_transport (J : W →ₗ[ℤ] U)
    (hiM : IsIntegral C M)
    (hdual : C.dualSubmodule M = M ⊔ (B.dualSubmodule N).map J)
    (hclass : ∀ v ∈ B.dualSubmodule N, J v ∈ M ↔ v ∈ N) (p : ℕ) :
    torsionPart C M p = M ⊔ (torsionPart B N p).map J := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hzd, hzp⟩ := mem_torsionPart.mp hz
    rw [hdual] at hzd
    obtain ⟨m, hm, jv, hjv, rfl⟩ := Submodule.mem_sup.mp hzd
    obtain ⟨v, hv, rfl⟩ := hjv
    have hjp : (p : ℤ) • J v ∈ M := by
      have heq : (p : ℤ) • J v = (p : ℤ) • (m + J v) - (p : ℤ) • m := by module
      rw [heq]
      exact M.sub_mem hzp (M.smul_mem _ hm)
    have hvp : (p : ℤ) • v ∈ N := by
      apply (hclass _ ((B.dualSubmodule N).smul_mem (p : ℤ) hv)).mp
      simpa only [map_smul] using hjp
    exact Submodule.add_mem_sup hm ⟨v, mem_torsionPart.mpr ⟨hv, hvp⟩, rfl⟩
  · refine sup_le (le_torsionPart hiM p) ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvd, hvp⟩ := mem_torsionPart.mp hv
    refine mem_torsionPart.mpr ⟨?_, ?_⟩
    · rw [hdual]
      exact Submodule.mem_sup_right ⟨v, hvd, rfl⟩
    · have h := (hclass _ ((B.dualSubmodule N).smul_mem (p : ℤ) hvd)).mpr hvp
      simpa only [map_smul] using h

omit [Module ℚ W] [Module ℚ U] in

theorem sup_map_eq_sup_span_image (J : W →ₗ[ℤ] U) (hmap : N.map J ≤ M)
    {P : Submodule ℤ W} {s : Set W} (hP : P = N ⊔ Submodule.span ℤ s) :
    M ⊔ P.map J = M ⊔ Submodule.span ℤ (J '' s) := by
  rw [hP, Submodule.map_sup, Submodule.map_span, ← sup_assoc, sup_eq_left.mpr hmap]

theorem HasPrimaryNormalForm.map (J : W →ₗ[ℤ] U) (hmap : N.map J ≤ M)
    {p : ℕ} {r : ℤ}
    (hprimary : torsionPart C M p = M ⊔ (torsionPart B N p).map J)
    (hnorm : ∀ u ∈ torsionPart B N p,
      ∃ n : ℤ, C (J u) (J u) = B u u + 2 * (n : ℚ))
    (hcross : ∀ u ∈ torsionPart B N p, ∀ v ∈ torsionPart B N p,
      B u v ∈ (1 : Submodule ℤ ℚ) → C (J u) (J v) ∈ (1 : Submodule ℤ ℚ))
    (h : HasPrimaryNormalForm B N p r) : HasPrimaryNormalForm C M p r := by
  rcases h with hzero | ⟨u, a, k, ha, hsp, hu⟩ | ⟨u, v, hsp, huv, ⟨k, hu⟩, ⟨l, hv⟩⟩
  · apply Or.inl
    rw [hprimary, hzero, sup_eq_left.mpr hmap]
  · have hut : u ∈ torsionPart B N p := by
      rw [hsp]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    obtain ⟨n, hn⟩ := hnorm u hut
    refine Or.inr (Or.inl ⟨J u, a, k + n, ha, ?_, ?_⟩)
    · rw [hprimary, sup_map_eq_sup_span_image J hmap hsp, Set.image_singleton]
    · rw [hn, hu]
      push_cast
      ring
  · have hut : u ∈ torsionPart B N p := by
      rw [hsp]
      exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    have hvt : v ∈ torsionPart B N p := by
      rw [hsp]
      exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    obtain ⟨n, hn⟩ := hnorm u hut
    obtain ⟨m, hm⟩ := hnorm v hvt
    refine Or.inr (Or.inr ⟨J u, J v, ?_, hcross u hut v hvt huv,
      ⟨k + n, ?_⟩, ⟨l + m, ?_⟩⟩)
    · rw [hprimary, sup_map_eq_sup_span_image J hmap hsp, Set.image_pair]
    · rw [hn, hu]
      push_cast
      ring
    · rw [hm, hv]
      push_cast
      ring

end SRG266.Lattice
