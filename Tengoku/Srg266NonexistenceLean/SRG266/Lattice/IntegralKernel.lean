/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BilinearLattice
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

def kernelNumerator (h : W →ₗ[ℚ] ℚ) (e : W) : W →ₗ[ℚ] h.ker where
  toFun z := ⟨h e • z - h z • e, by
    rw [LinearMap.mem_ker, map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring⟩
  map_add' z w := by
    apply Subtype.ext
    change h e • (z + w) - h (z + w) • e =
      (h e • z - h z • e) + (h e • w - h w • e)
    rw [map_add]
    module
  map_smul' a z := by
    apply Subtype.ext
    change h e • (a • z) - h (a • z) • e = a • (h e • z - h z • e)
    rw [map_smul]
    simp only [smul_eq_mul]
    module

/--
@isnad1 id=surjecti.1h3v.s8.dc23b39a809e from=translated src=- shape=6c0625bf vocab=4c4b3d2f
-/
theorem kernelNumerator_surjective (h : W →ₗ[ℚ] ℚ) (e : W) (he : h e ≠ 0) :
    Function.Surjective (kernelNumerator h e) := by
  intro y
  refine ⟨(h e)⁻¹ • (y : W), ?_⟩
  apply Subtype.ext
  change h e • ((h e)⁻¹ • (y : W)) - h ((h e)⁻¹ • (y : W)) • e = y
  have hy : h (y : W) = 0 := y.2
  rw [map_smul, hy, smul_zero, zero_smul, sub_zero, smul_smul, mul_inv_cancel₀ he,
    one_smul]

/--
@isnad1 id=islattic.4h4v.s9.6651e678c6ad from=translated src=- shape=13ddb2af vocab=62818f08
-/
theorem isLattice_comap_kernel (h : W →ₗ[ℚ] ℚ) {P : Submodule ℤ W}
    (hP : IsLattice ℚ P) (hint : ∀ z ∈ P, h z ∈ (1 : Submodule ℤ ℚ))
    {e : W} (heP : e ∈ P) (he : h e ≠ 0) :
    IsLattice ℚ (P.comap (h.ker.subtype.restrictScalars ℤ)) := by
  refine ⟨?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective (h.ker.subtype.restrictScalars ℤ)
      Subtype.val_injective
    exact hP.fg.of_le (Submodule.map_comap_le _ _)
  · have hmap : (kernelNumerator h e) '' (P : Set W) ⊆
        (P.comap (h.ker.subtype.restrictScalars ℤ) : Set h.ker) := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hint e heP)
      obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hint z hz)
      have ha' : (a : ℚ) = h e := by simpa using ha
      have hb' : (b : ℚ) = h z := by simpa using hb
      change h e • z - h z • e ∈ P
      rw [← ha', ← hb', Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      exact P.sub_mem (P.smul_mem a hz) (P.smul_mem b heP)
    have hspan : Submodule.span ℚ ((kernelNumerator h e) '' (P : Set W)) = ⊤ := by
      rw [← Submodule.map_span, hP.spans, Submodule.map_top,
        LinearMap.range_eq_top.mpr (kernelNumerator_surjective h e he)]
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono hmap

end SRG266.Lattice
