/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.E6Coordinates

abbrev Space := (Fin 5 → ℚ) × (Fin 1 → ℚ)

def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 5) (simplexRatForm 1)

def glueVector : Space := ((3 : ℤ) • simplexWeight 5, simplexWeight 1)

def lattice : Submodule ℤ Space :=
  cyclicGlueLattice (coordinateIntegerLattice 5) (coordinateIntegerLattice 1)
    ((3 : ℤ) • simplexWeight 5) (simplexWeight 1)

def dualVector : Space := ((2 : ℤ) • simplexWeight 5, 0)

/--
@isnad1 id=issymm.0h0v.s7.526e9ae258c0 from=translated src=- shape=54c8eceb vocab=2aca453f
-/
theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)

/--
@isnad1 id=lt.1h1v.s10.e0cf8c5be19a from=translated src=- shape=e7c936f8 vocab=f33c54a7
-/
theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 5) (simplexRatForm_posDef 1)

/--
@isnad1 id=eq.0h0v.s10.8f2b86e980b6 from=translated src=- shape=bd6f62e4 vocab=96b27e61
-/
theorem glueVector_norm : form glueVector glueVector = 8 := by
  norm_num [form, glueVector, prodForm_apply, simplexRatForm_apply, simplexWeight,
    Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.d1537e7e3c5e from=translated src=- shape=1a9fa12e vocab=7736097e
-/
theorem dualVector_norm : form dualVector dualVector = 10 / 3 := by
  norm_num [form, dualVector, prodForm_apply, simplexRatForm_apply, simplexWeight,
    Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.428c9cb367d3 from=translated src=- shape=0775d00c vocab=ea737be2
-/
theorem dualVector_pair_glueVector : form dualVector glueVector = 5 := by
  norm_num [form, dualVector, glueVector, prodForm_apply, simplexRatForm_apply,
    simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=islattic.0h0v.s8.7366637af89a from=translated src=- shape=93eefbde vocab=f826e88d
-/
theorem lattice_isLattice : IsLattice ℚ lattice :=
  cyclicGlueLattice_isLattice (coordinateIntegerLattice_isLattice 5)
    (coordinateIntegerLattice_isLattice 1)

/--
@isnad1 id=isintegr.0h0v.s7.1640fe14972f from=translated src=- shape=8175f13d vocab=57a54a47
-/
theorem lattice_isIntegral : IsIntegral form lattice := by
  apply cyclicGlueLattice_isIntegral (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)
    (simplexRatForm_isIntegral 5) (simplexRatForm_isIntegral 1)
    (Submodule.smul_mem _ (3 : ℤ) (simplexWeight_mem_dual 5)) (simplexWeight_mem_dual 1)
  exact mem_one_iff.mpr ⟨8, glueVector_norm.symm⟩

/--
@isnad1 id=iseven.0h0v.s7.cf767af1d798 from=translated src=- shape=54c8eceb vocab=fc30017e
-/
theorem lattice_isEven : IsEven form lattice := by
  apply cyclicGlueLattice_isEven (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)
    lattice_isIntegral (simplexRatForm_isEven 5) (simplexRatForm_isEven 1)
  exact ⟨4, glueVector_norm.trans (by norm_num)⟩

/--
@isnad1 id=eq.0h0v.s7.e0cb10c77e35 from=translated src=- shape=b3c4969c vocab=f1022ba0
-/
theorem finrank_space : Module.finrank ℚ Space = 6 := by
  rw [Module.finrank_prod]
  simp

/--
@isnad1 id=mem.0h0v.s8.9cf80255fcb7 from=translated src=- shape=9e1a6a83 vocab=c596e403
-/
theorem twice_glue_left_mem :
    (2 : ℤ) • ((3 : ℤ) • simplexWeight 5) ∈ coordinateIntegerLattice 5 := by
  convert succ_smul_simplexWeight_mem 5 using 1
  module

/--
@isnad1 id=iff.0h1v.s9.7d64af93f2eb from=translated src=- shape=a64ef624 vocab=37927010
-/
theorem mem_left_iff (x : Fin 5 → ℚ) :
    (x, (0 : Fin 1 → ℚ)) ∈ lattice ↔ x ∈ coordinateIntegerLattice 5 :=
  cyclicGlueLattice_mem_left_iff twice_glue_left_mem
    (fun m => by simpa using simplexWeight_zsmul_mem_iff (0 : Fin 1) m) x

/--
@isnad1 id=iff.0h1v.s9.75e9e65c0122 from=translated src=- shape=d7064de8 vocab=37927010
-/
theorem mem_right_iff (y : Fin 1 → ℚ) :
    ((0 : Fin 5 → ℚ), y) ∈ lattice ↔ y ∈ coordinateIntegerLattice 1 := by
  apply cyclicGlueLattice_mem_right_iff (p := 2) ?_
    (by simpa using succ_smul_simplexWeight_mem 1)
  intro m
  have heq : m • ((3 : ℤ) • simplexWeight 5) = (3 * m) • simplexWeight 5 := by module
  rw [heq, simplexWeight_zsmul_mem_iff (0 : Fin 5)]
  norm_num
  omega

/--
@isnad1 id=mem.0h0v.s9.0734d7d50749 from=translated src=- shape=568e8a8c vocab=ef1ddfa4
-/
theorem dualVector_mem_dual : dualVector ∈ form.dualSubmodule lattice := by
  change lattice ≤ rightIntegral form dualVector
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · have h := (simplexRatForm 5).dualSubmodule (coordinateIntegerLattice 5) |>.smul_mem
      (2 : ℤ) (simplexWeight_mem_dual 5)
    change simplexRatForm 5 ((2 : ℤ) • simplexWeight 5) z.1 +
      simplexRatForm 1 0 z.2 ∈ (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using h z.1 hz.1
  · rintro _ (rfl : _ = glueVector)
    exact mem_one_iff.mpr ⟨5, dualVector_pair_glueVector.symm⟩

/--
@isnad1 id=iff.0h1v.s8.44807565ba5d from=translated src=- shape=0f1bbc81 vocab=728ca767
-/
theorem dualVector_order (m : ℤ) : m • dualVector ∈ lattice ↔ 3 ∣ m := by
  change (m • ((2 : ℤ) • simplexWeight 5), m • (0 : Fin 1 → ℚ)) ∈ lattice ↔ _
  rw [smul_zero, mem_left_iff]
  have heq : m • ((2 : ℤ) • simplexWeight 5) = (2 * m) • simplexWeight 5 := by module
  rw [heq, simplexWeight_zsmul_mem_iff (0 : Fin 5)]
  norm_num
  omega

/--
@isnad1 id=eq.0h0v.s10.1a01148bebaf from=translated src=- shape=f0794321 vocab=d0ab3fad
-/
theorem lattice_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {dualVector} := by
  apply le_antisymm
  · intro z hz
    have hp : z ∈ (prodForm (simplexRatForm 5) (simplexRatForm 1)).dualSubmodule
        ((coordinateIntegerLattice 5).prod (coordinateIntegerLattice 1)) :=
      fun w hw => hz w (Submodule.mem_sup_left hw)
    rw [dualSubmodule_prodForm] at hp
    obtain ⟨hx, hy⟩ := hp
    rw [simplexRatForm_dual] at hx hy
    obtain ⟨nx, hnx, ax, hax, heqx⟩ := Submodule.mem_sup.mp hx
    obtain ⟨ny, hny, by', hby, heqy⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hax
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hby
    have hn : (nx, ny) ∈ lattice := Submodule.mem_sup_left ⟨hnx, hny⟩
    have hg : glueVector ∈ lattice :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hng := lattice_isIntegral hn glueVector hg
    have hzg := hz glueVector hg
    have hleft : simplexRatForm 5 (simplexWeight 5) ((3 : ℤ) • simplexWeight 5) = 5 / 2 := by
      norm_num [simplexWeight_pair, simplexWeight, Fin.sum_univ_succ]
    have hright : simplexRatForm 1 (simplexWeight 1) (simplexWeight 1) = 1 / 2 := by
      rw [simplexWeight_norm]
      norm_num
    have he : form z glueVector = form (nx, ny) glueVector +
        (a : ℚ) * (5 / 2) + (b : ℚ) * (1 / 2) := by
      change simplexRatForm 5 z.1 ((3 : ℤ) • simplexWeight 5) +
        simplexRatForm 1 z.2 (simplexWeight 1) = _
      rw [← heqx, ← heqy]
      have ha : a • simplexWeight 5 = (a : ℚ) • simplexWeight 5 := by module
      have hb : b • simplexWeight 1 = (b : ℚ) • simplexWeight 1 := by module
      rw [ha, hb]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hleft, hright, form, prodForm_apply, glueVector]
      ring
    obtain ⟨r, hr⟩ := mem_one_iff.mp hng
    obtain ⟨t, ht⟩ := mem_one_iff.mp hzg
    have hQ : (5 : ℚ) * a + b = 2 * ((t : ℚ) - r) := by
      rw [he, ← hr] at ht
      linarith
    have hZ : 5 * a + b = 2 * (t - r) := by exact_mod_cast hQ
    have hdiv : (2 : ℤ) ∣ a - 3 * b := by omega
    obtain ⟨k, hk⟩ := hdiv
    have hdecomp : z = ((nx, ny) + b • glueVector) + k • dualVector := by
      apply Prod.ext
      · change z.1 = (nx + b • ((3 : ℤ) • simplexWeight 5)) +
          k • ((2 : ℤ) • simplexWeight 5)
        rw [← heqx]
        have ha : a = 3 * b + 2 * k := by omega
        rw [ha]
        module
      · change z.2 = (ny + b • simplexWeight 1) + k • (0 : Fin 1 → ℚ)
        simpa only [smul_zero, add_zero] using heqy.symm
    rw [hdecomp]
    exact Submodule.add_mem_sup (Submodule.add_mem _ hn (Submodule.smul_mem _ b hg))
      (Submodule.smul_mem _ k (Submodule.mem_span_singleton_self _))
  · refine sup_le lattice_isIntegral (Submodule.span_le.mpr ?_)
    rintro _ (rfl : _ = dualVector)
    exact dualVector_mem_dual

/--
@isnad1 id=mem.0h0v.s8.78a5d08a7225 from=translated src=- shape=cddf0ccc vocab=616d72e3
-/
theorem three_smul_dualVector_mem : (3 : ℤ) • dualVector ∈ lattice :=
  (dualVector_order 3).mpr (dvd_refl 3)

end SRG266.Lattice.E6Coordinates
