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

theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)

theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 5) (simplexRatForm_posDef 1)

theorem glueVector_norm : form glueVector glueVector = 8 := by
  norm_num [form, glueVector, prodForm_apply, simplexRatForm_apply, simplexWeight,
    Fin.sum_univ_succ]

theorem dualVector_norm : form dualVector dualVector = 10 / 3 := by
  norm_num [form, dualVector, prodForm_apply, simplexRatForm_apply, simplexWeight,
    Fin.sum_univ_succ]

theorem dualVector_pair_glueVector : form dualVector glueVector = 5 := by
  norm_num [form, dualVector, glueVector, prodForm_apply, simplexRatForm_apply,
    simplexWeight, Fin.sum_univ_succ]

theorem lattice_isLattice : IsLattice ℚ lattice :=
  cyclicGlueLattice_isLattice (coordinateIntegerLattice_isLattice 5)
    (coordinateIntegerLattice_isLattice 1)

theorem lattice_isIntegral : IsIntegral form lattice := by
  apply cyclicGlueLattice_isIntegral (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)
    (simplexRatForm_isIntegral 5) (simplexRatForm_isIntegral 1)
    (Submodule.smul_mem _ (3 : ℤ) (simplexWeight_mem_dual 5)) (simplexWeight_mem_dual 1)
  exact mem_one_iff.mpr ⟨8, glueVector_norm.symm⟩

theorem lattice_isEven : IsEven form lattice := by
  apply cyclicGlueLattice_isEven (simplexRatForm_isSymm 5) (simplexRatForm_isSymm 1)
    lattice_isIntegral (simplexRatForm_isEven 5) (simplexRatForm_isEven 1)
  exact ⟨4, glueVector_norm.trans (by norm_num)⟩

theorem finrank_space : Module.finrank ℚ Space = 6 := by
  rw [Module.finrank_prod]
  simp

theorem twice_glue_left_mem :
    (2 : ℤ) • ((3 : ℤ) • simplexWeight 5) ∈ coordinateIntegerLattice 5 := by
  convert succ_smul_simplexWeight_mem 5 using 1
  module

theorem mem_left_iff (x : Fin 5 → ℚ) :
    (x, (0 : Fin 1 → ℚ)) ∈ lattice ↔ x ∈ coordinateIntegerLattice 5 :=
  cyclicGlueLattice_mem_left_iff twice_glue_left_mem
    (fun m => by simpa using simplexWeight_zsmul_mem_iff (0 : Fin 1) m) x

theorem mem_right_iff (y : Fin 1 → ℚ) :
    ((0 : Fin 5 → ℚ), y) ∈ lattice ↔ y ∈ coordinateIntegerLattice 1 := by
  apply cyclicGlueLattice_mem_right_iff (p := 2) ?_
    (by simpa using succ_smul_simplexWeight_mem 1)
  intro m
  have heq : m • ((3 : ℤ) • simplexWeight 5) = (3 * m) • simplexWeight 5 := by module
  rw [heq, simplexWeight_zsmul_mem_iff (0 : Fin 5)]
  norm_num
  omega

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

theorem dualVector_order (m : ℤ) : m • dualVector ∈ lattice ↔ 3 ∣ m := by
  change (m • ((2 : ℤ) • simplexWeight 5), m • (0 : Fin 1 → ℚ)) ∈ lattice ↔ _
  rw [smul_zero, mem_left_iff]
  have heq : m • ((2 : ℤ) • simplexWeight 5) = (2 * m) • simplexWeight 5 := by module
  rw [heq, simplexWeight_zsmul_mem_iff (0 : Fin 5)]
  norm_num
  omega

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

theorem three_smul_dualVector_mem : (3 : ℤ) • dualVector ∈ lattice :=
  (dualVector_order 3).mpr (dvd_refl 3)

end SRG266.Lattice.E6Coordinates
