/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6Coordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ScaledForm
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PrimarySpan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.H6Coordinates

abbrev Space := E6Coordinates.Space
def rightForm : LinearMap.BilinForm ℚ (Fin 1 → ℚ) := (10 : ℚ) • standardRatForm 1
def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 5) rightForm
def lattice : Submodule ℤ Space := E6Coordinates.lattice
def glueVector : Space := E6Coordinates.glueVector
def dualThree : Space := E6Coordinates.dualVector
def fifth : Fin 1 → ℚ := fun _ => 1 / 5
def dualFive : Space := (0, fifth)

private theorem standard_integral : IsIntegral (standardRatForm 1) (coordinateIntegerLattice 1) := by
  rw [IsIntegral, standardRatForm_dual_coordinateIntegerLattice]

/--
@isnad1 id=issymm.0h0v.s7.cde479eb4a40 from=translated src=- shape=54c8eceb vocab=658c6e07
-/
theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 5) (isSymm_smul_form (standardRatForm_isSymm 1) 10)

/--
@isnad1 id=lt.1h1v.s10.80abb4a264c5 from=translated src=- shape=e7c936f8 vocab=7547b03f
-/
theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 5)
    (posDef_smul_form (by norm_num) (standardRatForm_posDef 1))

/--
@isnad1 id=mem.0h0v.s8.7384abbd987a from=translated src=- shape=0a8cc1f1 vocab=15e3964a
-/
theorem half_mem_dual : simplexWeight 1 ∈ rightForm.dualSubmodule (coordinateIntegerLattice 1) := by
  rw [rightForm, mem_dual_smul_form_iff, standardRatForm_dual_coordinateIntegerLattice]
  refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 5, ?_⟩
  intro i
  norm_num [simplexWeight]

/--
@isnad1 id=eq.0h0v.s10.5680050e04f5 from=translated src=- shape=bd6f62e4 vocab=c21f4a36
-/
theorem glueVector_norm : form glueVector glueVector = 10 := by
  norm_num [form, rightForm, glueVector, E6Coordinates.glueVector, prodForm_apply,
    simplexRatForm_apply, standardRatForm_apply, simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.3c8a23d2039f from=translated src=- shape=1a9fa12e vocab=71cf364f
-/
theorem dualThree_norm : form dualThree dualThree = 10 / 3 := by
  norm_num [form, rightForm, dualThree, E6Coordinates.dualVector, prodForm_apply,
    simplexRatForm_apply, standardRatForm_apply, simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.4d849c92a832 from=translated src=- shape=1a9fa12e vocab=ab3264a2
-/
theorem dualFive_norm : form dualFive dualFive = 2 / 5 := by
  norm_num [form, rightForm, dualFive, fifth, prodForm_apply, simplexRatForm_apply,
    standardRatForm_apply, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.dd4c036384bb from=translated src=- shape=0775d00c vocab=62b147e1
-/
theorem dualThree_pair_glueVector : form dualThree glueVector = 5 := by
  norm_num [form, rightForm, dualThree, glueVector, E6Coordinates.dualVector,
    E6Coordinates.glueVector, prodForm_apply, simplexRatForm_apply,
    standardRatForm_apply, simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.57dd6afafc8f from=translated src=- shape=0775d00c vocab=99f98eca
-/
theorem dualFive_pair_glueVector : form dualFive glueVector = 1 := by
  norm_num [form, rightForm, dualFive, fifth, glueVector, E6Coordinates.glueVector,
    prodForm_apply, simplexRatForm_apply, standardRatForm_apply, simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.ff4e4f2264c8 from=translated src=- shape=0775d00c vocab=7c56a6c8
-/
theorem dualThree_pair_dualFive : form dualThree dualFive = 0 := by
  simp [form, dualThree, E6Coordinates.dualVector, dualFive, prodForm_apply]

/--
@isnad1 id=islattic.0h0v.s8.abc96217e889 from=translated src=- shape=93eefbde vocab=c4ba2fe7
-/
theorem lattice_isLattice : IsLattice ℚ lattice := E6Coordinates.lattice_isLattice

/--
@isnad1 id=isintegr.0h0v.s7.73e9db0e8221 from=translated src=- shape=8175f13d vocab=7f00ffe5
-/
theorem lattice_isIntegral : IsIntegral form lattice := by
  apply cyclicGlueLattice_isIntegral (simplexRatForm_isSymm 5)
    (isSymm_smul_form (standardRatForm_isSymm 1) 10)
    (simplexRatForm_isIntegral 5) (isIntegral_int_smul_form standard_integral 10)
    (Submodule.smul_mem _ (3 : ℤ) (simplexWeight_mem_dual 5)) half_mem_dual
  exact mem_one_iff.mpr ⟨10, glueVector_norm.symm⟩

/--
@isnad1 id=iseven.0h0v.s7.6e6f786e7410 from=translated src=- shape=54c8eceb vocab=da0d2ded
-/
theorem lattice_isEven : IsEven form lattice := by
  apply cyclicGlueLattice_isEven (simplexRatForm_isSymm 5)
    (isSymm_smul_form (standardRatForm_isSymm 1) 10) lattice_isIntegral
    (simplexRatForm_isEven 5) (isEven_even_smul_form standard_integral (by decide : Even (10 : ℤ)))
  exact ⟨5, glueVector_norm.trans (by norm_num)⟩

/--
@isnad1 id=eq.0h0v.s7.63608335fca2 from=translated src=- shape=b3c4969c vocab=833f0bbf
-/
theorem finrank_space : Module.finrank ℚ Space = 6 := E6Coordinates.finrank_space

/--
@isnad1 id=mem.0h0v.s9.a103d3bd842c from=translated src=- shape=568e8a8c vocab=b965b6c1
-/
theorem dualThree_mem_dual : dualThree ∈ form.dualSubmodule lattice := by
  change lattice ≤ rightIntegral form dualThree
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · have h := (simplexRatForm 5).dualSubmodule (coordinateIntegerLattice 5) |>.smul_mem
      (2 : ℤ) (simplexWeight_mem_dual 5)
    change simplexRatForm 5 ((2 : ℤ) • simplexWeight 5) z.1 + rightForm 0 z.2 ∈ (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using h z.1 hz.1
  · rintro _ (rfl : _ = glueVector)
    exact mem_one_iff.mpr ⟨5, dualThree_pair_glueVector.symm⟩

/--
@isnad1 id=mem.0h0v.s9.54a8fe40bbce from=translated src=- shape=568e8a8c vocab=97673725
-/
theorem dualFive_mem_dual : dualFive ∈ form.dualSubmodule lattice := by
  have hf : fifth ∈ rightForm.dualSubmodule (coordinateIntegerLattice 1) := by
    rw [rightForm, mem_dual_smul_form_iff, standardRatForm_dual_coordinateIntegerLattice]
    refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 2, ?_⟩
    intro i
    norm_num [fifth]
  change lattice ≤ rightIntegral form dualFive
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · change simplexRatForm 5 0 z.1 + rightForm fifth z.2 ∈ (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, zero_add] using hf z.2 hz.2
  · rintro _ (rfl : _ = glueVector)
    exact mem_one_iff.mpr ⟨1, dualFive_pair_glueVector.symm⟩

/--
@isnad1 id=mem.0h0v.s8.bb8a7e57d434 from=translated src=- shape=cddf0ccc vocab=5e369da0
-/
theorem three_smul_dualThree_mem : (3 : ℤ) • dualThree ∈ lattice :=
  E6Coordinates.three_smul_dualVector_mem

/--
@isnad1 id=mem.0h0v.s8.92d8b9161c49 from=translated src=- shape=cddf0ccc vocab=3129088e
-/
theorem five_smul_dualFive_mem : (5 : ℤ) • dualFive ∈ lattice := by
  apply Submodule.mem_sup_left
  constructor
  · simp [dualFive]
  · refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 1, ?_⟩
    intro i
    norm_num [dualFive, fifth]

/--
@isnad1 id=eq.0h0v.s10.4168dd158826 from=translated src=- shape=a049e693 vocab=4eee17ce
-/
theorem lattice_dual : form.dualSubmodule lattice =
    lattice ⊔ Submodule.span ℤ {dualThree, dualFive} := by
  apply le_antisymm
  · intro z hz
    have hp : z ∈ (prodForm (simplexRatForm 5) rightForm).dualSubmodule
        ((coordinateIntegerLattice 5).prod (coordinateIntegerLattice 1)) :=
      fun w hw => hz w (Submodule.mem_sup_left hw)
    rw [dualSubmodule_prodForm] at hp
    obtain ⟨hx, hy⟩ := hp
    rw [simplexRatForm_dual] at hx
    obtain ⟨nx, hnx, bw, hbw, heqx⟩ := Submodule.mem_sup.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hbw
    have hy' := (mem_dual_smul_form_iff (B := standardRatForm 1)
      (N := coordinateIntegerLattice 1) (10 : ℚ) z.2).mp hy
    rw [standardRatForm_dual_coordinateIntegerLattice] at hy'
    obtain ⟨d, hd⟩ := mem_coordinateIntegerLattice.mp hy'
    have hy0 : z.2 0 = (d 0 : ℚ) / 10 := by
      have h := hd 0
      change (d 0 : ℚ) = 10 * z.2 0 at h
      linarith
    have hn : (nx, (0 : Fin 1 → ℚ)) ∈ lattice :=
      Submodule.mem_sup_left ⟨hnx, (coordinateIntegerLattice 1).zero_mem⟩
    have hg : glueVector ∈ lattice := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hng := lattice_isIntegral hn glueVector hg
    have hzg := hz glueVector hg
    have hleft : simplexRatForm 5 (simplexWeight 5) ((3 : ℤ) • simplexWeight 5) = 5 / 2 := by
      norm_num [simplexWeight_pair, simplexWeight, Fin.sum_univ_succ]
    have he : form z glueVector = form (nx, 0) glueVector +
        (b : ℚ) * (5 / 2) + (d 0 : ℚ) / 2 := by
      change simplexRatForm 5 z.1 ((3 : ℤ) • simplexWeight 5) + rightForm z.2 (simplexWeight 1) = _
      rw [← heqx]
      have hb : b • simplexWeight 5 = (b : ℚ) • simplexWeight 5 := by module
      rw [hb]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hleft, form, prodForm_apply, glueVector, E6Coordinates.glueVector]
      norm_num [rightForm, standardRatForm_apply, simplexWeight, Fin.sum_univ_succ, hy0]
      ring
    obtain ⟨r, hr⟩ := mem_one_iff.mp hng
    obtain ⟨t, ht⟩ := mem_one_iff.mp hzg
    have hQ : (5 : ℚ) * b + d 0 = 2 * ((t : ℚ) - r) := by
      rw [he, ← hr] at ht
      linarith
    have hZ : 5 * b + d 0 = 2 * (t - r) := by exact_mod_cast hQ
    have hd' : (2 : ℤ) ∣ d 0 - 5 * b := by omega
    obtain ⟨l, hl⟩ := hd'
    have hdecomp : z = ((nx, (0 : Fin 1 → ℚ)) + b • glueVector) +
        ((-b) • dualThree + l • dualFive) := by
      apply Prod.ext
      · change z.1 = (nx + b • ((3 : ℤ) • simplexWeight 5)) +
          ((-b) • ((2 : ℤ) • simplexWeight 5) + l • (0 : Fin 5 → ℚ))
        rw [← heqx]
        module
      · ext i
        fin_cases i
        have h : (d 0 : ℚ) - 5 * (b : ℚ) = 2 * (l : ℚ) := by exact_mod_cast hl
        norm_num [glueVector, E6Coordinates.glueVector, dualThree, E6Coordinates.dualVector,
          dualFive, fifth, simplexWeight, hy0, zsmul_eq_mul]
        linarith
    rw [hdecomp]
    refine Submodule.add_mem_sup (lattice.add_mem hn (lattice.smul_mem b hg)) ?_
    exact Submodule.add_mem _
      (Submodule.smul_mem _ (-b) (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ l (Submodule.subset_span (by simp)))
  · refine sup_le lattice_isIntegral (Submodule.span_le.mpr ?_)
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
      z = dualThree ∨ z = dualFive) with rfl | rfl
    · exact dualThree_mem_dual
    · exact dualFive_mem_dual

end SRG266.Lattice.H6Coordinates
