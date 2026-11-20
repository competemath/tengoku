/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ScaledForm
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicSelfDual
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OddPrimaryNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.K8Coordinates

abbrev Space := (Fin 7 → ℚ) × (Fin 1 → ℚ)

def rightForm : LinearMap.BilinForm ℚ (Fin 1 → ℚ) := (10 : ℚ) • standardRatForm 1
def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 7) rightForm
def half : Fin 1 → ℚ := fun _ => 1 / 2
def fifth : Fin 1 → ℚ := fun _ => 1 / 5
def glueVector : Space := ((2 : ℤ) • simplexWeight 7, half)
def dualVector : Space := (0, fifth)
def lattice : Submodule ℤ Space :=
  cyclicGlueLattice (coordinateIntegerLattice 7) (coordinateIntegerLattice 1)
    ((2 : ℤ) • simplexWeight 7) half

private theorem standard_integral : IsIntegral (standardRatForm 1) (coordinateIntegerLattice 1) := by
  rw [IsIntegral, standardRatForm_dual_coordinateIntegerLattice]

/--
@isnad1 id=issymm.0h0v.s7.b8126882fe04 from=translated src=- shape=54c8eceb vocab=1873e7ef
-/
theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 7) (isSymm_smul_form (standardRatForm_isSymm 1) 10)

/--
@isnad1 id=lt.1h1v.s10.b4bcd929f2e9 from=translated src=- shape=e7c936f8 vocab=571d4eef
-/
theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 7)
    (posDef_smul_form (by norm_num) (standardRatForm_posDef 1))

/--
@isnad1 id=mem.0h0v.s8.c1486d4e15df from=translated src=- shape=355401fc vocab=95986c43
-/
theorem half_mem_dual : half ∈ rightForm.dualSubmodule (coordinateIntegerLattice 1) := by
  rw [rightForm, mem_dual_smul_form_iff, standardRatForm_dual_coordinateIntegerLattice]
  refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 5, ?_⟩
  intro i
  norm_num [half]

/--
@isnad1 id=eq.0h0v.s10.be9095bbc255 from=translated src=- shape=bd6f62e4 vocab=faba2ca7
-/
theorem glueVector_norm : form glueVector glueVector = 6 := by
  norm_num [form, rightForm, glueVector, half, prodForm_apply, simplexRatForm_apply,
    standardRatForm_apply, simplexWeight, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.08909597eba8 from=translated src=- shape=1a9fa12e vocab=c34ca903
-/
theorem dualVector_norm : form dualVector dualVector = 2 / 5 := by
  norm_num [form, rightForm, dualVector, fifth, prodForm_apply, simplexRatForm_apply,
    standardRatForm_apply, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h0v.s10.0afcfd623761 from=translated src=- shape=0775d00c vocab=35360d63
-/
theorem dualVector_pair_glueVector : form dualVector glueVector = 1 := by
  norm_num [form, rightForm, dualVector, glueVector, half, fifth, prodForm_apply,
    simplexRatForm_apply, standardRatForm_apply, Fin.sum_univ_succ]

/--
@isnad1 id=islattic.0h0v.s8.71d81e2316cc from=translated src=- shape=93eefbde vocab=b652f5fd
-/
theorem lattice_isLattice : IsLattice ℚ lattice :=
  cyclicGlueLattice_isLattice (coordinateIntegerLattice_isLattice 7)
    (coordinateIntegerLattice_isLattice 1)

/--
@isnad1 id=isintegr.0h0v.s7.2c8f1b6da3e8 from=translated src=- shape=8175f13d vocab=1e7a3485
-/
theorem lattice_isIntegral : IsIntegral form lattice := by
  apply cyclicGlueLattice_isIntegral (simplexRatForm_isSymm 7)
    (isSymm_smul_form (standardRatForm_isSymm 1) 10)
    (simplexRatForm_isIntegral 7) (isIntegral_int_smul_form standard_integral 10)
    (Submodule.smul_mem _ (2 : ℤ) (simplexWeight_mem_dual 7)) half_mem_dual
  exact mem_one_iff.mpr ⟨6, glueVector_norm.symm⟩

/--
@isnad1 id=iseven.0h0v.s7.ae19f3342d31 from=translated src=- shape=54c8eceb vocab=7dcefb73
-/
theorem lattice_isEven : IsEven form lattice := by
  apply cyclicGlueLattice_isEven (simplexRatForm_isSymm 7)
    (isSymm_smul_form (standardRatForm_isSymm 1) 10) lattice_isIntegral
    (simplexRatForm_isEven 7) (isEven_even_smul_form standard_integral (by decide : Even (10 : ℤ)))
  exact ⟨3, glueVector_norm.trans (by norm_num)⟩

/--
@isnad1 id=eq.0h0v.s7.d88fda3c0d53 from=translated src=- shape=b3c4969c vocab=b3a89a5a
-/
theorem finrank_space : Module.finrank ℚ Space = 8 := by
  rw [Module.finrank_prod]
  simp

/--
@isnad1 id=mem.0h0v.s9.c23e2eca84f7 from=translated src=- shape=568e8a8c vocab=72c735f6
-/
theorem dualVector_mem_dual : dualVector ∈ form.dualSubmodule lattice := by
  have hf : fifth ∈ rightForm.dualSubmodule (coordinateIntegerLattice 1) := by
    rw [rightForm, mem_dual_smul_form_iff, standardRatForm_dual_coordinateIntegerLattice]
    refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 2, ?_⟩
    intro i
    norm_num [fifth]
  change lattice ≤ rightIntegral form dualVector
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · change simplexRatForm 7 0 z.1 + rightForm fifth z.2 ∈ (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, zero_add] using hf z.2 hz.2
  · rintro _ (rfl : _ = glueVector)
    exact mem_one_iff.mpr ⟨1, dualVector_pair_glueVector.symm⟩

/--
@isnad1 id=mem.0h0v.s8.d543cb299744 from=translated src=- shape=cddf0ccc vocab=950e4cd3
-/
theorem five_smul_dualVector_mem : (5 : ℤ) • dualVector ∈ lattice := by
  apply Submodule.mem_sup_left
  constructor
  · simp [dualVector]
  · refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 1, ?_⟩
    intro i
    norm_num [dualVector, fifth]

/--
@isnad1 id=iff.0h1v.s8.0a4fe90db7d6 from=translated src=- shape=0f1bbc81 vocab=d741ff8a
-/
theorem dualVector_order (m : ℤ) : m • dualVector ∈ lattice ↔ 5 ∣ m := by
  constructor
  · intro hm
    apply norm_denominator_unit (p := 5) (r := 2) (k := 0) (by norm_num)
      ⟨1, -2, by norm_num⟩ (by simpa using dualVector_norm) m
    have h := dualVector_mem_dual _ hm
    have heq : m • dualVector = (m : ℚ) • dualVector := by module
    rwa [heq, map_smul, smul_eq_mul] at h
  · rintro ⟨k, rfl⟩
    have heq : (5 * k) • dualVector = k • ((5 : ℤ) • dualVector) := by module
    rw [heq]
    exact lattice.smul_mem k five_smul_dualVector_mem

/--
@isnad1 id=eq.0h0v.s10.8b6159abbeea from=translated src=- shape=f0794321 vocab=5cc0a98c
-/
theorem lattice_dual : form.dualSubmodule lattice = lattice ⊔ Submodule.span ℤ {dualVector} := by
  apply le_antisymm
  · intro z hz
    have hp : z ∈ (prodForm (simplexRatForm 7) rightForm).dualSubmodule
        ((coordinateIntegerLattice 7).prod (coordinateIntegerLattice 1)) :=
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
    have hg : glueVector ∈ lattice :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have hng := lattice_isIntegral hn glueVector hg
    have hzg := hz glueVector hg
    have hleft : simplexRatForm 7 (simplexWeight 7) ((2 : ℤ) • simplexWeight 7) = 7 / 4 := by
      norm_num [simplexWeight_pair, simplexWeight, Fin.sum_univ_succ]
    have he : form z glueVector = form (nx, 0) glueVector +
        (b : ℚ) * (7 / 4) + (d 0 : ℚ) / 2 := by
      change simplexRatForm 7 z.1 ((2 : ℤ) • simplexWeight 7) + rightForm z.2 half = _
      rw [← heqx]
      have hb : b • simplexWeight 7 = (b : ℚ) • simplexWeight 7 := by module
      rw [hb]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hleft, form, prodForm_apply, glueVector]
      norm_num [rightForm, standardRatForm_apply, half, Fin.sum_univ_succ, hy0]
      ring
    obtain ⟨r, hr⟩ := mem_one_iff.mp hng
    obtain ⟨t, ht⟩ := mem_one_iff.mp hzg
    have hQ : (7 : ℚ) * b + 2 * d 0 = 4 * ((t : ℚ) - r) := by
      rw [he, ← hr] at ht
      linarith
    have hZ : 7 * b + 2 * d 0 = 4 * (t - r) := by exact_mod_cast hQ
    have hb : (2 : ℤ) ∣ b := by omega
    obtain ⟨k, hk⟩ := hb
    have hd' : (2 : ℤ) ∣ d 0 - 5 * k := by omega
    obtain ⟨l, hl⟩ := hd'
    have hdecomp : z = ((nx, (0 : Fin 1 → ℚ)) + k • glueVector) + l • dualVector := by
      apply Prod.ext
      · change z.1 = (nx + k • ((2 : ℤ) • simplexWeight 7)) + l • (0 : Fin 7 → ℚ)
        rw [← heqx, hk]
        module
      · ext i
        fin_cases i
        change z.2 0 = (0 + k • (1 / 2 : ℚ)) + l • (1 / 5 : ℚ)
        simp only [zsmul_eq_mul, zero_add]
        rw [hy0]
        have h : (d 0 : ℚ) - 5 * (k : ℚ) = 2 * (l : ℚ) := by exact_mod_cast hl
        linarith
    rw [hdecomp]
    exact Submodule.add_mem_sup (lattice.add_mem hn (lattice.smul_mem k hg))
      (Submodule.smul_mem _ l (Submodule.mem_span_singleton_self _))
  · refine sup_le lattice_isIntegral (Submodule.span_le.mpr ?_)
    rintro _ (rfl : _ = dualVector)
    exact dualVector_mem_dual

end SRG266.Lattice.K8Coordinates
