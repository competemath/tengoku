/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ScaledForm
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicGlue
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.OddPrimaryNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice.K4Coordinates

open scoped BigOperators

abbrev Space := (Fin 2 → ℚ) × (Fin 2 → ℚ)
def rightForm : LinearMap.BilinForm ℚ (Fin 2 → ℚ) := (5 : ℚ) • simplexRatForm 2
def form : LinearMap.BilinForm ℚ Space := prodForm (simplexRatForm 2) rightForm
def glueVector : Space := (simplexWeight 2, simplexWeight 2)
def lattice : Submodule ℤ Space :=
  cyclicGlueLattice (coordinateIntegerLattice 2) (coordinateIntegerLattice 2)
    (simplexWeight 2) (simplexWeight 2)
def rightFraction (c : Fin 2 → ℤ) : Space := (0, (1 / 5 : ℚ) • intCoordsToRat c)
def dualA : Space := rightFraction (fun i => if i = 0 then 1 else 0)
def dualB : Space := rightFraction (fun i => if i = 0 then -2 else 4)

theorem form_isSymm : form.IsSymm :=
  prodForm_isSymm (simplexRatForm_isSymm 2) (isSymm_smul_form (simplexRatForm_isSymm 2) 5)

theorem form_posDef : ∀ x : Space, x ≠ 0 → 0 < form x x :=
  prodForm_posDef (simplexRatForm_posDef 2)
    (posDef_smul_form (by norm_num) (simplexRatForm_posDef 2))

theorem glueVector_norm : form glueVector glueVector = 4 := by
  norm_num [form, rightForm, glueVector, prodForm_apply, simplexRatForm_apply,
    simplexWeight, Fin.sum_univ_succ]

theorem lattice_isLattice : IsLattice ℚ lattice :=
  cyclicGlueLattice_isLattice (coordinateIntegerLattice_isLattice 2)
    (coordinateIntegerLattice_isLattice 2)

theorem lattice_isIntegral : IsIntegral form lattice := by
  have hr : simplexWeight 2 ∈ rightForm.dualSubmodule (coordinateIntegerLattice 2) := by
    apply (mem_dual_smul_form_iff (B := simplexRatForm 2) (5 : ℚ) _).mpr
    have heq : (5 : ℚ) • simplexWeight 2 = (5 : ℤ) • simplexWeight 2 := by module
    rw [heq]
    exact Submodule.smul_mem _ (5 : ℤ) (simplexWeight_mem_dual 2)
  apply cyclicGlueLattice_isIntegral (simplexRatForm_isSymm 2)
    (isSymm_smul_form (simplexRatForm_isSymm 2) 5)
    (simplexRatForm_isIntegral 2) (isIntegral_int_smul_form (simplexRatForm_isIntegral 2) 5)
    (simplexWeight_mem_dual 2) hr
  exact mem_one_iff.mpr ⟨4, glueVector_norm.symm⟩

theorem lattice_isEven : IsEven form lattice := by
  apply cyclicGlueLattice_isEven (simplexRatForm_isSymm 2)
    (isSymm_smul_form (simplexRatForm_isSymm 2) 5) lattice_isIntegral
    (simplexRatForm_isEven 2) (isEven_int_smul_form (simplexRatForm_isEven 2) 5)
  exact ⟨2, glueVector_norm.trans (by norm_num)⟩

theorem finrank_space : Module.finrank ℚ Space = 4 := by
  rw [Module.finrank_prod]
  simp

theorem rightFraction_pair (c : Fin 2 → ℤ) (z : Space) :
    form (rightFraction c) z = simplexRatForm 2 (intCoordsToRat c) z.2 := by
  simp only [form, rightFraction, prodForm_apply, rightForm, map_zero,
    LinearMap.zero_apply, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem rightFraction_mem_dual (c : Fin 2 → ℤ) :
    rightFraction c ∈ form.dualSubmodule lattice := by
  change lattice ≤ rightIntegral form (rightFraction c)
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · change form (rightFraction c) z ∈ (1 : Submodule ℤ ℚ)
    rw [rightFraction_pair]
    exact simplexRatForm_isIntegral 2 (intCoordsToRat_mem c) z.2 hz.2
  · rintro _ (rfl : _ = glueVector)
    change form (rightFraction c) glueVector ∈ (1 : Submodule ℤ ℚ)
    rw [rightFraction_pair]
    change simplexRatForm 2 (intCoordsToRat c) (simplexWeight 2) ∈ _
    rw [(simplexRatForm_isSymm 2).eq, simplexWeight_pair]
    exact mem_one_iff.mpr ⟨∑ i, c i, by simp⟩

theorem five_smul_rightFraction_mem (c : Fin 2 → ℤ) :
    (5 : ℤ) • rightFraction c ∈ lattice := by
  have heq : (5 : ℤ) • rightFraction c = (0, intCoordsToRat c) := by
    ext i <;> simp [rightFraction, zsmul_eq_mul]
  rw [heq]
  exact Submodule.mem_sup_left ⟨(coordinateIntegerLattice 2).zero_mem, intCoordsToRat_mem c⟩

theorem dualA_mem_dual : dualA ∈ form.dualSubmodule lattice :=
  rightFraction_mem_dual _
theorem dualB_mem_dual : dualB ∈ form.dualSubmodule lattice :=
  rightFraction_mem_dual _
theorem five_smul_dualA_mem : (5 : ℤ) • dualA ∈ lattice := five_smul_rightFraction_mem _
theorem five_smul_dualB_mem : (5 : ℤ) • dualB ∈ lattice := five_smul_rightFraction_mem _

theorem dualA_norm : form dualA dualA = 2 / 5 := by
  norm_num [form, rightForm, dualA, rightFraction, prodForm_apply, simplexRatForm_apply,
    intCoordsToRat_apply, Fin.sum_univ_succ]

theorem dualB_norm : form dualB dualB = 24 / 5 := by
  norm_num [form, rightForm, dualB, rightFraction, prodForm_apply, simplexRatForm_apply,
    intCoordsToRat_apply, Fin.sum_univ_succ]

theorem dualA_pair_dualB : form dualA dualB = 0 := by
  norm_num [form, rightForm, dualA, dualB, rightFraction, prodForm_apply, simplexRatForm_apply,
    intCoordsToRat_apply, Fin.sum_univ_succ]

theorem dual_independent (a b : ℤ) (h : a • dualA + b • dualB ∈ lattice) :
    (5 : ℤ) ∣ a ∧ (5 : ℤ) ∣ b := by
  have heq : a • dualA + b • dualB = (a : ℚ) • dualA + (b : ℚ) • dualB := by module
  have ha := dualA_mem_dual _ h
  have hb := dualB_mem_dual _ h
  have hba : form dualB dualA = 0 := by rw [form_isSymm.eq, dualA_pair_dualB]
  simp only [heq, map_add, map_smul, smul_eq_mul, dualA_pair_dualB, mul_zero, add_zero] at ha
  simp only [heq, map_add, map_smul, smul_eq_mul, hba, mul_zero, zero_add] at hb
  exact ⟨norm_denominator_unit (p := 5) (r := 2) (k := 0) (by norm_num)
      ⟨1, -2, by norm_num⟩ (by simpa using dualA_norm) a ha,
    norm_denominator_unit (p := 5) (r := 4) (k := 2) (by norm_num)
      ⟨1, -1, by norm_num⟩ (by rw [dualB_norm]; norm_num) b hb⟩

theorem rightFraction_mem_extension (c : Fin 2 → ℤ) :
    rightFraction c ∈ lattice ⊔ Submodule.span ℤ {dualA, dualB} := by
  let d : Fin 2 → ℤ := fun i => if i = 0 then 0 else c 1
  have hd : ((0 : Fin 2 → ℚ), intCoordsToRat d) ∈ lattice :=
    Submodule.mem_sup_left ⟨(coordinateIntegerLattice 2).zero_mem, intCoordsToRat_mem d⟩
  have heq : rightFraction c = ((0 : Fin 2 → ℚ), intCoordsToRat d) +
      (c 0 - 2 * c 1) • dualA + (-(c 1)) • dualB := by
    apply Prod.ext
    · simp [rightFraction, dualA, dualB]
    · ext i
      fin_cases i <;>
        norm_num [rightFraction, dualA, dualB, d, intCoordsToRat_apply, zsmul_eq_mul] <;> ring
  have ha : dualA ∈ Submodule.span ℤ {dualA, dualB} := Submodule.subset_span (by simp)
  have hb : dualB ∈ Submodule.span ℤ {dualA, dualB} := Submodule.subset_span (by simp)
  rw [heq]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.mem_sup_left hd)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ ha)))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ hb))

theorem lattice_dual : form.dualSubmodule lattice = lattice ⊔ Submodule.span ℤ {dualA, dualB} := by
  apply le_antisymm
  · intro z hz
    have hp : z ∈ (prodForm (simplexRatForm 2) rightForm).dualSubmodule
        ((coordinateIntegerLattice 2).prod (coordinateIntegerLattice 2)) :=
      fun w hw => hz w (Submodule.mem_sup_left hw)
    rw [dualSubmodule_prodForm] at hp
    obtain ⟨hx, hy⟩ := hp
    have hy' := (mem_dual_smul_form_iff (B := simplexRatForm 2)
      (N := coordinateIntegerLattice 2) (5 : ℚ) z.2).mp hy
    rw [simplexRatForm_dual] at hx hy'
    obtain ⟨nx, hnx, rwgt, hrwgt, heqx⟩ := Submodule.mem_sup.mp hx
    obtain ⟨ny, hny, swgt, hswgt, heqy⟩ := Submodule.mem_sup.mp hy'
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hrwgt
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hswgt
    obtain ⟨a, rfl⟩ := hnx
    obtain ⟨b, rfl⟩ := hny
    have hg : glueVector ∈ lattice :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    have he : form z glueVector = (∑ i, (a i : ℚ)) + (∑ i, (b i : ℚ)) +
        ((r : ℚ) + s) * (2 / 3) := by
      have hr : r • simplexWeight 2 = (r : ℚ) • simplexWeight 2 := by module
      have hs : s • simplexWeight 2 = (s : ℚ) • simplexWeight 2 := by module
      have hscale : rightForm z.2 (simplexWeight 2) =
          simplexRatForm 2 ((5 : ℚ) • z.2) (simplexWeight 2) := by
        simp [rightForm]
      change simplexRatForm 2 z.1 (simplexWeight 2) +
        rightForm z.2 (simplexWeight 2) = _
      rw [hscale, ← heqx, ← heqy, hr, hs]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [simplexWeight_norm, (simplexRatForm_isSymm 2).eq (intCoordsToRat a),
        (simplexRatForm_isSymm 2).eq (intCoordsToRat b)]
      simp only [simplexWeight_pair]
      norm_num only [Nat.cast_ofNat, intCoordsToRat_apply]
      ring
    obtain ⟨t, ht⟩ := mem_one_iff.mp (hz glueVector hg)
    have hQ : (2 : ℚ) * ((r : ℚ) + s) =
        3 * ((t : ℚ) - (∑ i, a i : ℤ) - (∑ i, b i : ℤ)) := by
      rw [he] at ht
      push_cast
      linarith
    have hZ : 2 * (r + s) = 3 * (t - (∑ i, a i) - (∑ i, b i)) := by
      exact_mod_cast hQ
    have hrs : (3 : ℤ) ∣ r + s := by omega
    obtain ⟨k, hk⟩ := hrs
    let c : Fin 2 → ℤ := fun i => b i + k - 2 * r
    have hdecomp : z = ((intCoordsToRat a, (0 : Fin 2 → ℚ)) + r • glueVector) +
        rightFraction c := by
      apply Prod.ext
      · change z.1 = (intCoordsToRat a + r • simplexWeight 2) + 0
        simpa only [add_zero] using heqx.symm
      · ext i
        have hs : s • simplexWeight 2 = (s : ℚ) • simplexWeight 2 := by module
        rw [hs] at heqy
        have hi := congrFun heqy i
        change (b i : ℚ) + (s : ℚ) * simplexWeight 2 i = 5 * z.2 i at hi
        norm_num only [simplexWeight] at hi
        change z.2 i = (0 + r • simplexWeight 2 i) + (1 / 5 : ℚ) * (c i : ℚ)
        norm_num only [simplexWeight, zsmul_eq_mul]
        dsimp [c]
        push_cast
        have hkQ : (r : ℚ) + s = 3 * (k : ℚ) := by exact_mod_cast hk
        linarith
    have hn : (intCoordsToRat a, (0 : Fin 2 → ℚ)) ∈ lattice :=
      Submodule.mem_sup_left ⟨intCoordsToRat_mem a, (coordinateIntegerLattice 2).zero_mem⟩
    rw [hdecomp]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (lattice.add_mem hn (lattice.smul_mem r hg)))
      (rightFraction_mem_extension c)
  · refine sup_le lattice_isIntegral (Submodule.span_le.mpr ?_)
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz :
      z = dualA ∨ z = dualB) with rfl | rfl
    · exact dualA_mem_dual
    · exact dualB_mem_dual

end SRG266.Lattice.K4Coordinates
