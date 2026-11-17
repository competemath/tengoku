import Tengoku.LeanEvalPlatonicClassification.Submission.CellVentiquattro
import Tengoku.LeanEvalPlatonicClassification.Submission.MacchinaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.FacciaArgmax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
La bandiera fondamentale del 24-cell e le quattro riflessioni di parete.

Il file mantiene tutti i certificati nel kernel di Lean.  Le quattro facce
sono esposte direttamente sul 24-cell dai pesi, rispettivamente,
`(2,1,0,0)`, `(2,1,1,0)`, `(1,1,1,0)` e `(1,1,1,1)`.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set Metric PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

private abbrev E4 := E 4

def v0_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 0 1 (by omega) true true)
def v1_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 0 2 (by omega) true true)
def v2_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 1 2 (by omega) true true)
def v3_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 0 3 (by omega) true true)
def v4_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 1 3 (by omega) true true)
def v5_24 : E4 :=
  vertVentiquattro (codiceVentiquattro 2 3 (by omega) true true)

def l0_24 : E4 →L[ℝ] ℝ :=
  2 • EuclideanSpace.proj (0 : Fin 4) + EuclideanSpace.proj (1 : Fin 4)

def l1_24 : E4 →L[ℝ] ℝ :=
  2 • EuclideanSpace.proj (0 : Fin 4) + EuclideanSpace.proj (1 : Fin 4) +
    EuclideanSpace.proj (2 : Fin 4)

def l2_24 : E4 →L[ℝ] ℝ :=
  EuclideanSpace.proj (0 : Fin 4) + EuclideanSpace.proj (1 : Fin 4) +
    EuclideanSpace.proj (2 : Fin 4)

def l3_24 : E4 →L[ℝ] ℝ :=
  EuclideanSpace.proj (0 : Fin 4) + EuclideanSpace.proj (1 : Fin 4) +
    EuclideanSpace.proj (2 : Fin 4) + EuclideanSpace.proj (3 : Fin 4)

def generatoriF0_24 : Finset E4 := {v0_24}
def generatoriF1_24 : Finset E4 := {v0_24, v1_24}
def generatoriF2_24 : Finset E4 := {v0_24, v1_24, v2_24}
def generatoriF3_24 : Finset E4 := {v0_24, v1_24, v2_24, v3_24, v4_24, v5_24}

def F0_24 : Set E4 := convexHull ℝ (generatoriF0_24 : Set E4)
def F1_24 : Set E4 := convexHull ℝ (generatoriF1_24 : Set E4)
def F2_24 : Set E4 := convexHull ℝ (generatoriF2_24 : Set E4)
def F3_24 : Set E4 := convexHull ℝ (generatoriF3_24 : Set E4)

private theorem vi_mem_vertices :
    v0_24 ∈ (verticiVentiquattro : Set E4) ∧
      v1_24 ∈ (verticiVentiquattro : Set E4) ∧
      v2_24 ∈ (verticiVentiquattro : Set E4) ∧
      v3_24 ∈ (verticiVentiquattro : Set E4) ∧
      v4_24 ∈ (verticiVentiquattro : Set E4) ∧
      v5_24 ∈ (verticiVentiquattro : Set E4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 0 1 (by omega) true true, rfl⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 0 2 (by omega) true true, rfl⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 1 2 (by omega) true true, rfl⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 0 3 (by omega) true true, rfl⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 1 3 (by omega) true true, rfl⟩
  · exact_mod_cast mem_verticiVentiquattro.mpr
      ⟨codiceVentiquattro 2 3 (by omega) true true, rfl⟩

private theorem li_values :
    l0_24 v0_24 = 3 ∧
      (l1_24 v0_24 = 3 ∧ l1_24 v1_24 = 3) ∧
      (l2_24 v0_24 = 2 ∧ l2_24 v1_24 = 2 ∧ l2_24 v2_24 = 2) ∧
      (l3_24 v0_24 = 2 ∧ l3_24 v1_24 = 2 ∧ l3_24 v2_24 = 2 ∧
        l3_24 v3_24 = 2 ∧ l3_24 v4_24 = 2 ∧ l3_24 v5_24 = 2) := by
  have h01 : (0 : Fin 4) ≠ 1 := by omega
  have h02 : (0 : Fin 4) ≠ 2 := by omega
  have h03 : (0 : Fin 4) ≠ 3 := by omega
  have h12 : (1 : Fin 4) ≠ 2 := by omega
  have h13 : (1 : Fin 4) ≠ 3 := by omega
  have h23 : (2 : Fin 4) ≠ 3 := by omega
  norm_num [l0_24, l1_24, l2_24, l3_24, v0_24, v1_24, v2_24,
    v3_24, v4_24, v5_24, vertVentiquattro, segnoVentiquattro,
    h01, h02, h03, h12, h13, h23, Ne.symm h01, Ne.symm h02,
    Ne.symm h03, Ne.symm h12, Ne.symm h13, Ne.symm h23]

private theorem code_of_l0_eq (c : CodiceVentiquattro)
    (h : l0_24 (vertVentiquattro c) = 3) :
    c = codiceVentiquattro 0 1 (by omega) true true := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals norm_num [l0_24, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals norm_num [codiceVentiquattro, Fin.ext_iff]

private theorem code_of_l1_eq (c : CodiceVentiquattro)
    (h : l1_24 (vertVentiquattro c) = 3) :
    c = codiceVentiquattro 0 1 (by omega) true true ∨
      c = codiceVentiquattro 0 2 (by omega) true true := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals norm_num [l1_24, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals norm_num [codiceVentiquattro, Fin.ext_iff]

private theorem code_of_l2_eq (c : CodiceVentiquattro)
    (h : l2_24 (vertVentiquattro c) = 2) :
    c = codiceVentiquattro 0 1 (by omega) true true ∨
      c = codiceVentiquattro 0 2 (by omega) true true ∨
      c = codiceVentiquattro 1 2 (by omega) true true := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals norm_num [l2_24, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals norm_num [codiceVentiquattro, Fin.ext_iff]

private theorem code_of_l3_eq (c : CodiceVentiquattro)
    (h : l3_24 (vertVentiquattro c) = 2) :
    c = codiceVentiquattro 0 1 (by omega) true true ∨
      c = codiceVentiquattro 0 2 (by omega) true true ∨
      c = codiceVentiquattro 1 2 (by omega) true true ∨
      c = codiceVentiquattro 0 3 (by omega) true true ∨
      c = codiceVentiquattro 1 3 (by omega) true true ∨
      c = codiceVentiquattro 2 3 (by omega) true true := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals norm_num [l3_24, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals norm_num [codiceVentiquattro, Fin.ext_iff]

private theorem argmax_l0_24 :
    {x ∈ (verticiVentiquattro : Set E4) | l0_24 x = 3} =
      (generatoriF0_24 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ verticiVentiquattro := by exact_mod_cast hx
    rw [mem_verticiVentiquattro] at hx'
    obtain ⟨c, rfl⟩ := hx'
    rw [code_of_l0_eq c hl]
    simp [generatoriF0_24, v0_24]
  · intro hx
    have : x = v0_24 := by simpa [generatoriF0_24] using hx
    subst x
    exact ⟨vi_mem_vertices.1, li_values.1⟩

private theorem argmax_l1_24 :
    {x ∈ (verticiVentiquattro : Set E4) | l1_24 x = 3} =
      (generatoriF1_24 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ verticiVentiquattro := by exact_mod_cast hx
    rw [mem_verticiVentiquattro] at hx'
    obtain ⟨c, rfl⟩ := hx'
    rcases code_of_l1_eq c hl with hc | hc <;> rw [hc] <;>
      simp [generatoriF1_24, v0_24, v1_24]
  · intro hx
    have cases : x = v0_24 ∨ x = v1_24 := by
      simpa [generatoriF1_24] using hx
    rcases cases with rfl | rfl
    · exact ⟨vi_mem_vertices.1, li_values.2.1.1⟩
    · exact ⟨vi_mem_vertices.2.1, li_values.2.1.2⟩

private theorem argmax_l2_24 :
    {x ∈ (verticiVentiquattro : Set E4) | l2_24 x = 2} =
      (generatoriF2_24 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ verticiVentiquattro := by exact_mod_cast hx
    rw [mem_verticiVentiquattro] at hx'
    obtain ⟨c, rfl⟩ := hx'
    rcases code_of_l2_eq c hl with hc | hc | hc <;> rw [hc] <;>
      simp [generatoriF2_24, v0_24, v1_24, v2_24]
  · intro hx
    have cases : x = v0_24 ∨ x = v1_24 ∨ x = v2_24 := by
      simpa [generatoriF2_24] using hx
    rcases cases with rfl | rfl | rfl
    · exact ⟨vi_mem_vertices.1, li_values.2.2.1.1⟩
    · exact ⟨vi_mem_vertices.2.1, li_values.2.2.1.2.1⟩
    · exact ⟨vi_mem_vertices.2.2.1, li_values.2.2.1.2.2⟩

private theorem argmax_l3_24 :
    {x ∈ (verticiVentiquattro : Set E4) | l3_24 x = 2} =
      (generatoriF3_24 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ verticiVentiquattro := by exact_mod_cast hx
    rw [mem_verticiVentiquattro] at hx'
    obtain ⟨c, rfl⟩ := hx'
    rcases code_of_l3_eq c hl with hc | hc | hc | hc | hc | hc <;> rw [hc] <;>
      simp [generatoriF3_24, v0_24, v1_24, v2_24, v3_24, v4_24, v5_24]
  · intro hx
    have cases : x = v0_24 ∨ x = v1_24 ∨ x = v2_24 ∨
        x = v3_24 ∨ x = v4_24 ∨ x = v5_24 := by
      simpa [generatoriF3_24] using hx
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨vi_mem_vertices.1, li_values.2.2.2.1⟩
    · exact ⟨vi_mem_vertices.2.1, li_values.2.2.2.2.1⟩
    · exact ⟨vi_mem_vertices.2.2.1, li_values.2.2.2.2.2.1⟩
    · exact ⟨vi_mem_vertices.2.2.2.1, li_values.2.2.2.2.2.2.1⟩
    · exact ⟨vi_mem_vertices.2.2.2.2.1, li_values.2.2.2.2.2.2.2.1⟩
    · exact ⟨vi_mem_vertices.2.2.2.2.2, li_values.2.2.2.2.2.2.2.2⟩

private theorem li_vert_le (c : CodiceVentiquattro) :
    l0_24 (vertVentiquattro c) ≤ 3 ∧
      l1_24 (vertVentiquattro c) ≤ 3 ∧
      l2_24 (vertVentiquattro c) ≤ 2 ∧
      l3_24 (vertVentiquattro c) ≤ 2 := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals norm_num [l0_24, l1_24, l2_24, l3_24, vertVentiquattro,
    segnoVentiquattro, indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff]

private theorem li_toSet_le :
    (∀ x ∈ ventiquattro.toSet, l0_24 x ≤ 3) ∧
      (∀ x ∈ ventiquattro.toSet, l1_24 x ≤ 3) ∧
      (∀ x ∈ ventiquattro.toSet, l2_24 x ≤ 2) ∧
      (∀ x ∈ ventiquattro.toSet, l3_24 x ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply le_su_toSet <;> intro v hv
  all_goals
    have hv' : v ∈ verticiVentiquattro := by exact_mod_cast hv
    rw [mem_verticiVentiquattro] at hv'
    obtain ⟨c, rfl⟩ := hv'
  · exact (li_vert_le c).1
  · exact (li_vert_le c).2.1
  · exact (li_vert_le c).2.2.1
  · exact (li_vert_le c).2.2.2

private theorem isExposed_argmax_24 (s : Finset E4) (l : E4 →L[ℝ] ℝ)
    (c : ℝ) (hs : s.Nonempty)
    (harg : {x ∈ (verticiVentiquattro : Set E4) | l x = c} = (s : Set E4))
    (hle : ∀ x ∈ ventiquattro.toSet, l x ≤ c) :
    IsExposed ℝ ventiquattro.toSet (convexHull ℝ (s : Set E4)) := by
  intro _
  have hsV : (s : Set E4) ⊆ (verticiVentiquattro : Set E4) := by
    intro x hx
    rw [← harg] at hx
    exact hx.1
  have hsP : (s : Set E4) ⊆ ventiquattro.toSet := by
    intro x hx
    exact subset_convexHull ℝ _ (by exact_mod_cast hsV hx)
  have hsub : convexHull ℝ (s : Set E4) ⊆ ventiquattro.toSet :=
    convexHull_min hsP (convex_convexHull ℝ _)
  have heq : ∀ x ∈ (s : Set E4), l x = c := by
    intro x hx
    rw [← harg] at hx
    exact hx.2
  have hge : ∀ x ∈ convexHull ℝ (s : Set E4), c ≤ l x := by
    intro x hx
    exact convexHull_min (fun y hy => by
        change c ≤ l y
        rw [heq y hy])
      (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c) hx
  refine ⟨l, Set.ext ?_⟩
  intro x
  constructor
  · intro hx
    have hlx : l x = c := le_antisymm (hle x (hsub hx)) (hge x hx)
    refine ⟨hsub hx, ?_⟩
    intro y hy
    rw [hlx]
    exact hle y hy
  · rintro ⟨hxP, hxmax⟩
    obtain ⟨a, ha⟩ := hs
    have haS : a ∈ (s : Set E4) := by exact_mod_cast ha
    have haP : a ∈ ventiquattro.toSet := hsP haS
    have hlx : l x = c := by
      apply le_antisymm (hle x hxP)
      simpa [heq a haS] using hxmax a haP
    have hxarg := faccia_argmax verticiVentiquattro l hxP hxmax
    have hset : {z ∈ (verticiVentiquattro : Set E4) | l z = l x} =
        (s : Set E4) := by simpa [hlx] using harg
    rwa [hset] at hxarg

theorem F0_24_isFace : ventiquattro.IsFace F0_24 := by
  refine ⟨?_, ⟨v0_24, subset_convexHull ℝ _ (by simp [generatoriF0_24])⟩⟩
  exact isExposed_argmax_24 generatoriF0_24 l0_24 3
    (by simp [generatoriF0_24]) argmax_l0_24 li_toSet_le.1

theorem F1_24_isFace : ventiquattro.IsFace F1_24 := by
  refine ⟨?_, ⟨v0_24, subset_convexHull ℝ _ (by simp [generatoriF1_24])⟩⟩
  exact isExposed_argmax_24 generatoriF1_24 l1_24 3
    (by simp [generatoriF1_24]) argmax_l1_24 li_toSet_le.2.1

theorem F2_24_isFace : ventiquattro.IsFace F2_24 := by
  refine ⟨?_, ⟨v0_24, subset_convexHull ℝ _ (by simp [generatoriF2_24])⟩⟩
  exact isExposed_argmax_24 generatoriF2_24 l2_24 2
    (by simp [generatoriF2_24]) argmax_l2_24 li_toSet_le.2.2.1

theorem F3_24_isFace : ventiquattro.IsFace F3_24 := by
  refine ⟨?_, ⟨v0_24, subset_convexHull ℝ _ (by simp [generatoriF3_24])⟩⟩
  exact isExposed_argmax_24 generatoriF3_24 l3_24 2
    (by simp [generatoriF3_24]) argmax_l3_24 li_toSet_le.2.2.2

private def p2_24 : Fin 3 → E4 := ![v0_24, v1_24, v2_24]
private def p3_24 : Fin 4 → E4 := ![v0_24, v1_24, v2_24, v3_24]

@[simp] private theorem p2_24_zero : p2_24 0 = v0_24 := rfl
@[simp] private theorem p2_24_one : p2_24 1 = v1_24 := rfl
@[simp] private theorem p2_24_two : p2_24 2 = v2_24 := rfl
@[simp] private theorem p3_24_zero : p3_24 0 = v0_24 := rfl
@[simp] private theorem p3_24_one : p3_24 1 = v1_24 := rfl
@[simp] private theorem p3_24_two : p3_24 2 = v2_24 := rfl
@[simp] private theorem p3_24_three : p3_24 3 = v3_24 := rfl

private theorem p2_24_affineIndependent : AffineIndependent ℝ p2_24 := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hc (j : Fin 4) := congrArg (fun x : E4 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hc
  have h0 := hc 0
  have h1 := hc 1
  rw [Fin.sum_univ_three] at ha hb
  norm_num [v0_24, v1_24, v2_24, vertVentiquattro,
    segnoVentiquattro, Fin.sum_univ_three, Fin.ext_iff] at h0 h1
  have e0 : a 0 = b 0 := by linarith
  have e1 : a 1 = b 1 := by linarith
  have e2 : a 2 = b 2 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

private theorem p3_24_affineIndependent : AffineIndependent ℝ p3_24 := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hc (j : Fin 4) := congrArg (fun x : E4 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [Fin.sum_univ_four] at ha hb
  norm_num [v0_24, v1_24, v2_24, v3_24, vertVentiquattro,
    segnoVentiquattro, Fin.sum_univ_four, Fin.ext_iff] at h0 h1 h2 h3
  have e0 : a 0 = b 0 := by linarith
  have e1 : a 1 = b 1 := by linarith
  have e2 : a 2 = b 2 := by linarith
  have e3 : a 3 = b 3 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

private theorem range_p2_24 :
    Set.range p2_24 = (generatoriF2_24 : Set E4) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [p2_24, generatoriF2_24]
  · intro hx
    have : x = v0_24 ∨ x = v1_24 ∨ x = v2_24 := by
      simpa [generatoriF2_24] using hx
    rcases this with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem faceDim_F0_24 : faceDim F0_24 = 0 := by
  rw [F0_24, generatoriF0_24]
  simpa using faceDim_singleton v0_24

private theorem v0_ne_v1_24 : v0_24 ≠ v1_24 := by
  intro h
  have hc := congrArg (fun x : E4 => x (1 : Fin 4)) h
  norm_num [v0_24, v1_24, vertVentiquattro, segnoVentiquattro,
    Fin.ext_iff] at hc

theorem faceDim_F1_24 : faceDim F1_24 = 1 := by
  have hgen : (generatoriF1_24 : Set E4) = {v0_24, v1_24} := by
    ext x
    simp [generatoriF1_24]
  rw [F1_24, hgen, convexHull_pair]
  unfold faceDim
  rw [vectorSpan_segment]
  apply finrank_span_singleton
  exact vsub_ne_zero.mpr v0_ne_v1_24.symm

theorem faceDim_F2_24 : faceDim F2_24 = 2 := by
  unfold faceDim
  rw [F2_24, ← direction_affineSpan, affineSpan_convexHull,
    direction_affineSpan, ← range_p2_24]
  exact p2_24_affineIndependent.finrank_vectorSpan (by simp)

private theorem l3_eq_on_F3_24 {x : E4} (hx : x ∈ F3_24) : l3_24 x = 2 := by
  apply le_antisymm (li_toSet_le.2.2.2 x (F3_24_isFace.1.subset hx))
  rw [F3_24] at hx
  exact convexHull_min (fun y hy => by
      change (2 : ℝ) ≤ l3_24 y
      have hy' : y ∈ (generatoriF3_24 : Set E4) := hy
      rw [← argmax_l3_24] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l3_24.toLinearMap) 2) hx

private theorem span_F3_le_ker_l3 :
    vectorSpan ℝ F3_24 ≤ LinearMap.ker l3_24.toLinearMap := by
  show Submodule.span ℝ (F3_24 -ᵥ F3_24) ≤ _
  rw [Submodule.span_le]
  rintro d ⟨x, hx, y, hy, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  change l3_24 (x - y) = 0
  rw [map_sub, l3_eq_on_F3_24 hx, l3_eq_on_F3_24 hy, sub_self]

private theorem finrank_ker_l3_24 :
    Module.finrank ℝ (LinearMap.ker l3_24.toLinearMap) = 3 := by
  have hsurj : Function.Surjective l3_24.toLinearMap := by
    intro t
    refine ⟨t • EuclideanSpace.single (0 : Fin 4) 1, ?_⟩
    norm_num [l3_24, Fin.ext_iff]
  have hr := LinearMap.finrank_range_add_finrank_ker l3_24.toLinearMap
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  have hE : Module.finrank ℝ E4 = 4 := by simp [E4, finrank_euclideanSpace]
  have hR : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  omega

theorem faceDim_F3_24 : faceDim F3_24 = 3 := by
  unfold faceDim
  apply le_antisymm
  · calc
      Module.finrank ℝ (vectorSpan ℝ F3_24) ≤
          Module.finrank ℝ (LinearMap.ker l3_24.toLinearMap) :=
        Submodule.finrank_mono span_F3_le_ker_l3
      _ = 3 := finrank_ker_l3_24
  · have hsub : vectorSpan ℝ (Set.range p3_24) ≤ vectorSpan ℝ F3_24 := by
      apply vectorSpan_mono ℝ
      rintro x ⟨i, rfl⟩
      apply subset_convexHull ℝ _
      fin_cases i <;> simp [p3_24, generatoriF3_24]
    calc
      3 = Module.finrank ℝ (vectorSpan ℝ (Set.range p3_24)) :=
        (p3_24_affineIndependent.finrank_vectorSpan (by simp)).symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ F3_24) :=
        Submodule.finrank_mono hsub

theorem F0_ssubset_F1_24 : F0_24 ⊂ F1_24 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx0 : x = v0_24 := by simpa [generatoriF0_24] using hx
    subst x
    simp [generatoriF1_24]
  · intro h
    have := faceDim_F0_24
    rw [h, faceDim_F1_24] at this
    omega

theorem F1_ssubset_F2_24 : F1_24 ⊂ F2_24 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx01 : x = v0_24 ∨ x = v1_24 := by
      simpa [generatoriF1_24] using hx
    rcases hx01 with rfl | rfl <;> simp [generatoriF2_24]
  · intro h
    have := faceDim_F1_24
    rw [h, faceDim_F2_24] at this
    omega

theorem F2_ssubset_F3_24 : F2_24 ⊂ F3_24 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx012 : x = v0_24 ∨ x = v1_24 ∨ x = v2_24 := by
      simpa [generatoriF2_24] using hx
    rcases hx012 with rfl | rfl | rfl <;> simp [generatoriF3_24]
  · intro h
    have := faceDim_F2_24
    rw [h, faceDim_F3_24] at this
    omega

/-- La bandiera fondamentale del 24-cell.-/
def ventiquattroFlag : ventiquattro.Flag where
  face i := ![F0_24, F1_24, F2_24, F3_24] i
  isFace i := by
    fin_cases i
    · exact F0_24_isFace
    · exact F1_24_isFace
    · exact F2_24_isFace
    · exact F3_24_isFace
  dim_eq i := by
    fin_cases i
    · exact faceDim_F0_24
    · exact faceDim_F1_24
    · exact faceDim_F2_24
    · exact faceDim_F3_24
  strict_mono i j hij := by
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    · exact F0_ssubset_F1_24
    · exact F0_ssubset_F1_24.trans F1_ssubset_F2_24
    · exact F0_ssubset_F1_24.trans (F1_ssubset_F2_24.trans F2_ssubset_F3_24)
    · exact F1_ssubset_F2_24
    · exact F1_ssubset_F2_24.trans F2_ssubset_F3_24
    · exact F2_ssubset_F3_24

private theorem segnoPerm_vertVentiquattro_24
    (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ({-1, 1} : Set ℝ))
    (c : CodiceVentiquattro) :
    ∃ d : CodiceVentiquattro,
      segnoPerm 4 σ ε (vertVentiquattro c) = vertVentiquattro d := by
  let i := indicePrimoVentiquattro c
  let j := indiceSecondoVentiquattro c
  let si := segnoBoolDaReale (ε i) (segnoPrimoVentiquattro c)
  let sj := segnoBoolDaReale (ε j) (segnoSecondoVentiquattro c)
  have hij : i ≠ j := indicePrimo_ne_indiceSecondo c
  by_cases hlt : σ i < σ j
  · refine ⟨codiceVentiquattro (σ i) (σ j) hlt si sj, ?_⟩
    simp only [segnoPerm_apply, vertVentiquattro, map_add, segnoLinear_single,
      indicePrimo_codiceVentiquattro, indiceSecondo_codiceVentiquattro,
      segnoPrimo_codiceVentiquattro, segnoSecondo_codiceVentiquattro]
    rw [segnoBoolDaReale_spec, segnoBoolDaReale_spec]
  · have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
    have hgt : σ j < σ i := by omega
    refine ⟨codiceVentiquattro (σ j) (σ i) hgt sj si, ?_⟩
    simp only [segnoPerm_apply, vertVentiquattro, map_add, segnoLinear_single,
      indicePrimo_codiceVentiquattro, indiceSecondo_codiceVentiquattro,
      segnoPrimo_codiceVentiquattro, segnoSecondo_codiceVentiquattro]
    rw [segnoBoolDaReale_spec, segnoBoolDaReale_spec, add_comm]

private theorem segnoPerm_mem_verticiVentiquattro_24
    (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ({-1, 1} : Set ℝ))
    {v : E4} (hv : v ∈ verticiVentiquattro) :
    segnoPerm 4 σ ε v ∈ verticiVentiquattro := by
  rw [mem_verticiVentiquattro] at hv
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨d, hd⟩ := segnoPerm_vertVentiquattro_24 σ ε c
  exact mem_verticiVentiquattro.mpr ⟨d, hd.symm⟩

private theorem segnoPerm_image_verticiVentiquattro_24
    (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    (segnoPerm 4 σ ε : E4 → E4) '' (verticiVentiquattro : Set E4) =
      (verticiVentiquattro : Set E4) := by
  have hfin :
      Finset.image (segnoPerm 4 σ ε : E4 → E4) verticiVentiquattro =
        verticiVentiquattro := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact segnoPerm_mem_verticiVentiquattro_24 σ ε hu
    · rw [Finset.card_image_of_injective _ (segnoPerm 4 σ ε).injective]
  rw [← Finset.coe_image, hfin]

theorem segnoPerm_isSymmetry_ventiquattro
    (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    ventiquattro.isSymmetry (segnoPerm 4 σ ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm 4 σ ε : E4 → E4) ''
        convexHull ℝ ((ventiquattro.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((segnoPerm 4 σ ε : E4 → E4) ''
        ((ventiquattro.vertices : Finset E4) : Set E4)) := by
          exact (segnoPerm 4 σ ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ventiquattro.vertices : Finset E4) : Set E4) := by
      rw [show ((ventiquattro.vertices : Finset E4) : Set E4) =
          (verticiVentiquattro : Set E4) by rfl,
        segnoPerm_image_verticiVentiquattro_24]

private def segnoUno_24 : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun _ => ⟨1, by simp⟩

private def segnoQuarta_24 : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun i => if i = 3 then ⟨-1, by simp⟩ else ⟨1, by simp⟩

/-- Parete 0: scambia le coordinate 1 e 2 (indici zero-based).-/
def r0_24 : Isom 4 := segnoPerm 4 (Equiv.swap 1 2) segnoUno_24

/-- Parete 1: scambia le coordinate 0 e 1.-/
def r1_24 : Isom 4 := segnoPerm 4 (Equiv.swap 0 1) segnoUno_24

/-- Parete 3: cambia il segno della coordinata 3.-/
def r3_24 : Isom 4 := segnoPerm 4 (Equiv.refl (Fin 4)) segnoQuarta_24

theorem r0_24_isSymmetry : ventiquattro.isSymmetry r0_24 :=
  segnoPerm_isSymmetry_ventiquattro _ _

theorem r1_24_isSymmetry : ventiquattro.isSymmetry r1_24 :=
  segnoPerm_isSymmetry_ventiquattro _ _

theorem r3_24_isSymmetry : ventiquattro.isSymmetry r3_24 :=
  segnoPerm_refl_isSymmetry segnoQuarta_24

private theorem r0_24_vertices :
    r0_24 v0_24 = v1_24 ∧ r0_24 v1_24 = v0_24 ∧
      r0_24 v2_24 = v2_24 ∧ r0_24 v3_24 = v3_24 ∧
      r0_24 v4_24 = v5_24 ∧ r0_24 v5_24 = v4_24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [r0_24, v0_24, v1_24, v2_24, v3_24, v4_24, v5_24,
      segnoPerm_apply, vertVentiquattro, map_add, segnoLinear_single]
    norm_num [segnoUno_24, Equiv.swap_apply_def, segnoVentiquattro,
      Fin.ext_iff]
  all_goals ac_rfl

private theorem r1_24_vertices :
    r1_24 v0_24 = v0_24 ∧ r1_24 v1_24 = v2_24 ∧
      r1_24 v2_24 = v1_24 ∧ r1_24 v3_24 = v4_24 ∧
      r1_24 v4_24 = v3_24 ∧ r1_24 v5_24 = v5_24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [r1_24, v0_24, v1_24, v2_24, v3_24, v4_24, v5_24,
      segnoPerm_apply, vertVentiquattro, map_add, segnoLinear_single]
    norm_num [segnoUno_24, Equiv.swap_apply_def, segnoVentiquattro,
      Fin.ext_iff]
  all_goals ac_rfl

private theorem r3_24_vertices :
    r3_24 v0_24 = v0_24 ∧ r3_24 v1_24 = v1_24 ∧
      r3_24 v2_24 = v2_24 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext k <;> fin_cases k <;>
    norm_num [r3_24, segnoQuarta_24, v0_24, v1_24, v2_24,
      segnoPerm_apply, segnoLinear_single, vertVentiquattro,
      segnoVentiquattro, isometriaSegno, Fin.ext_iff]

private theorem image_convexHull_isom24 (g : Isom 4) (s : Set E4) :
    (g : E4 → E4) '' convexHull ℝ s = convexHull ℝ ((g : E4 → E4) '' s) :=
  g.toAffineEquiv.toAffineMap.image_convexHull s

private theorem r0_image_F1_24 : (r0_24 : E4 → E4) '' F1_24 = F1_24 := by
  rw [F1_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF1_24, r0_24_vertices.1, r0_24_vertices.2.1] <;> tauto

private theorem r0_image_F2_24 : (r0_24 : E4 → E4) '' F2_24 = F2_24 := by
  rw [F2_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF2_24, r0_24_vertices.1, r0_24_vertices.2.1,
    r0_24_vertices.2.2.1] <;> tauto

private theorem r0_image_F3_24 : (r0_24 : E4 → E4) '' F3_24 = F3_24 := by
  rw [F3_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF3_24, r0_24_vertices.1, r0_24_vertices.2.1,
    r0_24_vertices.2.2.1, r0_24_vertices.2.2.2.1,
    r0_24_vertices.2.2.2.2.1, r0_24_vertices.2.2.2.2.2] <;> tauto

private theorem r1_image_F0_24 : (r1_24 : E4 → E4) '' F0_24 = F0_24 := by
  rw [F0_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF0_24, r1_24_vertices.1]

private theorem r1_image_F2_24 : (r1_24 : E4 → E4) '' F2_24 = F2_24 := by
  rw [F2_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF2_24, r1_24_vertices.1, r1_24_vertices.2.1,
    r1_24_vertices.2.2.1] <;> tauto

private theorem r1_image_F3_24 : (r1_24 : E4 → E4) '' F3_24 = F3_24 := by
  rw [F3_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF3_24, r1_24_vertices.1, r1_24_vertices.2.1,
    r1_24_vertices.2.2.1, r1_24_vertices.2.2.2.1,
    r1_24_vertices.2.2.2.2.1, r1_24_vertices.2.2.2.2.2] <;> tauto

private theorem r3_image_F0_24 : (r3_24 : E4 → E4) '' F0_24 = F0_24 := by
  rw [F0_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF0_24, r3_24_vertices.1]

private theorem r3_image_F1_24 : (r3_24 : E4 → E4) '' F1_24 = F1_24 := by
  rw [F1_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF1_24, r3_24_vertices.1, r3_24_vertices.2.1] <;> tauto

private theorem r3_image_F2_24 : (r3_24 : E4 → E4) '' F2_24 = F2_24 := by
  rw [F2_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF2_24, r3_24_vertices.1, r3_24_vertices.2.1,
    r3_24_vertices.2.2] <;> tauto

private theorem r0_moves_F0_24 : (r0_24 : E4 → E4) '' F0_24 ≠ F0_24 := by
  intro h
  have hv : v1_24 ∈ (r0_24 : E4 → E4) '' F0_24 :=
    ⟨v0_24, subset_convexHull ℝ _ (by simp [generatoriF0_24]),
      r0_24_vertices.1⟩
  rw [h, F0_24, generatoriF0_24] at hv
  have heq : v1_24 = v0_24 := by simpa using hv
  exact v0_ne_v1_24 heq.symm

private theorem l1_eq_on_F1_24 {x : E4} (hx : x ∈ F1_24) : l1_24 x = 3 := by
  apply le_antisymm (li_toSet_le.2.1 x (F1_24_isFace.1.subset hx))
  rw [F1_24] at hx
  exact convexHull_min (fun y hy => by
      change (3 : ℝ) ≤ l1_24 y
      have hy' : y ∈ (generatoriF1_24 : Set E4) := hy
      rw [← argmax_l1_24] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l1_24.toLinearMap) 3) hx

private theorem l1_v2_24 : l1_24 v2_24 = 2 := by
  norm_num [l1_24, v2_24, vertVentiquattro, segnoVentiquattro, Fin.ext_iff]

private theorem r1_moves_F1_24 : (r1_24 : E4 → E4) '' F1_24 ≠ F1_24 := by
  intro h
  have hv : v2_24 ∈ (r1_24 : E4 → E4) '' F1_24 :=
    ⟨v1_24, subset_convexHull ℝ _ (by simp [generatoriF1_24]),
      r1_24_vertices.2.1⟩
  rw [h] at hv
  have := l1_eq_on_F1_24 hv
  rw [l1_v2_24] at this
  norm_num at this

private theorem l3_r3_v3_24 : l3_24 (r3_24 v3_24) = 0 := by
  norm_num [l3_24, r3_24, segnoQuarta_24, v3_24, segnoPerm_apply,
    segnoLinear_single, vertVentiquattro, segnoVentiquattro,
    isometriaSegno, Fin.ext_iff]

private theorem r3_moves_F3_24 : (r3_24 : E4 → E4) '' F3_24 ≠ F3_24 := by
  intro h
  have hv : r3_24 v3_24 ∈ (r3_24 : E4 → E4) '' F3_24 :=
    ⟨v3_24, subset_convexHull ℝ _ (by simp [generatoriF3_24]), rfl⟩
  rw [h] at hv
  have := l3_eq_on_F3_24 hv
  rw [l3_r3_v3_24] at this
  norm_num at this

theorem r0_24_flagAdjacent :
    FlagAdjacentAt ventiquattro ventiquattroFlag
      (mapFlag ventiquattro r0_24_isSymmetry ventiquattroFlag) 0 := by
  constructor
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact r0_image_F1_24
    · exact r0_image_F2_24
    · exact r0_image_F3_24
  · exact r0_moves_F0_24

theorem r1_24_flagAdjacent :
    FlagAdjacentAt ventiquattro ventiquattroFlag
      (mapFlag ventiquattro r1_24_isSymmetry ventiquattroFlag) 1 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r1_image_F0_24
    · exact (hj rfl).elim
    · exact r1_image_F2_24
    · exact r1_image_F3_24
  · exact r1_moves_F1_24

theorem r3_24_flagAdjacent :
    FlagAdjacentAt ventiquattro ventiquattroFlag
      (mapFlag ventiquattro r3_24_isSymmetry ventiquattroFlag) 3 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r3_image_F0_24
    · exact r3_image_F1_24
    · exact r3_image_F2_24
    · exact (hj rfl).elim
  · exact r3_moves_F3_24

/-- La radice corta unitaria di F₄ che definisce la parete di rango 2.-/
def alpha_24 : E4 :=
  EuclideanSpace.single 0 (-(1 / 2 : ℝ)) +
    EuclideanSpace.single 1 (1 / 2 : ℝ) +
    EuclideanSpace.single 2 (1 / 2 : ℝ) +
    EuclideanSpace.single 3 (-(1 / 2 : ℝ))

private theorem norm_sq_alpha_24 : ‖alpha_24‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  norm_num [alpha_24, Fin.ext_iff]

private theorem norm_alpha_24 : ‖alpha_24‖ = 1 := by
  nlinarith [norm_sq_alpha_24, norm_nonneg alpha_24]

/-- Parete 2: riflessione ortogonale nell'iperpiano `alpha_24ᵖ`.-/
def r2_24 : Isom 4 :=
  ((ℝ ∙ alpha_24)ᗮ).reflection.toAffineIsometryEquiv

private theorem r2_24_formula (x : E4) :
    r2_24 x = x - (2 * ⟪alpha_24, x⟫ : ℝ) • alpha_24 := by
  change ((ℝ ∙ alpha_24)ᗮ).reflection x = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, norm_alpha_24]
  norm_num
  module

private theorem r2_24_vertices :
    r2_24 v0_24 = v0_24 ∧ r2_24 v1_24 = v1_24 ∧
      r2_24 v2_24 = v3_24 ∧ r2_24 v3_24 = v2_24 ∧
      r2_24 v4_24 = v4_24 ∧ r2_24 v5_24 = v5_24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [r2_24_formula]
    ext k
    fin_cases k <;>
      norm_num [alpha_24, v0_24, v1_24, v2_24, v3_24, v4_24, v5_24,
        vertVentiquattro, segnoVentiquattro, inner_add_left,
        inner_add_right, EuclideanSpace.inner_single_left, Fin.ext_iff]

private def r2Code01_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 0 1 (by omega) false false
  | false, true => codiceVentiquattro 2 3 (by omega) false true
  | true, false => codiceVentiquattro 2 3 (by omega) true false
  | true, true => codiceVentiquattro 0 1 (by omega) true true

private def r2Code02_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 0 2 (by omega) false false
  | false, true => codiceVentiquattro 1 3 (by omega) false true
  | true, false => codiceVentiquattro 1 3 (by omega) true false
  | true, true => codiceVentiquattro 0 2 (by omega) true true

private def r2Code03_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 1 2 (by omega) false false
  | false, true => codiceVentiquattro 0 3 (by omega) false true
  | true, false => codiceVentiquattro 0 3 (by omega) true false
  | true, true => codiceVentiquattro 1 2 (by omega) true true

private def r2Code12_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 0 3 (by omega) false false
  | false, true => codiceVentiquattro 1 2 (by omega) false true
  | true, false => codiceVentiquattro 1 2 (by omega) true false
  | true, true => codiceVentiquattro 0 3 (by omega) true true

private def r2Code13_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 1 3 (by omega) false false
  | false, true => codiceVentiquattro 0 2 (by omega) false true
  | true, false => codiceVentiquattro 0 2 (by omega) true false
  | true, true => codiceVentiquattro 1 3 (by omega) true true

private def r2Code23_24 : Bool → Bool → CodiceVentiquattro
  | false, false => codiceVentiquattro 2 3 (by omega) false false
  | false, true => codiceVentiquattro 0 1 (by omega) false true
  | true, false => codiceVentiquattro 0 1 (by omega) true false
  | true, true => codiceVentiquattro 2 3 (by omega) true true

private theorem r2_pair01_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 0 1 (by omega) si sj)) =
      vertVentiquattro (r2Code01_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code01_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_pair02_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 0 2 (by omega) si sj)) =
      vertVentiquattro (r2Code02_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code02_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_pair03_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 0 3 (by omega) si sj)) =
      vertVentiquattro (r2Code03_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code03_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_pair12_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 1 2 (by omega) si sj)) =
      vertVentiquattro (r2Code12_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code12_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_pair13_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 1 3 (by omega) si sj)) =
      vertVentiquattro (r2Code13_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code13_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_pair23_24 (si sj : Bool) :
    r2_24 (vertVentiquattro (codiceVentiquattro 2 3 (by omega) si sj)) =
      vertVentiquattro (r2Code23_24 si sj) := by
  cases si <;> cases sj
  all_goals rw [r2_24_formula]
  all_goals ext k
  all_goals fin_cases k
  all_goals norm_num [r2Code23_24, alpha_24, vertVentiquattro,
    segnoVentiquattro, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_mem_verticiVentiquattro_24 {v : E4}
    (hv : v ∈ verticiVentiquattro) : r2_24 v ∈ verticiVentiquattro := by
  rw [mem_verticiVentiquattro] at hv ⊢
  obtain ⟨c, rfl⟩ := hv
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals first
    | exact ⟨r2Code01_24 si sj, (r2_pair01_24 si sj).symm⟩
    | exact ⟨r2Code02_24 si sj, (r2_pair02_24 si sj).symm⟩
    | exact ⟨r2Code03_24 si sj, (r2_pair03_24 si sj).symm⟩
    | exact ⟨r2Code12_24 si sj, (r2_pair12_24 si sj).symm⟩
    | exact ⟨r2Code13_24 si sj, (r2_pair13_24 si sj).symm⟩
    | exact ⟨r2Code23_24 si sj, (r2_pair23_24 si sj).symm⟩

private theorem r2_image_verticiVentiquattro_24 :
    (r2_24 : E4 → E4) '' (verticiVentiquattro : Set E4) =
      (verticiVentiquattro : Set E4) := by
  have hfin : Finset.image (r2_24 : E4 → E4) verticiVentiquattro =
      verticiVentiquattro := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact r2_mem_verticiVentiquattro_24 hu
    · rw [Finset.card_image_of_injective _ r2_24.injective]
  rw [← Finset.coe_image, hfin]

theorem r2_24_isSymmetry : ventiquattro.isSymmetry r2_24 := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (r2_24 : E4 → E4) ''
        convexHull ℝ ((ventiquattro.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((r2_24 : E4 → E4) ''
        ((ventiquattro.vertices : Finset E4) : Set E4)) := by
          exact r2_24.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((ventiquattro.vertices : Finset E4) : Set E4) := by
      rw [show ((ventiquattro.vertices : Finset E4) : Set E4) =
          (verticiVentiquattro : Set E4) by rfl,
        r2_image_verticiVentiquattro_24]

private theorem r2_image_F0_24 : (r2_24 : E4 → E4) '' F0_24 = F0_24 := by
  rw [F0_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF0_24, r2_24_vertices.1]

private theorem r2_image_F1_24 : (r2_24 : E4 → E4) '' F1_24 = F1_24 := by
  rw [F1_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF1_24, r2_24_vertices.1, r2_24_vertices.2.1] <;> tauto

private theorem r2_image_F3_24 : (r2_24 : E4 → E4) '' F3_24 = F3_24 := by
  rw [F3_24, image_convexHull_isom24]
  congr 1
  ext x
  simp [generatoriF3_24, r2_24_vertices.1, r2_24_vertices.2.1,
    r2_24_vertices.2.2.1, r2_24_vertices.2.2.2.1,
    r2_24_vertices.2.2.2.2.1, r2_24_vertices.2.2.2.2.2] <;> tauto

private theorem l2_eq_on_F2_24 {x : E4} (hx : x ∈ F2_24) : l2_24 x = 2 := by
  apply le_antisymm (li_toSet_le.2.2.1 x (F2_24_isFace.1.subset hx))
  rw [F2_24] at hx
  exact convexHull_min (fun y hy => by
      change (2 : ℝ) ≤ l2_24 y
      have hy' : y ∈ (generatoriF2_24 : Set E4) := hy
      rw [← argmax_l2_24] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l2_24.toLinearMap) 2) hx

private theorem l2_v3_24 : l2_24 v3_24 = 1 := by
  norm_num [l2_24, v3_24, vertVentiquattro, segnoVentiquattro, Fin.ext_iff]

private theorem r2_moves_F2_24 : (r2_24 : E4 → E4) '' F2_24 ≠ F2_24 := by
  intro h
  have hv : v3_24 ∈ (r2_24 : E4 → E4) '' F2_24 :=
    ⟨v2_24, subset_convexHull ℝ _ (by simp [generatoriF2_24]),
      r2_24_vertices.2.2.1⟩
  rw [h] at hv
  have := l2_eq_on_F2_24 hv
  rw [l2_v3_24] at this
  norm_num at this

theorem r2_24_flagAdjacent :
    FlagAdjacentAt ventiquattro ventiquattroFlag
      (mapFlag ventiquattro r2_24_isSymmetry ventiquattroFlag) 2 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r2_image_F0_24
    · exact r2_image_F1_24
    · exact (hj rfl).elim
    · exact r2_image_F3_24
  · exact r2_moves_F2_24

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
