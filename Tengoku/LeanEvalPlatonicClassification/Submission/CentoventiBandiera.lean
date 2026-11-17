import Tengoku.LeanEvalPlatonicClassification.Submission.CentoventiVertici
import Tengoku.LeanEvalPlatonicClassification.Submission.MacchinaBandiere
import Tengoku.LeanEvalPlatonicClassification.Submission.FacciaArgmax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/Solarys431/lean-eval-platonic-classification@3cd00dfd965e, `Submission/CentoventiBandiera.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
La bandiera fondamentale del 120-cell e le quattro riflessioni di parete.

I certificati sono organizzati per famiglia parametrica dei 600 vertici;
nessuna prova enumera in blocco il finset completo.
-/

open Set Metric PlatoniciL3
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope


private abbrev E4 := E 4

private def permA : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

private def permB : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 3

private def permC : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3 * Equiv.swap 1 2

@[simp] private theorem permA_symm_apply (i : Fin 4) :
    permA.symm i = ![2, 3, 0, 1] i := by
  fin_cases i <;> decide

@[simp] private theorem permB_symm_apply (i : Fin 4) :
    permB.symm i = ![1, 3, 2, 0] i := by
  fin_cases i <;> decide

@[simp] private theorem permC_symm_apply (i : Fin 4) :
    permC.symm i = ![3, 2, 1, 0] i := by
  fin_cases i <;> decide

private def sigmaA : alternatingGroup (Fin 4) :=
  ⟨permA, by
    apply Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide⟩

private def sigmaB : alternatingGroup (Fin 4) :=
  ⟨permB, by
    apply Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide⟩

private def sigmaC : alternatingGroup (Fin 4) :=
  ⟨permC, by
    apply Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide
    · rw [Equiv.Perm.swap_isSwap_iff]
      decide⟩

def v0_120 : E4 :=
  vertP1 (codiceVentiquattro 0 1 (by omega) true true)

def w0_120 : E4 := vertP6 sigmaA ![true, true, true]
def w1_120 : E4 := vertP6 sigmaA ![false, true, true]
def w2_120 : E4 := vertP6 sigmaC ![true, true, true]
def w3_120 : E4 := vertP6 sigmaC ![false, true, true]

def p4_120 : E4 := vertP5 sigmaA ![true, true, true]
def p5_120 : E4 := vertP5 sigmaA ![false, true, true]

private def cellVertex120 : Fin 20 → E4 := ![
  v0_120,
  vertP2 1 ![true, true, true, true],
  vertP2 1 ![true, true, true, false],
  vertP3 3 ![true, true, true, true],
  vertP3 3 ![true, true, true, false],
  vertP4 1 ![true, true, true, true],
  vertP4 1 ![true, true, true, false],
  p4_120,
  p5_120,
  vertP5 sigmaB ![true, true, true],
  w0_120,
  w1_120,
  vertP6 sigmaB ![true, true, true],
  w2_120,
  vertP7 sigmaA ![true, true, true, true],
  vertP7 sigmaA ![true, false, true, true],
  vertP7 sigmaB ![true, true, true, true],
  vertP7 sigmaB ![false, true, true, true],
  vertP7 sigmaC ![true, true, true, true],
  vertP7 sigmaC ![false, true, true, true]]

def generatoriF0_120 : Finset E4 := {v0_120}
def generatoriF1_120 : Finset E4 := {v0_120, w0_120}
def generatoriF2_120 : Finset E4 :=
  {v0_120, w0_120, w1_120, p4_120, p5_120}
def generatoriF3_120 : Finset E4 := Finset.univ.image cellVertex120

def F0_120 : Set E4 := convexHull ℝ (generatoriF0_120 : Set E4)
def F1_120 : Set E4 := convexHull ℝ (generatoriF1_120 : Set E4)
def F2_120 : Set E4 := convexHull ℝ (generatoriF2_120 : Set E4)
def F3_120 : Set E4 := convexHull ℝ (generatoriF3_120 : Set E4)

def l0_120 : E4 →L[ℝ] ℝ :=
  2 • EuclideanSpace.proj (0 : Fin 4) +
    2 • EuclideanSpace.proj (1 : Fin 4)

def l1_120 : E4 →L[ℝ] ℝ :=
  (2 + aureo) • EuclideanSpace.proj (0 : Fin 4) +
    (1 + 2 * aureo) • EuclideanSpace.proj (1 : Fin 4) +
    (aureo - 1) • EuclideanSpace.proj (3 : Fin 4)

def l2_120 : E4 →L[ℝ] ℝ :=
  aureo • EuclideanSpace.proj (0 : Fin 4) +
    (aureo + 1) • EuclideanSpace.proj (1 : Fin 4)

def l3_120 : E4 →L[ℝ] ℝ :=
  aureo • EuclideanSpace.proj (0 : Fin 4) +
    (aureo + 1) • EuclideanSpace.proj (1 : Fin 4) +
    EuclideanSpace.proj (2 : Fin 4)

private theorem sqrt_five_eq_aureo : Real.sqrt 5 = 2 * aureo - 1 := by
  rw [aureo]
  ring

private theorem fundamental_values :
    l0_120 v0_120 = 8 ∧
      (l1_120 v0_120 = 6 + 6 * aureo ∧
        l1_120 w0_120 = 6 + 6 * aureo) ∧
      (l2_120 v0_120 = 2 + 4 * aureo ∧
        l2_120 w0_120 = 2 + 4 * aureo ∧
        l2_120 w1_120 = 2 + 4 * aureo ∧
        l2_120 p4_120 = 2 + 4 * aureo ∧
        l2_120 p5_120 = 2 + 4 * aureo) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · norm_num [l0_120, v0_120, vertP1, vertVentiquattro,
      segnoVentiquattro, Fin.ext_iff]
  · norm_num [l1_120, v0_120, vertP1, vertVentiquattro,
      segnoVentiquattro, Fin.ext_iff]
    nlinarith [aureo_sq]
  · norm_num [l1_120, w0_120, sigmaA, vertP6_apply,
      base6, segnoZeroTesta, sqrt_five_eq_aureo,
      Equiv.swap_apply_def, Fin.ext_iff]
    simp at *
    nlinarith [aureo_sq]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals
      norm_num [l2_120, v0_120, w0_120, w1_120, p4_120, p5_120,
        sigmaA, vertP1, vertVentiquattro, segnoVentiquattro,
        vertP5_apply, vertP6_apply, base5, base6, segnoZeroTesta,
        sqrt_five_eq_aureo, Equiv.swap_apply_def, Fin.ext_iff]
    all_goals try simp at *
    all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem l3_cellVertex120 (i : Fin 20) :
    l3_120 (cellVertex120 i) = 2 + 4 * aureo := by
  fin_cases i <;>
    norm_num [cellVertex120, l3_120, v0_120, w0_120, w1_120, w2_120,
      p4_120, p5_120, sigmaA, sigmaB, sigmaC,
      vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
      vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
      vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
      sqrt_five_eq_aureo, Equiv.swap_apply_def, Fin.ext_iff] <;>
    (try simp at *) <;>
    nlinarith [aureo_sq]

private theorem vertP1_mem120 (c : CodiceVentiquattro) :
    vertP1 c ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c, rfl⟩)))))

private theorem vertP2_mem120 (i : Fin 4) (s : Fin 4 → Bool) :
    vertP2 i s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, s), rfl⟩)))))

private theorem vertP3_mem120 (i : Fin 4) (s : Fin 4 → Bool) :
    vertP3 i s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, s), rfl⟩))))

private theorem vertP4_mem120 (i : Fin 4) (s : Fin 4 → Bool) :
    vertP4 i s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, s), rfl⟩)))

private theorem vertP5_mem120 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : vertP5 sigma s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inr ⟨(sigma, s), rfl⟩))

private theorem vertP6_mem120 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : vertP6 sigma s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨(sigma, s), rfl⟩)

private theorem vertP7_mem120 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : vertP7 sigma s ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inr ⟨(sigma, s), rfl⟩

private theorem cellVertex120_mem (i : Fin 20) :
    cellVertex120 i ∈ centoventiVertici := by
  fin_cases i
  · exact vertP1_mem120 _
  · exact vertP2_mem120 _ _
  · exact vertP2_mem120 _ _
  · exact vertP3_mem120 _ _
  · exact vertP3_mem120 _ _
  · exact vertP4_mem120 _ _
  · exact vertP4_mem120 _ _
  · exact vertP5_mem120 _ _
  · exact vertP5_mem120 _ _
  · exact vertP5_mem120 _ _
  · exact vertP6_mem120 _ _
  · exact vertP6_mem120 _ _
  · exact vertP6_mem120 _ _
  · exact vertP6_mem120 _ _
  · exact vertP7_mem120 _ _
  · exact vertP7_mem120 _ _
  · exact vertP7_mem120 _ _
  · exact vertP7_mem120 _ _
  · exact vertP7_mem120 _ _
  · exact vertP7_mem120 _ _

private theorem P2_l1_le (i : Fin 4) (s : Fin 4 → Bool) :
    l1_120 (vertP2 i s) ≤ 6 + 6 * aureo := by
  fin_cases i <;>
    simp [l1_120, vertP2_apply] <;>
    split_ifs <;>
    (try rw [sqrt_five_eq_aureo]) <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P2_l2_le (i : Fin 4) (s : Fin 4 → Bool) :
    l2_120 (vertP2 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;>
    simp [l2_120, vertP2_apply] <;>
    split_ifs <;>
    (try rw [sqrt_five_eq_aureo]) <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P2_l3_le (i : Fin 4) (s : Fin 4 → Bool) :
    l3_120 (vertP2 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;>
    simp [l3_120, vertP2_apply] <;>
    split_ifs <;>
    (try rw [sqrt_five_eq_aureo]) <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P3_l1_le (i : Fin 4) (s : Fin 4 → Bool) :
    l1_120 (vertP3 i s) ≤ 6 + 6 * aureo := by
  fin_cases i <;> simp [l1_120, vertP3_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P3_l2_le (i : Fin 4) (s : Fin 4 → Bool) :
    l2_120 (vertP3 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;> simp [l2_120, vertP3_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P3_l3_le (i : Fin 4) (s : Fin 4 → Bool) :
    l3_120 (vertP3 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;> simp [l3_120, vertP3_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P4_l1_le (i : Fin 4) (s : Fin 4 → Bool) :
    l1_120 (vertP4 i s) ≤ 6 + 6 * aureo := by
  fin_cases i <;> simp [l1_120, vertP4_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P4_l2_le (i : Fin 4) (s : Fin 4 → Bool) :
    l2_120 (vertP4 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;> simp [l2_120, vertP4_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P4_l3_le (i : Fin 4) (s : Fin 4 → Bool) :
    l3_120 (vertP4 i s) ≤ 2 + 4 * aureo := by
  fin_cases i <;> simp [l3_120, vertP4_apply] <;> split_ifs <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_signed_le (s : Fin 3 → Bool) (k : Fin 4) :
    segnoZeroTesta s k * base5 k ≤ base5 k := by
  fin_cases k <;> simp [segnoZeroTesta, base5] <;> split_ifs <;>
    nlinarith [aureo_bounds.1, aureo_bounds.2]

private theorem perm_symm_ne (sigma : alternatingGroup (Fin 4))
    {i j : Fin 4} (hij : i ≠ j) :
    (sigma : Equiv.Perm (Fin 4)).symm i ≠
      (sigma : Equiv.Perm (Fin 4)).symm j :=
  (sigma : Equiv.Perm (Fin 4)).symm.injective.ne hij

private theorem alternating_inverse_cases (sigma : alternatingGroup (Fin 4)) :
    let p := (sigma : Equiv.Perm (Fin 4)).symm
    (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2 ∧ p 3 = 3) ∨
    (p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 3 ∧ p 3 = 1) ∨
    (p 0 = 0 ∧ p 1 = 3 ∧ p 2 = 1 ∧ p 3 = 2) ∨
    (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 3 ∧ p 3 = 2) ∨
    (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0 ∧ p 3 = 3) ∨
    (p 0 = 1 ∧ p 1 = 3 ∧ p 2 = 2 ∧ p 3 = 0) ∨
    (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1 ∧ p 3 = 3) ∨
    (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 3 ∧ p 3 = 0) ∨
    (p 0 = 2 ∧ p 1 = 3 ∧ p 2 = 0 ∧ p 3 = 1) ∨
    (p 0 = 3 ∧ p 1 = 0 ∧ p 2 = 2 ∧ p 3 = 1) ∨
    (p 0 = 3 ∧ p 1 = 1 ∧ p 2 = 0 ∧ p 3 = 2) ∨
    (p 0 = 3 ∧ p 1 = 2 ∧ p 2 = 1 ∧ p 3 = 0) := by
  classical
  fin_cases sigma <;> decide

private theorem P5_l1_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l1_120 (vertP5 sigma s) ≤ 6 + 6 * aureo := by
  generalize hk0 : ((sigma : Equiv.Perm (Fin 4)).symm 0) = k0
  generalize hk1 : ((sigma : Equiv.Perm (Fin 4)).symm 1) = k1
  generalize hk3 : ((sigma : Equiv.Perm (Fin 4)).symm 3) = k3
  have h01 : k0 ≠ k1 := by
    intro h
    have := (sigma : Equiv.Perm (Fin 4)).symm.injective (hk0.trans (h.trans hk1.symm))
    norm_num at this
  have h03 : k0 ≠ k3 := by
    intro h
    have := (sigma : Equiv.Perm (Fin 4)).symm.injective (hk0.trans (h.trans hk3.symm))
    omega
  have h13 : k1 ≠ k3 := by
    intro h
    have := (sigma : Equiv.Perm (Fin 4)).symm.injective (hk1.trans (h.trans hk3.symm))
    omega
  have hc0 : 0 ≤ 2 + aureo := by linarith [aureo_bounds.1]
  have hc1 : 0 ≤ 1 + 2 * aureo := by linarith [aureo_bounds.1]
  have hc3 : 0 ≤ aureo - 1 := by linarith [aureo_bounds.1]
  simp [l1_120, vertP5_apply]
  rw [hk0, hk1, hk3]
  calc
    (2 + aureo) * (segnoZeroTesta s k0 * base5 k0) +
          (1 + 2 * aureo) * (segnoZeroTesta s k1 * base5 k1) +
        (aureo - 1) * (segnoZeroTesta s k3 * base5 k3)
        ≤ (2 + aureo) * base5 k0 + (1 + 2 * aureo) * base5 k1 +
            (aureo - 1) * base5 k3 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P5_signed_le s k0) hc0)
              (mul_le_mul_of_nonneg_left (P5_signed_le s k1) hc1))
            (mul_le_mul_of_nonneg_left (P5_signed_le s k3) hc3)
    _ ≤ 6 + 6 * aureo := by
      fin_cases k0 <;> fin_cases k1 <;> fin_cases k3
      all_goals simp [base5] at h01 h03 h13 ⊢
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l2_120 (vertP5 sigma s) ≤ 2 + 4 * aureo := by
  generalize hk0 : ((sigma : Equiv.Perm (Fin 4)).symm 0) = k0
  generalize hk1 : ((sigma : Equiv.Perm (Fin 4)).symm 1) = k1
  have h01 : k0 ≠ k1 := by
    rw [← hk0, ← hk1]
    exact perm_symm_ne sigma (by omega)
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l2_120, vertP5_apply]
  rw [hk0, hk1]
  calc
    aureo * (segnoZeroTesta s k0 * base5 k0) +
        (aureo + 1) * (segnoZeroTesta s k1 * base5 k1)
        ≤ aureo * base5 k0 + (aureo + 1) * base5 k1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (P5_signed_le s k0) hc0)
        (mul_le_mul_of_nonneg_left (P5_signed_le s k1) hc1)
    _ ≤ 2 + 4 * aureo := by
      fin_cases k0 <;> fin_cases k1
      all_goals simp [base5] at h01 ⊢
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l3_120 (vertP5 sigma s) ≤ 2 + 4 * aureo := by
  generalize hk0 : ((sigma : Equiv.Perm (Fin 4)).symm 0) = k0
  generalize hk1 : ((sigma : Equiv.Perm (Fin 4)).symm 1) = k1
  generalize hk2 : ((sigma : Equiv.Perm (Fin 4)).symm 2) = k2
  have h01 : k0 ≠ k1 := by
    rw [← hk0, ← hk1]
    exact perm_symm_ne sigma (by omega)
  have h02 : k0 ≠ k2 := by
    rw [← hk0, ← hk2]
    exact perm_symm_ne sigma (by omega)
  have h12 : k1 ≠ k2 := by
    rw [← hk1, ← hk2]
    exact perm_symm_ne sigma (by omega)
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l3_120, vertP5_apply]
  rw [hk0, hk1, hk2]
  calc
    aureo * (segnoZeroTesta s k0 * base5 k0) +
          (aureo + 1) * (segnoZeroTesta s k1 * base5 k1) +
        segnoZeroTesta s k2 * base5 k2
        ≤ aureo * base5 k0 + (aureo + 1) * base5 k1 + base5 k2 := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P5_signed_le s k0) hc0)
              (mul_le_mul_of_nonneg_left (P5_signed_le s k1) hc1))
            (P5_signed_le s k2)
    _ ≤ 2 + 4 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals rw [← hk0, ← hk1, ← hk2]
      all_goals simp [h0, h1, h2, base5]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_signed_le (s : Fin 3 → Bool) (k : Fin 4) :
    segnoZeroTesta s k * base6 k ≤ base6 k := by
  fin_cases k <;> simp [segnoZeroTesta, base6] <;> split_ifs <;>
    nlinarith [aureo_bounds.1, aureo_bounds.2, Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 5)]

private theorem P6_l1_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l1_120 (vertP6 sigma s) ≤ 6 + 6 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ 2 + aureo := by linarith [aureo_bounds.1]
  have hc1 : 0 ≤ 1 + 2 * aureo := by linarith [aureo_bounds.1]
  have hc3 : 0 ≤ aureo - 1 := by linarith [aureo_bounds.1]
  simp [l1_120, vertP6_apply]
  calc
    (2 + aureo) * (segnoZeroTesta s (p 0) * base6 (p 0)) +
          (1 + 2 * aureo) * (segnoZeroTesta s (p 1) * base6 (p 1)) +
        (aureo - 1) * (segnoZeroTesta s (p 3) * base6 (p 3))
        ≤ (2 + aureo) * base6 (p 0) + (1 + 2 * aureo) * base6 (p 1) +
            (aureo - 1) * base6 (p 3) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P6_signed_le s (p 0)) hc0)
              (mul_le_mul_of_nonneg_left (P6_signed_le s (p 1)) hc1))
            (mul_le_mul_of_nonneg_left (P6_signed_le s (p 3)) hc3)
    _ ≤ 6 + 6 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base6, sqrt_five_eq_aureo]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l2_120 (vertP6 sigma s) ≤ 2 + 4 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l2_120, vertP6_apply]
  calc
    aureo * (segnoZeroTesta s (p 0) * base6 (p 0)) +
        (aureo + 1) * (segnoZeroTesta s (p 1) * base6 (p 1))
        ≤ aureo * base6 (p 0) + (aureo + 1) * base6 (p 1) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (P6_signed_le s (p 0)) hc0)
        (mul_le_mul_of_nonneg_left (P6_signed_le s (p 1)) hc1)
    _ ≤ 2 + 4 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base6, sqrt_five_eq_aureo]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : l3_120 (vertP6 sigma s) ≤ 2 + 4 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l3_120, vertP6_apply]
  calc
    aureo * (segnoZeroTesta s (p 0) * base6 (p 0)) +
          (aureo + 1) * (segnoZeroTesta s (p 1) * base6 (p 1)) +
        segnoZeroTesta s (p 2) * base6 (p 2)
        ≤ aureo * base6 (p 0) + (aureo + 1) * base6 (p 1) + base6 (p 2) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P6_signed_le s (p 0)) hc0)
              (mul_le_mul_of_nonneg_left (P6_signed_le s (p 1)) hc1))
            (P6_signed_le s (p 2))
    _ ≤ 2 + 4 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base6, sqrt_five_eq_aureo]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_signed_le (s : Fin 4 → Bool) (k : Fin 4) :
    segnoPieno s k * base7 k ≤ base7 k := by
  fin_cases k <;> simp [segnoPieno, base7] <;> split_ifs <;>
    nlinarith [aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : l1_120 (vertP7 sigma s) ≤ 6 + 6 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ 2 + aureo := by linarith [aureo_bounds.1]
  have hc1 : 0 ≤ 1 + 2 * aureo := by linarith [aureo_bounds.1]
  have hc3 : 0 ≤ aureo - 1 := by linarith [aureo_bounds.1]
  simp [l1_120, vertP7_apply]
  calc
    (2 + aureo) * (segnoPieno s (p 0) * base7 (p 0)) +
          (1 + 2 * aureo) * (segnoPieno s (p 1) * base7 (p 1)) +
        (aureo - 1) * (segnoPieno s (p 3) * base7 (p 3))
        ≤ (2 + aureo) * base7 (p 0) + (1 + 2 * aureo) * base7 (p 1) +
            (aureo - 1) * base7 (p 3) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P7_signed_le s (p 0)) hc0)
              (mul_le_mul_of_nonneg_left (P7_signed_le s (p 1)) hc1))
            (mul_le_mul_of_nonneg_left (P7_signed_le s (p 3)) hc3)
    _ ≤ 6 + 6 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base7]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : l2_120 (vertP7 sigma s) ≤ 2 + 4 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l2_120, vertP7_apply]
  calc
    aureo * (segnoPieno s (p 0) * base7 (p 0)) +
        (aureo + 1) * (segnoPieno s (p 1) * base7 (p 1))
        ≤ aureo * base7 (p 0) + (aureo + 1) * base7 (p 1) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (P7_signed_le s (p 0)) hc0)
        (mul_le_mul_of_nonneg_left (P7_signed_le s (p 1)) hc1)
    _ ≤ 2 + 4 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base7]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_le (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : l3_120 (vertP7 sigma s) ≤ 2 + 4 * aureo := by
  let p := (sigma : Equiv.Perm (Fin 4)).symm
  have hc0 : 0 ≤ aureo := le_of_lt aureo_pos
  have hc1 : 0 ≤ aureo + 1 := by linarith [aureo_pos]
  simp [l3_120, vertP7_apply]
  calc
    aureo * (segnoPieno s (p 0) * base7 (p 0)) +
          (aureo + 1) * (segnoPieno s (p 1) * base7 (p 1)) +
        segnoPieno s (p 2) * base7 (p 2)
        ≤ aureo * base7 (p 0) + (aureo + 1) * base7 (p 1) + base7 (p 2) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (P7_signed_le s (p 0)) hc0)
              (mul_le_mul_of_nonneg_left (P7_signed_le s (p 1)) hc1))
            (P7_signed_le s (p 2))
    _ ≤ 2 + 4 * aureo := by
      rcases alternating_inverse_cases sigma with h | h | h | h | h | h |
        h | h | h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2, h3⟩
      all_goals simp [p, h0, h1, h2, h3, base7]
      all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P1_l1_le (c : CodiceVentiquattro) :
    l1_120 (vertP1 c) ≤ 6 + 6 * aureo := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l1_120, vertP1,
    vertVentiquattro, segnoVentiquattro, indicePrimoVentiquattro,
    indiceSecondoVentiquattro, segnoPrimoVentiquattro,
    segnoSecondoVentiquattro, Fin.ext_iff]
  all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P1_l2_le (c : CodiceVentiquattro) :
    l2_120 (vertP1 c) ≤ 2 + 4 * aureo := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l2_120, vertP1,
    vertVentiquattro, segnoVentiquattro, indicePrimoVentiquattro,
    indiceSecondoVentiquattro, segnoPrimoVentiquattro,
    segnoSecondoVentiquattro, Fin.ext_iff]
  all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P1_l3_le (c : CodiceVentiquattro) :
    l3_120 (vertP1 c) ≤ 2 + 4 * aureo := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l3_120, vertP1,
    vertVentiquattro, segnoVentiquattro, indicePrimoVentiquattro,
    indiceSecondoVentiquattro, segnoPrimoVentiquattro,
    segnoSecondoVentiquattro, Fin.ext_iff]
  all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem l0_eq_inner_v0 (x : E4) : l0_120 x = ⟪x, v0_120⟫ := by
  rw [PiLp.inner_apply, Fin.sum_univ_four]
  simp [l0_120, v0_120, vertP1, vertVentiquattro,
    segnoVentiquattro, Fin.ext_iff]

private theorem l0_vertex_le {v : E4} (hv : v ∈ centoventiVertici) :
    l0_120 v ≤ 8 := by
  have hvnorm := norm_sq_mem_centoventiVertici hv
  have hv0norm : ‖v0_120‖ ^ 2 = 8 := by
    exact norm_sq_vertP1 (codiceVentiquattro 0 1 (by omega) true true)
  have hnonneg : 0 ≤ ‖v - v0_120‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, hvnorm, hv0norm, ← l0_eq_inner_v0] at hnonneg
  linarith

private theorem l0_vertex_eq_imp {v : E4} (hv : v ∈ centoventiVertici)
    (h : l0_120 v = 8) : v = v0_120 := by
  have hvnorm := norm_sq_mem_centoventiVertici hv
  have hv0norm : ‖v0_120‖ ^ 2 = 8 := by
    exact norm_sq_vertP1 (codiceVentiquattro 0 1 (by omega) true true)
  have hzero : ‖v - v0_120‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hvnorm, hv0norm, ← l0_eq_inner_v0, h]
    norm_num
  have hn : ‖v - v0_120‖ = 0 := (sq_eq_zero_iff).mp hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

private theorem l123_vertex_le {v : E4} (hv : v ∈ centoventiVertici) :
    l1_120 v ≤ 6 + 6 * aureo ∧
      l2_120 v ≤ 2 + 4 * aureo ∧
      l3_120 v ≤ 2 + 4 * aureo := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
    ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact ⟨P1_l1_le c, P1_l2_le c, P1_l3_le c⟩
  · exact ⟨P2_l1_le p.1 p.2, P2_l2_le p.1 p.2, P2_l3_le p.1 p.2⟩
  · exact ⟨P3_l1_le p.1 p.2, P3_l2_le p.1 p.2, P3_l3_le p.1 p.2⟩
  · exact ⟨P4_l1_le p.1 p.2, P4_l2_le p.1 p.2, P4_l3_le p.1 p.2⟩
  · exact ⟨P5_l1_le p.1 p.2, P5_l2_le p.1 p.2, P5_l3_le p.1 p.2⟩
  · exact ⟨P6_l1_le p.1 p.2, P6_l2_le p.1 p.2, P6_l3_le p.1 p.2⟩
  · exact ⟨P7_l1_le p.1 p.2, P7_l2_le p.1 p.2, P7_l3_le p.1 p.2⟩

private theorem li_toSet_le :
    (∀ x ∈ centoventi.toSet, l0_120 x ≤ 8) ∧
      (∀ x ∈ centoventi.toSet, l1_120 x ≤ 6 + 6 * aureo) ∧
      (∀ x ∈ centoventi.toSet, l2_120 x ≤ 2 + 4 * aureo) ∧
      (∀ x ∈ centoventi.toSet, l3_120 x ≤ 2 + 4 * aureo) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply le_su_toSet <;> intro v hv
  all_goals
    have hv' : v ∈ centoventiVertici := by exact_mod_cast hv
  · exact l0_vertex_le hv'
  · exact (l123_vertex_le hv').1
  · exact (l123_vertex_le hv').2.1
  · exact (l123_vertex_le hv').2.2

private theorem cellVertex_mem_generatoriF3 (i : Fin 20) :
    cellVertex120 i ∈ generatoriF3_120 := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

private theorem P2_l1_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l1_120 (vertP2 i s) = 6 + 6 * aureo) : False := by
  fin_cases i <;> simp [l1_120, vertP2_apply] at h <;>
    split_ifs at h <;> (try rw [sqrt_five_eq_aureo] at h) <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P2_l2_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l2_120 (vertP2 i s) = 2 + 4 * aureo) : False := by
  fin_cases i <;> simp [l2_120, vertP2_apply] at h <;>
    split_ifs at h <;> (try rw [sqrt_five_eq_aureo] at h) <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P2_l3_eq_cell (i : Fin 4) (s : Fin 4 → Bool)
    (h : l3_120 (vertP2 i s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP2 i s = cellVertex120 k := by
  fin_cases i <;> simp [l3_120, vertP2_apply] at h <;>
    split_ifs at h <;> (try rw [sqrt_five_eq_aureo] at h) <;>
    try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs3 : s 3 = true
  · refine ⟨1, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP2_apply]
  · refine ⟨2, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP2_apply]

private theorem P3_l1_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l1_120 (vertP3 i s) = 6 + 6 * aureo) : False := by
  fin_cases i <;> simp [l1_120, vertP3_apply] at h <;>
    split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P3_l2_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l2_120 (vertP3 i s) = 2 + 4 * aureo) : False := by
  fin_cases i <;> simp [l2_120, vertP3_apply] at h <;>
    split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P3_l3_eq_cell (i : Fin 4) (s : Fin 4 → Bool)
    (h : l3_120 (vertP3 i s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP3 i s = cellVertex120 k := by
  fin_cases i <;> simp [l3_120, vertP3_apply] at h <;>
    split_ifs at h <;>
    try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs3 : s 3 = true
  · refine ⟨3, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP3_apply]
  · refine ⟨4, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP3_apply]

private theorem P4_l1_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l1_120 (vertP4 i s) = 6 + 6 * aureo) : False := by
  fin_cases i <;> simp [l1_120, vertP4_apply] at h <;>
    split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P4_l2_ne (i : Fin 4) (s : Fin 4 → Bool)
    (h : l2_120 (vertP4 i s) = 2 + 4 * aureo) : False := by
  fin_cases i <;> simp [l2_120, vertP4_apply] at h <;>
    split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P4_l3_eq_cell (i : Fin 4) (s : Fin 4 → Bool)
    (h : l3_120 (vertP4 i s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP4 i s = cellVertex120 k := by
  fin_cases i <;> simp [l3_120, vertP4_apply] at h <;>
    split_ifs at h <;>
    try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs3 : s 3 = true
  · refine ⟨5, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP4_apply]
  · refine ⟨6, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, vertP4_apply]

private theorem P1_l1_eq_v0 (c : CodiceVentiquattro)
    (h : l1_120 (vertP1 c) = 6 + 6 * aureo) : vertP1 c = v0_120 := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l1_120, vertP1, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals simp [v0_120, vertP1, vertVentiquattro,
    segnoVentiquattro, Fin.ext_iff]

private theorem P1_l2_eq_v0 (c : CodiceVentiquattro)
    (h : l2_120 (vertP1 c) = 2 + 4 * aureo) : vertP1 c = v0_120 := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l2_120, vertP1, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals simp [v0_120, vertP1, vertVentiquattro,
    segnoVentiquattro, Fin.ext_iff]

private theorem P1_l3_eq_v0 (c : CodiceVentiquattro)
    (h : l3_120 (vertP1 c) = 2 + 4 * aureo) : vertP1 c = v0_120 := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j <;> cases si <;> cases sj
  all_goals norm_num at hij
  all_goals simp [l3_120, vertP1, vertVentiquattro, segnoVentiquattro,
    indicePrimoVentiquattro, indiceSecondoVentiquattro,
    segnoPrimoVentiquattro, segnoSecondoVentiquattro, Fin.ext_iff] at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals simp [v0_120, vertP1, vertVentiquattro,
    segnoVentiquattro, Fin.ext_iff]

private theorem P5_l1_ne_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l1_ne (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l1_120 (vertP5 sigma s) = 6 + 6 * aureo) : False := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P5_l1_ne_0123 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_0231 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_0312 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_1032 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_1203 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_1320 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_2013 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_2130 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_2301 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_3021 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_3102 sigma s h0 h1 h2 h3 h
    | exact P5_l1_ne_3210 sigma s h0 h1 h2 h3 h

private theorem P5_l2_eq_pair_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · left
    ext j
    fin_cases j <;> simp_all [p4_120, sigmaA, vertP5_apply,
      base5, segnoZeroTesta]
  · right
    ext j
    fin_cases j <;> simp_all [p5_120, sigmaA, vertP5_apply,
      base5, segnoZeroTesta]

private theorem P5_l2_eq_pair_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  exfalso
  simp [l2_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l2_eq_pair (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l2_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    vertP5 sigma s = p4_120 ∨ vertP5 sigma s = p5_120 := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P5_l2_eq_pair_0123 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_0231 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_0312 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_1032 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_1203 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_1320 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_2013 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_2130 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_2301 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_3021 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_3102 sigma s h0 h1 h2 h3 h
    | exact P5_l2_eq_pair_3210 sigma s h0 h1 h2 h3 h

private theorem P5_l3_eq_cell_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals refine ⟨9, ?_⟩
  all_goals ext j
  all_goals fin_cases j <;> simp_all [cellVertex120, sigmaB,
    vertP5_apply, base5, segnoZeroTesta]

private theorem P5_l3_eq_cell_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · refine ⟨7, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, p4_120, sigmaA,
      vertP5_apply, base5, segnoZeroTesta]
  · refine ⟨8, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, p5_120, sigmaA,
      vertP5_apply, base5, segnoZeroTesta]

private theorem P5_l3_eq_cell_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP5_apply, h0, h1, h2, h3,
    base5, segnoZeroTesta] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P5_l3_eq_cell (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l3_120 (vertP5 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP5 sigma s = cellVertex120 k := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P5_l3_eq_cell_0123 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_0231 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_0312 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_1032 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_1203 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_1320 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_2013 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_2130 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_2301 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_3021 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_3102 sigma s h0 h1 h2 h3 h
    | exact P5_l3_eq_cell_3210 sigma s h0 h1 h2 h3 h
private theorem P6_l1_eq_w0_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals ext j
  all_goals fin_cases j <;> simp_all [w0_120, sigmaA, vertP6_apply,
    base6, segnoZeroTesta, sqrt_five_eq_aureo]

private theorem P6_l1_eq_w0_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) : vertP6 sigma s = w0_120 := by
  exfalso
  simp [l1_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l1_eq_w0 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l1_120 (vertP6 sigma s) = 6 + 6 * aureo) :
    vertP6 sigma s = w0_120 := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P6_l1_eq_w0_0123 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_0231 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_0312 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_1032 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_1203 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_1320 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_2013 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_2130 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_2301 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_3021 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_3102 sigma s h0 h1 h2 h3 h
    | exact P6_l1_eq_w0_3210 sigma s h0 h1 h2 h3 h

private theorem P6_l2_eq_pair_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · left
    ext j
    fin_cases j <;> simp_all [w0_120, sigmaA, vertP6_apply,
      base6, segnoZeroTesta, sqrt_five_eq_aureo]
  · right
    ext j
    fin_cases j <;> simp_all [w1_120, sigmaA, vertP6_apply,
      base6, segnoZeroTesta, sqrt_five_eq_aureo]

private theorem P6_l2_eq_pair_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) : vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  exfalso
  simp [l2_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l2_eq_pair (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l2_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    vertP6 sigma s = w0_120 ∨ vertP6 sigma s = w1_120 := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P6_l2_eq_pair_0123 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_0231 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_0312 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_1032 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_1203 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_1320 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_2013 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_2130 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_2301 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_3021 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_3102 sigma s h0 h1 h2 h3 h
    | exact P6_l2_eq_pair_3210 sigma s h0 h1 h2 h3 h

private theorem P6_l3_eq_cell_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals refine ⟨12, ?_⟩
  all_goals ext j
  all_goals fin_cases j <;> simp_all [cellVertex120, sigmaB,
    vertP6_apply, base6, segnoZeroTesta, sqrt_five_eq_aureo]

private theorem P6_l3_eq_cell_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · refine ⟨10, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, w0_120, sigmaA,
      vertP6_apply, base6, segnoZeroTesta, sqrt_five_eq_aureo]
  · refine ⟨11, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, w1_120, sigmaA,
      vertP6_apply, base6, segnoZeroTesta, sqrt_five_eq_aureo]

private theorem P6_l3_eq_cell_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P6_l3_eq_cell_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  simp [l3_120, vertP6_apply, h0, h1, h2, h3,
    base6, segnoZeroTesta, sqrt_five_eq_aureo] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals refine ⟨13, ?_⟩
  all_goals ext j
  all_goals fin_cases j <;> simp_all [cellVertex120, w2_120, sigmaC,
    vertP6_apply, base6, segnoZeroTesta, sqrt_five_eq_aureo]

private theorem P6_l3_eq_cell (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (h : l3_120 (vertP6 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP6 sigma s = cellVertex120 k := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P6_l3_eq_cell_0123 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_0231 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_0312 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_1032 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_1203 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_1320 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_2013 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_2130 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_2301 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_3021 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_3102 sigma s h0 h1 h2 h3 h
    | exact P6_l3_eq_cell_3210 sigma s h0 h1 h2 h3 h

private theorem P7_l1_ne_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  simp [l1_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l1_ne (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) (h : l1_120 (vertP7 sigma s) = 6 + 6 * aureo) : False := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P7_l1_ne_0123 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_0231 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_0312 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_1032 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_1203 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_1320 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_2013 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_2130 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_2301 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_3021 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_3102 sigma s h0 h1 h2 h3 h
    | exact P7_l1_ne_3210 sigma s h0 h1 h2 h3 h

private theorem P7_l2_ne_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  simp [l2_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l2_ne (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) (h : l2_120 (vertP7 sigma s) = 2 + 4 * aureo) : False := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P7_l2_ne_0123 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_0231 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_0312 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_1032 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_1203 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_1320 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_2013 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_2130 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_2301 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_3021 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_3102 sigma s h0 h1 h2 h3 h
    | exact P7_l2_ne_3210 sigma s h0 h1 h2 h3 h

private theorem P7_l3_eq_cell_0123 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_0231 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_0312 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 0)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_1032 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_1203 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_1320 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 1)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · refine ⟨16, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaB,
      vertP7_apply, base7, segnoPieno]
  · refine ⟨17, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaB,
      vertP7_apply, base7, segnoPieno]

private theorem P7_l3_eq_cell_2013 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 3)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_2130 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 3)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_2301 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 2)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 3)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs1 : s 1 = true
  · refine ⟨14, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaA,
      vertP7_apply, base7, segnoPieno]
  · refine ⟨15, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaA,
      vertP7_apply, base7, segnoPieno]

private theorem P7_l3_eq_cell_3021 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 0)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 2)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 1)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_3102 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 1)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 0)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 2)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  exfalso
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]

private theorem P7_l3_eq_cell_3210 (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool)
    (h0 : (sigma : Equiv.Perm (Fin 4)).symm 0 = 3)
    (h1 : (sigma : Equiv.Perm (Fin 4)).symm 1 = 2)
    (h2 : (sigma : Equiv.Perm (Fin 4)).symm 2 = 1)
    (h3 : (sigma : Equiv.Perm (Fin 4)).symm 3 = 0)
    (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  simp [l3_120, vertP7_apply, h0, h1, h2, h3,
    base7, segnoPieno] at h
  split_ifs at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals by_cases hs0 : s 0 = true
  · refine ⟨18, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaC,
      vertP7_apply, base7, segnoPieno]
  · refine ⟨19, ?_⟩
    ext j
    fin_cases j <;> simp_all [cellVertex120, sigmaC,
      vertP7_apply, base7, segnoPieno]

private theorem P7_l3_eq_cell (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) (h : l3_120 (vertP7 sigma s) = 2 + 4 * aureo) :
    ∃ k : Fin 20, vertP7 sigma s = cellVertex120 k := by
  rcases alternating_inverse_cases sigma with hp | hp | hp | hp | hp | hp |
    hp | hp | hp | hp | hp | hp
  all_goals rcases hp with ⟨h0, h1, h2, h3⟩
  all_goals first
    | exact P7_l3_eq_cell_0123 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_0231 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_0312 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_1032 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_1203 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_1320 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_2013 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_2130 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_2301 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_3021 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_3102 sigma s h0 h1 h2 h3 h
    | exact P7_l3_eq_cell_3210 sigma s h0 h1 h2 h3 h

private theorem l1_vertex_eq_imp {v : E4} (hv : v ∈ centoventiVertici)
    (h : l1_120 v = 6 + 6 * aureo) : v = v0_120 ∨ v = w0_120 := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
    ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact Or.inl (P1_l1_eq_v0 c h)
  · exact (P2_l1_ne p.1 p.2 h).elim
  · exact (P3_l1_ne p.1 p.2 h).elim
  · exact (P4_l1_ne p.1 p.2 h).elim
  · exact (P5_l1_ne p.1 p.2 h).elim
  · exact Or.inr (P6_l1_eq_w0 p.1 p.2 h)
  · exact (P7_l1_ne p.1 p.2 h).elim

private theorem l2_vertex_eq_imp {v : E4} (hv : v ∈ centoventiVertici)
    (h : l2_120 v = 2 + 4 * aureo) :
    v = v0_120 ∨ v = w0_120 ∨ v = w1_120 ∨
      v = p4_120 ∨ v = p5_120 := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
    ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact Or.inl (P1_l2_eq_v0 c h)
  · exact (P2_l2_ne p.1 p.2 h).elim
  · exact (P3_l2_ne p.1 p.2 h).elim
  · exact (P4_l2_ne p.1 p.2 h).elim
  · rcases P5_l2_eq_pair p.1 p.2 h with hp | hp
    · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))
  · rcases P6_l2_eq_pair p.1 p.2 h with hp | hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))
  · exact (P7_l2_ne p.1 p.2 h).elim

private theorem l3_vertex_eq_imp {v : E4} (hv : v ∈ centoventiVertici)
    (h : l3_120 v = 2 + 4 * aureo) :
    ∃ k : Fin 20, v = cellVertex120 k := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
    ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · refine ⟨0, ?_⟩
    simpa [cellVertex120] using P1_l3_eq_v0 c h
  · exact P2_l3_eq_cell p.1 p.2 h
  · exact P3_l3_eq_cell p.1 p.2 h
  · exact P4_l3_eq_cell p.1 p.2 h
  · exact P5_l3_eq_cell p.1 p.2 h
  · exact P6_l3_eq_cell p.1 p.2 h
  · exact P7_l3_eq_cell p.1 p.2 h

private theorem argmax_l0_120 :
    {x ∈ (centoventiVertici : Set E4) | l0_120 x = 8} =
      (generatoriF0_120 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ centoventiVertici := by exact_mod_cast hx
    have h := l0_vertex_eq_imp hx' hl
    subst x
    simp [generatoriF0_120]
  · intro hx
    have h : x = v0_120 := by simpa [generatoriF0_120] using hx
    subst x
    exact ⟨by exact_mod_cast vertP1_mem120 _, fundamental_values.1⟩

private theorem argmax_l1_120 :
    {x ∈ (centoventiVertici : Set E4) | l1_120 x = 6 + 6 * aureo} =
      (generatoriF1_120 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ centoventiVertici := by exact_mod_cast hx
    rcases l1_vertex_eq_imp hx' hl with rfl | rfl <;>
      simp [generatoriF1_120]
  · intro hx
    have h : x = v0_120 ∨ x = w0_120 := by
      simpa [generatoriF1_120] using hx
    rcases h with rfl | rfl
    · exact ⟨by exact_mod_cast vertP1_mem120 _, fundamental_values.2.1.1⟩
    · exact ⟨by exact_mod_cast vertP6_mem120 _ _, fundamental_values.2.1.2⟩

private theorem argmax_l2_120 :
    {x ∈ (centoventiVertici : Set E4) | l2_120 x = 2 + 4 * aureo} =
      (generatoriF2_120 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ centoventiVertici := by exact_mod_cast hx
    rcases l2_vertex_eq_imp hx' hl with rfl | rfl | rfl | rfl | rfl <;>
      simp [generatoriF2_120]
  · intro hx
    have h : x = v0_120 ∨ x = w0_120 ∨ x = w1_120 ∨
        x = p4_120 ∨ x = p5_120 := by
      simpa [generatoriF2_120] using hx
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by exact_mod_cast vertP1_mem120 _, fundamental_values.2.2.1⟩
    · exact ⟨by exact_mod_cast vertP6_mem120 _ _, fundamental_values.2.2.2.1⟩
    · exact ⟨by exact_mod_cast vertP6_mem120 _ _, fundamental_values.2.2.2.2.1⟩
    · exact ⟨by exact_mod_cast vertP5_mem120 _ _, fundamental_values.2.2.2.2.2.1⟩
    · exact ⟨by exact_mod_cast vertP5_mem120 _ _, fundamental_values.2.2.2.2.2.2⟩

private theorem argmax_l3_120 :
    {x ∈ (centoventiVertici : Set E4) | l3_120 x = 2 + 4 * aureo} =
      (generatoriF3_120 : Set E4) := by
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ centoventiVertici := by exact_mod_cast hx
    obtain ⟨k, rfl⟩ := l3_vertex_eq_imp hx' hl
    exact_mod_cast cellVertex_mem_generatoriF3 k
  · intro hx
    have hx' : x ∈ generatoriF3_120 := by exact_mod_cast hx
    rcases Finset.mem_image.mp hx' with ⟨k, _, rfl⟩
    exact ⟨by exact_mod_cast cellVertex120_mem k, l3_cellVertex120 k⟩

private theorem isExposed_argmax_120 (s : Finset E4) (l : E4 →L[ℝ] ℝ)
    (c : ℝ) (hs : s.Nonempty)
    (harg : {x ∈ (centoventiVertici : Set E4) | l x = c} = (s : Set E4))
    (hle : ∀ x ∈ centoventi.toSet, l x ≤ c) :
    IsExposed ℝ centoventi.toSet (convexHull ℝ (s : Set E4)) := by
  intro _
  have hsV : (s : Set E4) ⊆ (centoventiVertici : Set E4) := by
    intro x hx
    rw [← harg] at hx
    exact hx.1
  have hsP : (s : Set E4) ⊆ centoventi.toSet := by
    intro x hx
    exact subset_convexHull ℝ _ (by exact_mod_cast hsV hx)
  have hsub : convexHull ℝ (s : Set E4) ⊆ centoventi.toSet :=
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
    have haP : a ∈ centoventi.toSet := hsP haS
    have hlx : l x = c := by
      apply le_antisymm (hle x hxP)
      simpa [heq a haS] using hxmax a haP
    have hxarg := faccia_argmax centoventiVertici l hxP hxmax
    have hset : {z ∈ (centoventiVertici : Set E4) | l z = l x} =
        (s : Set E4) := by simpa [hlx] using harg
    rwa [hset] at hxarg

theorem F0_120_isFace : centoventi.IsFace F0_120 := by
  refine ⟨?_, ⟨v0_120, subset_convexHull ℝ _ (by simp [generatoriF0_120])⟩⟩
  exact isExposed_argmax_120 generatoriF0_120 l0_120 8
    (by simp [generatoriF0_120]) argmax_l0_120 li_toSet_le.1

theorem F1_120_isFace : centoventi.IsFace F1_120 := by
  refine ⟨?_, ⟨v0_120, subset_convexHull ℝ _ (by simp [generatoriF1_120])⟩⟩
  exact isExposed_argmax_120 generatoriF1_120 l1_120 (6 + 6 * aureo)
    (by simp [generatoriF1_120]) argmax_l1_120 li_toSet_le.2.1

theorem F2_120_isFace : centoventi.IsFace F2_120 := by
  refine ⟨?_, ⟨v0_120, subset_convexHull ℝ _ (by simp [generatoriF2_120])⟩⟩
  exact isExposed_argmax_120 generatoriF2_120 l2_120 (2 + 4 * aureo)
    (by simp [generatoriF2_120]) argmax_l2_120 li_toSet_le.2.2.1

theorem F3_120_isFace : centoventi.IsFace F3_120 := by
  refine ⟨?_, ⟨v0_120, subset_convexHull ℝ _ (by
    exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 0))⟩⟩
  exact isExposed_argmax_120 generatoriF3_120 l3_120 (2 + 4 * aureo)
    (by
      refine ⟨v0_120, ?_⟩
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 0)
    argmax_l3_120 li_toSet_le.2.2.2

private def p3_120 : Fin 4 → E4 := ![v0_120, w0_120, w1_120, w2_120]

@[simp] private theorem p3_120_zero : p3_120 0 = v0_120 := rfl
@[simp] private theorem p3_120_one : p3_120 1 = w0_120 := rfl
@[simp] private theorem p3_120_two : p3_120 2 = w1_120 := rfl
@[simp] private theorem p3_120_three : p3_120 3 = w2_120 := rfl

private theorem v0_120_coords : v0_120 = ![(2 : ℝ), 2, 0, 0] := by
  ext i
  fin_cases i <;> norm_num [v0_120, vertP1, vertVentiquattro,
    segnoVentiquattro, Fin.ext_iff]

private theorem w0_120_coords :
    w0_120 = ![aureo, 2 * aureo - 1, 0, aureo - 1] := by
  ext i
  change segnoZeroTesta ![true, true, true] (permA.symm i) *
    base6 (permA.symm i) = _
  rw [permA_symm_apply]
  fin_cases i <;> simp [segnoZeroTesta, base6, sqrt_five_eq_aureo]

private theorem w1_120_coords :
    w1_120 = ![aureo, 2 * aureo - 1, 0, -(aureo - 1)] := by
  ext i
  change segnoZeroTesta ![false, true, true] (permA.symm i) *
    base6 (permA.symm i) = _
  rw [permA_symm_apply]
  fin_cases i <;> simp [segnoZeroTesta, base6, sqrt_five_eq_aureo]

private theorem w2_120_coords :
    w2_120 = ![2 * aureo - 1, aureo, aureo - 1, 0] := by
  ext i
  change segnoZeroTesta ![true, true, true] (permC.symm i) *
    base6 (permC.symm i) = _
  rw [permC_symm_apply]
  fin_cases i <;> simp [segnoZeroTesta, base6, sqrt_five_eq_aureo]

private theorem p3_120_affineIndependent : AffineIndependent ℝ p3_120 := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hc (j : Fin 4) := congrArg (fun x : E4 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hc
  have h0 := hc 0
  have h2 := hc 2
  have h3 := hc 3
  rw [Fin.sum_univ_four] at ha hb
  norm_num [v0_120_coords, w0_120_coords, w1_120_coords,
    w2_120_coords, Fin.sum_univ_four] at h0 h2 h3
  simp at h0 h2 h3
  have hsum : (a 0 - b 0) + (a 1 - b 1) +
      (a 2 - b 2) + (a 3 - b 3) = 0 := by
    linarith
  have hn2 : aureo - 1 ≠ 0 := by nlinarith [aureo_bounds.1]
  have e3 : a 3 = b 3 := by
    rcases h2 with h2 | h2
    · exact h2
    · exact (hn2 h2).elim
  have hfac3 : (aureo - 1) *
      ((a 1 - b 1) - (a 2 - b 2)) = 0 := by
    linear_combination h3
  have hd : (a 1 - b 1) - (a 2 - b 2) = 0 := by
    exact (mul_eq_zero.mp hfac3).resolve_left hn2
  rw [e3] at h0 hsum
  simp only [sub_self, add_zero] at h0 hsum
  have hfac0 : (2 - aureo) * (a 0 - b 0) = 0 := by
    linear_combination h0 - aureo * hsum
  have hn0 : 2 - aureo ≠ 0 := by nlinarith [aureo_bounds.2]
  have e0 : a 0 = b 0 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac0).resolve_left hn0)
  have e1 : a 1 = b 1 := by linarith
  have e2 : a 2 = b 2 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem faceDim_F0_120 : faceDim F0_120 = 0 := by
  rw [F0_120, generatoriF0_120]
  simpa using faceDim_singleton v0_120

private theorem v0_ne_w0_120 : v0_120 ≠ w0_120 := by
  intro h
  have hc := congrArg (fun x : E4 => x (0 : Fin 4)) h
  norm_num [v0_120_coords, w0_120_coords] at hc
  simp at hc
  nlinarith [aureo_bounds.2]

private theorem w1_ne_w0_120 : w1_120 ≠ w0_120 := by
  intro h
  have hc := congrArg (fun x : E4 => x (3 : Fin 4)) h
  norm_num [w0_120_coords, w1_120_coords] at hc
  simp at hc
  nlinarith [aureo_bounds.1]

private theorem w2_ne_w0_120 : w2_120 ≠ w0_120 := by
  intro h
  have hc := congrArg (fun x : E4 => x (2 : Fin 4)) h
  norm_num [w0_120_coords, w2_120_coords] at hc
  simp at hc
  nlinarith [aureo_bounds.1]

private theorem w2_ne_w1_120 : w2_120 ≠ w1_120 := by
  intro h
  have hc := congrArg (fun x : E4 => x (2 : Fin 4)) h
  norm_num [w1_120_coords, w2_120_coords] at hc
  simp at hc
  nlinarith [aureo_bounds.1]

theorem faceDim_F1_120 : faceDim F1_120 = 1 := by
  have hgen : (generatoriF1_120 : Set E4) = {v0_120, w0_120} := by
    ext x
    simp [generatoriF1_120]
  rw [F1_120, hgen, convexHull_pair]
  unfold faceDim
  rw [vectorSpan_segment]
  apply finrank_span_singleton
  exact vsub_ne_zero.mpr v0_ne_w0_120.symm

private theorem l1_eq_on_F1_120 {x : E4} (hx : x ∈ F1_120) :
    l1_120 x = 6 + 6 * aureo := by
  apply le_antisymm
    (li_toSet_le.2.1 x (F1_120_isFace.1.subset hx))
  rw [F1_120] at hx
  exact convexHull_min (fun y hy => by
      change 6 + 6 * aureo ≤ l1_120 y
      have hy' : y ∈ (generatoriF1_120 : Set E4) := hy
      rw [← argmax_l1_120] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l1_120.toLinearMap)
      (6 + 6 * aureo)) hx

private theorem l2_eq_on_F2_120 {x : E4} (hx : x ∈ F2_120) :
    l2_120 x = 2 + 4 * aureo := by
  apply le_antisymm
    (li_toSet_le.2.2.1 x (F2_120_isFace.1.subset hx))
  rw [F2_120] at hx
  exact convexHull_min (fun y hy => by
      change 2 + 4 * aureo ≤ l2_120 y
      have hy' : y ∈ (generatoriF2_120 : Set E4) := hy
      rw [← argmax_l2_120] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l2_120.toLinearMap)
      (2 + 4 * aureo)) hx

private theorem l3_eq_on_F3_120 {x : E4} (hx : x ∈ F3_120) :
    l3_120 x = 2 + 4 * aureo := by
  apply le_antisymm
    (li_toSet_le.2.2.2 x (F3_120_isFace.1.subset hx))
  rw [F3_120] at hx
  exact convexHull_min (fun y hy => by
      change 2 + 4 * aureo ≤ l3_120 y
      have hy' : y ∈ (generatoriF3_120 : Set E4) := hy
      rw [← argmax_l3_120] at hy'
      rw [hy'.2])
    (convex_halfSpace_ge (LinearMap.isLinear l3_120.toLinearMap)
      (2 + 4 * aureo)) hx

theorem F0_ssubset_F1_120 : F0_120 ⊂ F1_120 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx0 : x = v0_120 := by simpa [generatoriF0_120] using hx
    subst x
    simp [generatoriF1_120]
  · intro h
    have hd := faceDim_F0_120
    rw [h, faceDim_F1_120] at hd
    omega

theorem F1_ssubset_F2_120 : F1_120 ⊂ F2_120 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx01 : x = v0_120 ∨ x = w0_120 := by
      simpa [generatoriF1_120] using hx
    rcases hx01 with rfl | rfl <;> simp [generatoriF2_120]
  · intro heq
    have hw1F2 : w1_120 ∈ F2_120 :=
      subset_convexHull ℝ _ (by simp [generatoriF2_120])
    have hw1F1 : w1_120 ∈ F1_120 := by rwa [heq]
    have hl := l1_eq_on_F1_120 hw1F1
    exact w1_ne_w0_120 (P6_l1_eq_w0 sigmaA ![false, true, true] hl)

private theorem generatorsF2_subset_generatorsF3 :
    (generatoriF2_120 : Set E4) ⊆ (generatoriF3_120 : Set E4) := by
  intro x hx
  have hcases : x = v0_120 ∨ x = w0_120 ∨ x = w1_120 ∨
      x = p4_120 ∨ x = p5_120 := by
    simpa [generatoriF2_120] using hx
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 0)
  · exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 10)
  · exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 11)
  · exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 7)
  · exact_mod_cast (by
      simpa [cellVertex120] using cellVertex_mem_generatoriF3 8)

theorem F2_ssubset_F3_120 : F2_120 ⊂ F3_120 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · exact convexHull_mono generatorsF2_subset_generatorsF3
  · intro heq
    have hw2F3 : w2_120 ∈ F3_120 :=
      subset_convexHull ℝ _ (by
        exact_mod_cast (by
          simpa [cellVertex120] using cellVertex_mem_generatoriF3 13))
    have hw2F2 : w2_120 ∈ F2_120 := by rwa [heq]
    have hl := l2_eq_on_F2_120 hw2F2
    rcases P6_l2_eq_pair sigmaC ![true, true, true] hl with hw | hw
    · exact w2_ne_w0_120 hw
    · exact w2_ne_w1_120 hw

private theorem span_F3_le_ker_l3_120 :
    vectorSpan ℝ F3_120 ≤ LinearMap.ker l3_120.toLinearMap := by
  show Submodule.span ℝ (F3_120 -ᵥ F3_120) ≤ _
  rw [Submodule.span_le]
  rintro d ⟨x, hx, y, hy, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  change l3_120 (x - y) = 0
  rw [map_sub, l3_eq_on_F3_120 hx, l3_eq_on_F3_120 hy, sub_self]

private theorem finrank_ker_l3_120 :
    Module.finrank ℝ (LinearMap.ker l3_120.toLinearMap) = 3 := by
  have hsurj : Function.Surjective l3_120.toLinearMap := by
    intro t
    refine ⟨t • EuclideanSpace.single (2 : Fin 4) 1, ?_⟩
    norm_num [l3_120, Fin.ext_iff]
  have hr := LinearMap.finrank_range_add_finrank_ker l3_120.toLinearMap
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  have hE : Module.finrank ℝ E4 = 4 := by
    simp [E4, finrank_euclideanSpace]
  have hR : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  omega

theorem faceDim_F3_120 : faceDim F3_120 = 3 := by
  unfold faceDim
  apply le_antisymm
  · calc
      Module.finrank ℝ (vectorSpan ℝ F3_120) ≤
          Module.finrank ℝ (LinearMap.ker l3_120.toLinearMap) :=
        Submodule.finrank_mono span_F3_le_ker_l3_120
      _ = 3 := finrank_ker_l3_120
  · have hsub : vectorSpan ℝ (Set.range p3_120) ≤ vectorSpan ℝ F3_120 := by
      apply vectorSpan_mono ℝ
      rintro x ⟨i, rfl⟩
      apply subset_convexHull ℝ _
      fin_cases i
      · exact_mod_cast (by
          simpa [p3_120, cellVertex120] using cellVertex_mem_generatoriF3 0)
      · exact_mod_cast (by
          simpa [p3_120, cellVertex120] using cellVertex_mem_generatoriF3 10)
      · exact_mod_cast (by
          simpa [p3_120, cellVertex120] using cellVertex_mem_generatoriF3 11)
      · exact_mod_cast (by
          simpa [p3_120, cellVertex120] using cellVertex_mem_generatoriF3 13)
    calc
      3 = Module.finrank ℝ (vectorSpan ℝ (Set.range p3_120)) :=
        (p3_120_affineIndependent.finrank_vectorSpan (by simp)).symm
      _ ≤ Module.finrank ℝ (vectorSpan ℝ F3_120) :=
        Submodule.finrank_mono hsub

theorem faceDim_F2_120 : faceDim F2_120 = 2 := by
  have hlo := faceDim_lt_of_ssubset centoventi
    F1_120_isFace F2_120_isFace F1_ssubset_F2_120
  have hhi := faceDim_lt_of_ssubset centoventi
    F2_120_isFace F3_120_isFace F2_ssubset_F3_120
  rw [faceDim_F1_120] at hlo
  rw [faceDim_F3_120] at hhi
  omega

/-- La bandiera fondamentale del 120-cell.-/
def centoventiFlag : centoventi.Flag where
  face i := ![F0_120, F1_120, F2_120, F3_120] i
  isFace i := by
    fin_cases i
    · exact F0_120_isFace
    · exact F1_120_isFace
    · exact F2_120_isFace
    · exact F3_120_isFace
  dim_eq i := by
    fin_cases i
    · exact faceDim_F0_120
    · exact faceDim_F1_120
    · exact faceDim_F2_120
    · exact faceDim_F3_120
  strict_mono i j hij := by
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    · exact F0_ssubset_F1_120
    · exact F0_ssubset_F1_120.trans F1_ssubset_F2_120
    · exact F0_ssubset_F1_120.trans
        (F1_ssubset_F2_120.trans F2_ssubset_F3_120)
    · exact F1_ssubset_F2_120
    · exact F1_ssubset_F2_120.trans F2_ssubset_F3_120
    · exact F2_ssubset_F3_120

private def permEven0123 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 1
private def permEven0231 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2 * Equiv.swap 2 3
private def permEven0312 : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 2 * Equiv.swap 1 3
private def permEven1032 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3
private def permEven1203 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 2
private def permEven1320 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 3
private def permEven2013 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 2
private def permEven2130 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 2 3
private def permEven2301 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3
private def permEven3021 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 3
private def permEven3102 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 0 3
private def permEven3210 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3 * Equiv.swap 1 2

private theorem twoSwaps_mem_alternating {a b c d : Fin 4}
    (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 4) := by
  apply Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
  · rw [Equiv.Perm.swap_isSwap_iff]
    exact hab
  · rw [Equiv.Perm.swap_isSwap_iff]
    exact hcd

private def sigmaEven0123 : alternatingGroup (Fin 4) :=
  ⟨permEven0123, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven0231 : alternatingGroup (Fin 4) :=
  ⟨permEven0231, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven0312 : alternatingGroup (Fin 4) :=
  ⟨permEven0312, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven1032 : alternatingGroup (Fin 4) :=
  ⟨permEven1032, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven1203 : alternatingGroup (Fin 4) :=
  ⟨permEven1203, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven1320 : alternatingGroup (Fin 4) :=
  ⟨permEven1320, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven2013 : alternatingGroup (Fin 4) :=
  ⟨permEven2013, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven2130 : alternatingGroup (Fin 4) :=
  ⟨permEven2130, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven2301 : alternatingGroup (Fin 4) :=
  ⟨permEven2301, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven3021 : alternatingGroup (Fin 4) :=
  ⟨permEven3021, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven3102 : alternatingGroup (Fin 4) :=
  ⟨permEven3102, twoSwaps_mem_alternating (by decide) (by decide)⟩
private def sigmaEven3210 : alternatingGroup (Fin 4) :=
  ⟨permEven3210, twoSwaps_mem_alternating (by decide) (by decide)⟩

private theorem alternating_eq_cases (sigma : alternatingGroup (Fin 4)) :
    sigma = sigmaEven0123 ∨ sigma = sigmaEven0231 ∨
    sigma = sigmaEven0312 ∨ sigma = sigmaEven1032 ∨
    sigma = sigmaEven1203 ∨ sigma = sigmaEven1320 ∨
    sigma = sigmaEven2013 ∨ sigma = sigmaEven2130 ∨
    sigma = sigmaEven2301 ∨ sigma = sigmaEven3021 ∨
    sigma = sigmaEven3102 ∨ sigma = sigmaEven3210 := by
  fin_cases sigma <;> decide

private inductive VertexCode120 where
  | p1 (c : CodiceVentiquattro)
  | p2 (i : Fin 4) (s : Fin 4 → Bool)
  | p3 (i : Fin 4) (s : Fin 4 → Bool)
  | p4 (i : Fin 4) (s : Fin 4 → Bool)
  | p5 (sigma : alternatingGroup (Fin 4)) (s : Fin 3 → Bool)
  | p6 (sigma : alternatingGroup (Fin 4)) (s : Fin 3 → Bool)
  | p7 (sigma : alternatingGroup (Fin 4)) (s : Fin 4 → Bool)

private noncomputable def VertexCode120.eval : VertexCode120 → E4
  | .p1 c => vertP1 c
  | .p2 i s => vertP2 i s
  | .p3 i s => vertP3 i s
  | .p4 i s => vertP4 i s
  | .p5 sigma s => vertP5 sigma s
  | .p6 sigma s => vertP6 sigma s
  | .p7 sigma s => vertP7 sigma s

private theorem VertexCode120.eval_mem (c : VertexCode120) :
    c.eval ∈ centoventiVertici := by
  cases c with
  | p1 c => exact vertP1_mem120 c
  | p2 i s => exact vertP2_mem120 i s
  | p3 i s => exact vertP3_mem120 i s
  | p4 i s => exact vertP4_mem120 i s
  | p5 sigma s => exact vertP5_mem120 sigma s
  | p6 sigma s => exact vertP6_mem120 sigma s
  | p7 sigma s => exact vertP7_mem120 sigma s

/-- Radice della parete di rango 0, di norma quadra 4.-/
def alpha0_120 : E4 :=
  EuclideanSpace.single 0 1 +
    EuclideanSpace.single 1 (1 - aureo) +
    EuclideanSpace.single 3 (-aureo)

private theorem norm_sq_alpha0_120 : ‖alpha0_120‖ ^ 2 = 4 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  norm_num [alpha0_120, Fin.ext_iff]
  nlinarith [aureo_sq]

private theorem norm_alpha0_120 : ‖alpha0_120‖ = 2 := by
  nlinarith [norm_sq_alpha0_120, norm_nonneg alpha0_120]

/-- Parete 0: riflessione aurea.-/
def r0_120 : Isom 4 :=
  ((ℝ ∙ alpha0_120)ᗮ).reflection.toAffineIsometryEquiv

private theorem r0_120_formula (x : E4) :
    r0_120 x = x - (⟪alpha0_120, x⟫ / 2 : ℝ) • alpha0_120 := by
  change ((ℝ ∙ alpha0_120)ᗮ).reflection x = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, norm_alpha0_120]
  norm_num
  module

/-- Radice della parete di rango 2, di norma quadra 4.-/
def alpha2_120 : E4 :=
  EuclideanSpace.single 0 1 +
    EuclideanSpace.single 1 (-1) +
    EuclideanSpace.single 2 1 +
    EuclideanSpace.single 3 1

private theorem norm_sq_alpha2_120 : ‖alpha2_120‖ ^ 2 = 4 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  norm_num [alpha2_120, Fin.ext_iff]

private theorem norm_alpha2_120 : ‖alpha2_120‖ = 2 := by
  nlinarith [norm_sq_alpha2_120, norm_nonneg alpha2_120]

/-- Parete 2: riflessione nella radice intera.-/
def r2_120 : Isom 4 :=
  ((ℝ ∙ alpha2_120)ᗮ).reflection.toAffineIsometryEquiv

private theorem r2_120_formula (x : E4) :
    r2_120 x = x - (⟪alpha2_120, x⟫ / 2 : ℝ) • alpha2_120 := by
  change ((ℝ ∙ alpha2_120)ᗮ).reflection x = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, norm_alpha2_120]
  norm_num
  module

@[simp] private theorem permEven0123_symm_apply (i : Fin 4) :
    permEven0123.symm i = ![0, 1, 2, 3] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven0231_symm_apply (i : Fin 4) :
    permEven0231.symm i = ![0, 3, 1, 2] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven0312_symm_apply (i : Fin 4) :
    permEven0312.symm i = ![0, 2, 3, 1] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven1032_symm_apply (i : Fin 4) :
    permEven1032.symm i = ![1, 0, 3, 2] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven1203_symm_apply (i : Fin 4) :
    permEven1203.symm i = ![2, 0, 1, 3] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven1320_symm_apply (i : Fin 4) :
    permEven1320.symm i = ![3, 0, 2, 1] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven2013_symm_apply (i : Fin 4) :
    permEven2013.symm i = ![1, 2, 0, 3] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven2130_symm_apply (i : Fin 4) :
    permEven2130.symm i = ![3, 1, 0, 2] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven2301_symm_apply (i : Fin 4) :
    permEven2301.symm i = ![2, 3, 0, 1] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven3021_symm_apply (i : Fin 4) :
    permEven3021.symm i = ![1, 3, 2, 0] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven3102_symm_apply (i : Fin 4) :
    permEven3102.symm i = ![2, 1, 3, 0] i := by
  fin_cases i <;> decide

@[simp] private theorem permEven3210_symm_apply (i : Fin 4) :
    permEven3210.symm i = ![3, 2, 1, 0] i := by
  fin_cases i <;> decide

private def delta0_120 (x : E4) : ℝ :=
  x 0 + (1 - aureo) * x 1 - aureo * x 3

private theorem r0_120_apply_zero (x : E4) :
    r0_120 x 0 = x 0 - delta0_120 x / 2 := by
  rw [r0_120_formula]
  simp [delta0_120, alpha0_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  ring

private theorem r0_120_apply_one (x : E4) :
    r0_120 x 1 = x 1 - delta0_120 x / 2 * (1 - aureo) := by
  rw [r0_120_formula]
  simp [delta0_120, alpha0_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  exact Or.inl (by ring)

private theorem r0_120_apply_two (x : E4) :
    r0_120 x 2 = x 2 := by
  rw [r0_120_formula]
  simp [alpha0_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r0_120_apply_three (x : E4) :
    r0_120 x 3 = x 3 + delta0_120 x / 2 * aureo := by
  rw [r0_120_formula]
  simp [delta0_120, alpha0_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  exact Or.inl (by ring)

private theorem r0_120_apply (x : E4) (k : Fin 4) :
    r0_120 x k = ![x 0 - delta0_120 x / 2,
      x 1 - delta0_120 x / 2 * (1 - aureo), x 2,
      x 3 + delta0_120 x / 2 * aureo] k := by
  fin_cases k
  · exact r0_120_apply_zero x
  · exact r0_120_apply_one x
  · exact r0_120_apply_two x
  · exact r0_120_apply_three x

private def delta2_120 (x : E4) : ℝ :=
  x 0 - x 1 + x 2 + x 3

private theorem r2_120_apply_zero (x : E4) :
    r2_120 x 0 = x 0 - delta2_120 x / 2 := by
  rw [r2_120_formula]
  norm_num [delta2_120, alpha2_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  ring

private theorem r2_120_apply_one (x : E4) :
    r2_120 x 1 = x 1 + delta2_120 x / 2 := by
  rw [r2_120_formula]
  norm_num [delta2_120, alpha2_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  ring

private theorem r2_120_apply_two (x : E4) :
    r2_120 x 2 = x 2 - delta2_120 x / 2 := by
  rw [r2_120_formula]
  norm_num [delta2_120, alpha2_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  ring

private theorem r2_120_apply_three (x : E4) :
    r2_120 x 3 = x 3 - delta2_120 x / 2 := by
  rw [r2_120_formula]
  norm_num [delta2_120, alpha2_120, inner_add_left,
    EuclideanSpace.inner_single_left, Fin.ext_iff]
  ring

private theorem r2_120_apply (x : E4) (k : Fin 4) :
    r2_120 x k = ![x 0 - delta2_120 x / 2,
      x 1 + delta2_120 x / 2, x 2 - delta2_120 x / 2,
      x 3 - delta2_120 x / 2] k := by
  fin_cases k
  · exact r2_120_apply_zero x
  · exact r2_120_apply_one x
  · exact r2_120_apply_two x
  · exact r2_120_apply_three x
private def r2TargetP1_01 : Bool → Bool → VertexCode120
  | false, false => .p1 (codiceVentiquattro 0 1 (by omega) false false)
  | false, true => .p1 (codiceVentiquattro 2 3 (by omega) true true)
  | true, false => .p1 (codiceVentiquattro 2 3 (by omega) false false)
  | true, true => .p1 (codiceVentiquattro 0 1 (by omega) true true)

private theorem r2_P1_01_ff :
    r2_120 (vertP1 (codiceVentiquattro 0 1 (by omega) false false)) =
      (r2TargetP1_01 false false).eval := by
  rw [r2_120_formula]
  ext k
  fin_cases k <;> norm_num [r2TargetP1_01, VertexCode120.eval, alpha2_120,
    vertP1, vertVentiquattro, segnoVentiquattro, inner_add_left,
    inner_add_right, EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_P1_01_ft :
    r2_120 (vertP1 (codiceVentiquattro 0 1 (by omega) false true)) =
      (r2TargetP1_01 false true).eval := by
  rw [r2_120_formula]
  ext k
  fin_cases k <;> norm_num [r2TargetP1_01, VertexCode120.eval, alpha2_120,
    vertP1, vertVentiquattro, segnoVentiquattro, inner_add_left,
    inner_add_right, EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_P1_01_tf :
    r2_120 (vertP1 (codiceVentiquattro 0 1 (by omega) true false)) =
      (r2TargetP1_01 true false).eval := by
  rw [r2_120_formula]
  ext k
  fin_cases k <;> norm_num [r2TargetP1_01, VertexCode120.eval, alpha2_120,
    vertP1, vertVentiquattro, segnoVentiquattro, inner_add_left,
    inner_add_right, EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_P1_01_tt :
    r2_120 (vertP1 (codiceVentiquattro 0 1 (by omega) true true)) =
      (r2TargetP1_01 true true).eval := by
  rw [r2_120_formula]
  ext k
  fin_cases k <;> norm_num [r2TargetP1_01, VertexCode120.eval, alpha2_120,
    vertP1, vertVentiquattro, segnoVentiquattro, inner_add_left,
    inner_add_right, EuclideanSpace.inner_single_left, Fin.ext_iff]

private theorem r2_P1_01 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 0 1 (by omega) si sj)) =
      (r2TargetP1_01 si sj).eval := by
  cases si <;> cases sj
  · exact r2_P1_01_ff
  · exact r2_P1_01_ft
  · exact r2_P1_01_tf
  · exact r2_P1_01_tt

private def r2TargetP2_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![true, true, false, false]
  | true, true, true, false => .p3 2 ![true, true, true, false]
  | true, true, false, true => .p3 3 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, true, false, false]
  | true, false, true, true => .p3 0 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![true, true, false, false]
  | true, false, false, true => .p4 2 ![true, true, false, false]
  | true, false, false, false => .p3 1 ![true, false, false, false]
  | false, true, true, true => .p3 1 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![false, false, true, true]
  | false, true, false, true => .p4 3 ![false, false, true, true]
  | false, true, false, false => .p3 0 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, false, true, true]
  | false, false, true, false => .p3 3 ![false, false, true, false]
  | false, false, false, true => .p3 2 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![false, false, true, true]

private theorem r2_P2_i0 (s : Fin 4 → Bool) :
    r2_120 (vertP2 0 s) = (r2TargetP2_i0 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP2_i0, delta2_120, VertexCode120.eval,
    vertP2_apply, vertP3_apply, vertP4_apply, sqrt_five_eq_aureo,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP1_02 : Bool → Bool → VertexCode120
  | true, true => .p1 (codiceVentiquattro 1 3 (by omega) true false)
  | true, false => .p1 (codiceVentiquattro 0 2 (by omega) true false)
  | false, true => .p1 (codiceVentiquattro 0 2 (by omega) false true)
  | false, false => .p1 (codiceVentiquattro 1 3 (by omega) false true)

private theorem r2_P1_02 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 0 2 (by omega) si sj)) =
      (r2TargetP1_02 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r2_120_apply]
  all_goals fin_cases k
  all_goals simp [r2TargetP1_02, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP1_03 : Bool → Bool → VertexCode120
  | true, true => .p1 (codiceVentiquattro 1 2 (by omega) true false)
  | true, false => .p1 (codiceVentiquattro 0 3 (by omega) true false)
  | false, true => .p1 (codiceVentiquattro 0 3 (by omega) false true)
  | false, false => .p1 (codiceVentiquattro 1 2 (by omega) false true)

private theorem r2_P1_03 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 0 3 (by omega) si sj)) =
      (r2TargetP1_03 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r2_120_apply]
  all_goals fin_cases k
  all_goals simp [r2TargetP1_03, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP1_12 : Bool → Bool → VertexCode120
  | true, true => .p1 (codiceVentiquattro 1 2 (by omega) true true)
  | true, false => .p1 (codiceVentiquattro 0 3 (by omega) true true)
  | false, true => .p1 (codiceVentiquattro 0 3 (by omega) false false)
  | false, false => .p1 (codiceVentiquattro 1 2 (by omega) false false)

private theorem r2_P1_12 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 1 2 (by omega) si sj)) =
      (r2TargetP1_12 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r2_120_apply]
  all_goals fin_cases k
  all_goals simp [r2TargetP1_12, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP1_13 : Bool → Bool → VertexCode120
  | true, true => .p1 (codiceVentiquattro 1 3 (by omega) true true)
  | true, false => .p1 (codiceVentiquattro 0 2 (by omega) true true)
  | false, true => .p1 (codiceVentiquattro 0 2 (by omega) false false)
  | false, false => .p1 (codiceVentiquattro 1 3 (by omega) false false)

private theorem r2_P1_13 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 1 3 (by omega) si sj)) =
      (r2TargetP1_13 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r2_120_apply]
  all_goals fin_cases k
  all_goals simp [r2TargetP1_13, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP1_23 : Bool → Bool → VertexCode120
  | true, true => .p1 (codiceVentiquattro 0 1 (by omega) false true)
  | true, false => .p1 (codiceVentiquattro 2 3 (by omega) true false)
  | false, true => .p1 (codiceVentiquattro 2 3 (by omega) false true)
  | false, false => .p1 (codiceVentiquattro 0 1 (by omega) true false)

private theorem r2_P1_23 (si sj : Bool) :
    r2_120 (vertP1 (codiceVentiquattro 2 3 (by omega) si sj)) =
      (r2TargetP1_23 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r2_120_apply]
  all_goals fin_cases k
  all_goals simp [r2TargetP1_23, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP2_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![true, true, true, true]
  | true, true, true, false => .p3 3 ![true, true, true, false]
  | true, true, false, true => .p3 2 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, true, true, true]
  | true, false, true, true => .p3 1 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![false, false, false, false]
  | true, false, false, true => .p4 2 ![false, false, false, false]
  | true, false, false, false => .p3 0 ![true, false, false, false]
  | false, true, true, true => .p3 0 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![true, true, true, true]
  | false, true, false, true => .p4 3 ![true, true, true, true]
  | false, true, false, false => .p3 1 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, false, false, false]
  | false, false, true, false => .p3 2 ![false, false, true, false]
  | false, false, false, true => .p3 3 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![false, false, false, false]

set_option maxHeartbeats 1000000 in
private theorem r2_P2_i1 (s : Fin 4 → Bool) :
    r2_120 (vertP2 1 s) = (r2TargetP2_i1 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP2_i1, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP2_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![false, true, true, false]
  | true, true, true, false => .p3 0 ![true, true, true, false]
  | true, true, false, true => .p3 1 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, false, false, true]
  | true, false, true, true => .p3 2 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![false, true, true, false]
  | true, false, false, true => .p4 2 ![true, false, false, true]
  | true, false, false, false => .p3 3 ![true, false, false, false]
  | false, true, true, true => .p3 3 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![false, true, true, false]
  | false, true, false, true => .p4 3 ![true, false, false, true]
  | false, true, false, false => .p3 2 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, true, true, false]
  | false, false, true, false => .p3 1 ![false, false, true, false]
  | false, false, false, true => .p3 0 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![true, false, false, true]

private theorem r2_P2_i2 (s : Fin 4 → Bool) :
    r2_120 (vertP2 2 s) = (r2TargetP2_i2 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP2_i2, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP2_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![false, true, false, true]
  | true, true, true, false => .p3 1 ![true, true, true, false]
  | true, true, false, true => .p3 0 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, false, true, false]
  | true, false, true, true => .p3 3 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![true, false, true, false]
  | true, false, false, true => .p4 2 ![false, true, false, true]
  | true, false, false, false => .p3 2 ![true, false, false, false]
  | false, true, true, true => .p3 2 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![true, false, true, false]
  | false, true, false, true => .p4 3 ![false, true, false, true]
  | false, true, false, false => .p3 3 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, true, false, true]
  | false, false, true, false => .p3 0 ![false, false, true, false]
  | false, false, false, true => .p3 1 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![true, false, true, false]

private theorem r2_P2_i3 (s : Fin 4 → Bool) :
    r2_120 (vertP2 3 s) = (r2TargetP2_i3 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP2_i3, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP3_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![false, true, true, true]
  | true, true, true, false => .p2 2 ![true, true, true, false]
  | true, true, false, true => .p2 3 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, false, true, true]
  | true, false, true, true => .p2 0 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![false, false, true, false]
  | true, false, false, true => .p4 2 ![false, false, false, true]
  | true, false, false, false => .p2 1 ![true, false, false, false]
  | false, true, true, true => .p2 1 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![true, true, true, false]
  | false, true, false, true => .p4 3 ![true, true, false, true]
  | false, true, false, false => .p2 0 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, true, false, false]
  | false, false, true, false => .p2 3 ![false, false, true, false]
  | false, false, false, true => .p2 2 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![true, false, false, false]

private theorem r2_P3_i0 (s : Fin 4 → Bool) :
    r2_120 (vertP3 0 s) = (r2TargetP3_i0 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP3_i0, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP3_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![false, true, false, false]
  | true, true, true, false => .p2 3 ![true, true, true, false]
  | true, true, false, true => .p2 2 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, false, false, false]
  | true, false, true, true => .p2 1 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![true, true, true, false]
  | true, false, false, true => .p4 2 ![true, true, false, true]
  | true, false, false, false => .p2 0 ![true, false, false, false]
  | false, true, true, true => .p2 0 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![false, false, true, false]
  | false, true, false, true => .p4 3 ![false, false, false, true]
  | false, true, false, false => .p2 1 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, true, true, true]
  | false, false, true, false => .p2 2 ![false, false, true, false]
  | false, false, false, true => .p2 3 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![true, false, true, true]

private theorem r2_P3_i1 (s : Fin 4 → Bool) :
    r2_120 (vertP3 1 s) = (r2TargetP3_i1 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP3_i1, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP3_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![true, true, false, true]
  | true, true, true, false => .p2 0 ![true, true, true, false]
  | true, true, false, true => .p2 1 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, true, true, false]
  | true, false, true, true => .p2 2 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![true, false, false, false]
  | true, false, false, true => .p4 2 ![false, true, false, false]
  | true, false, false, false => .p2 3 ![true, false, false, false]
  | false, true, true, true => .p2 3 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![true, false, true, true]
  | false, true, false, true => .p4 3 ![false, true, true, true]
  | false, true, false, false => .p2 2 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, false, false, true]
  | false, false, true, false => .p2 1 ![false, false, true, false]
  | false, false, false, true => .p2 0 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![false, false, true, false]

private theorem r2_P3_i2 (s : Fin 4 → Bool) :
    r2_120 (vertP3 2 s) = (r2TargetP3_i2 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP3_i2, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP3_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 1 ![true, true, true, false]
  | true, true, true, false => .p2 1 ![true, true, true, false]
  | true, true, false, true => .p2 0 ![true, true, false, true]
  | true, true, false, false => .p4 0 ![true, true, false, true]
  | true, false, true, true => .p2 3 ![false, true, false, false]
  | true, false, true, false => .p4 3 ![false, true, false, false]
  | true, false, false, true => .p4 2 ![true, false, false, false]
  | true, false, false, false => .p2 2 ![true, false, false, false]
  | false, true, true, true => .p2 2 ![false, true, true, true]
  | false, true, true, false => .p4 2 ![false, true, true, true]
  | false, true, false, true => .p4 3 ![true, false, true, true]
  | false, true, false, false => .p2 3 ![true, false, true, true]
  | false, false, true, true => .p4 0 ![false, false, true, false]
  | false, false, true, false => .p2 0 ![false, false, true, false]
  | false, false, false, true => .p2 1 ![false, false, false, true]
  | false, false, false, false => .p4 1 ![false, false, false, true]

private theorem r2_P3_i3 (s : Fin 4 → Bool) :
    r2_120 (vertP3 3 s) = (r2TargetP3_i3 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP3_i3, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP4_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 1 ![true, true, false, false]
  | true, true, true, false => .p3 2 ![true, true, false, false]
  | true, true, false, true => .p3 3 ![true, true, false, false]
  | true, true, false, false => .p2 0 ![true, true, false, false]
  | true, false, true, true => .p3 0 ![true, true, false, false]
  | true, false, true, false => .p2 3 ![true, true, false, false]
  | true, false, false, true => .p2 2 ![true, true, false, false]
  | true, false, false, false => .p3 1 ![true, true, false, false]
  | false, true, true, true => .p3 1 ![false, false, true, true]
  | false, true, true, false => .p2 2 ![false, false, true, true]
  | false, true, false, true => .p2 3 ![false, false, true, true]
  | false, true, false, false => .p3 0 ![false, false, true, true]
  | false, false, true, true => .p2 0 ![false, false, true, true]
  | false, false, true, false => .p3 3 ![false, false, true, true]
  | false, false, false, true => .p3 2 ![false, false, true, true]
  | false, false, false, false => .p2 1 ![false, false, true, true]

private theorem r2_P4_i0_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r2_120 (vertP4 0 s) = (r2TargetP4_i0 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i0, delta2_120, VertexCode120.eval,
    vertP2_apply, vertP3_apply, vertP4_apply, sqrt_five_eq_aureo,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r2_P4_i0_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r2_120 (vertP4 0 s) = (r2TargetP4_i0 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i0, delta2_120, VertexCode120.eval,
    vertP2_apply, vertP3_apply, vertP4_apply, sqrt_five_eq_aureo,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r2_P4_i0 (s : Fin 4 → Bool) :
    r2_120 (vertP4 0 s) = (r2TargetP4_i0 s).eval := by
  cases h0 : s 0
  · exact r2_P4_i0_false s h0
  · exact r2_P4_i0_true s h0

private def r2TargetP4_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 1 ![true, true, true, true]
  | true, true, true, false => .p3 3 ![true, true, true, true]
  | true, true, false, true => .p3 2 ![true, true, true, true]
  | true, true, false, false => .p2 0 ![true, true, true, true]
  | true, false, true, true => .p3 1 ![false, false, false, false]
  | true, false, true, false => .p2 3 ![false, false, false, false]
  | true, false, false, true => .p2 2 ![false, false, false, false]
  | true, false, false, false => .p3 0 ![false, false, false, false]
  | false, true, true, true => .p3 0 ![true, true, true, true]
  | false, true, true, false => .p2 2 ![true, true, true, true]
  | false, true, false, true => .p2 3 ![true, true, true, true]
  | false, true, false, false => .p3 1 ![true, true, true, true]
  | false, false, true, true => .p2 0 ![false, false, false, false]
  | false, false, true, false => .p3 2 ![false, false, false, false]
  | false, false, false, true => .p3 3 ![false, false, false, false]
  | false, false, false, false => .p2 1 ![false, false, false, false]

private theorem r2_P4_i1_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r2_120 (vertP4 1 s) = (r2TargetP4_i1 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i1, delta2_120, VertexCode120.eval,
    vertP2_apply, vertP3_apply, vertP4_apply, sqrt_five_eq_aureo,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r2_P4_i1_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r2_120 (vertP4 1 s) = (r2TargetP4_i1 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i1, delta2_120, VertexCode120.eval,
    vertP2_apply, vertP3_apply, vertP4_apply, sqrt_five_eq_aureo,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r2_P4_i1 (s : Fin 4 → Bool) :
    r2_120 (vertP4 1 s) = (r2TargetP4_i1 s).eval := by
  cases h0 : s 0
  · exact r2_P4_i1_false s h0
  · exact r2_P4_i1_true s h0

private def r2TargetP4_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 1 ![false, true, true, false]
  | true, true, true, false => .p3 0 ![false, true, true, false]
  | true, true, false, true => .p3 1 ![true, false, false, true]
  | true, true, false, false => .p2 0 ![true, false, false, true]
  | true, false, true, true => .p3 2 ![false, true, true, false]
  | true, false, true, false => .p2 3 ![false, true, true, false]
  | true, false, false, true => .p2 2 ![true, false, false, true]
  | true, false, false, false => .p3 3 ![true, false, false, true]
  | false, true, true, true => .p3 3 ![false, true, true, false]
  | false, true, true, false => .p2 2 ![false, true, true, false]
  | false, true, false, true => .p2 3 ![true, false, false, true]
  | false, true, false, false => .p3 2 ![true, false, false, true]
  | false, false, true, true => .p2 0 ![false, true, true, false]
  | false, false, true, false => .p3 1 ![false, true, true, false]
  | false, false, false, true => .p3 0 ![true, false, false, true]
  | false, false, false, false => .p2 1 ![true, false, false, true]

set_option maxHeartbeats 1000000 in
private theorem r2_P4_i2 (s : Fin 4 → Bool) :
    r2_120 (vertP4 2 s) = (r2TargetP4_i2 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i2, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP4_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 1 ![false, true, false, true]
  | true, true, true, false => .p3 1 ![true, false, true, false]
  | true, true, false, true => .p3 0 ![false, true, false, true]
  | true, true, false, false => .p2 0 ![true, false, true, false]
  | true, false, true, true => .p3 3 ![false, true, false, true]
  | true, false, true, false => .p2 3 ![true, false, true, false]
  | true, false, false, true => .p2 2 ![false, true, false, true]
  | true, false, false, false => .p3 2 ![true, false, true, false]
  | false, true, true, true => .p3 2 ![false, true, false, true]
  | false, true, true, false => .p2 2 ![true, false, true, false]
  | false, true, false, true => .p2 3 ![false, true, false, true]
  | false, true, false, false => .p3 3 ![true, false, true, false]
  | false, false, true, true => .p2 0 ![false, true, false, true]
  | false, false, true, false => .p3 0 ![true, false, true, false]
  | false, false, false, true => .p3 1 ![false, true, false, true]
  | false, false, false, false => .p2 1 ![true, false, true, false]

private theorem r2_P4_i3 (s : Fin 4 → Bool) :
    r2_120 (vertP4 3 s) = (r2TargetP4_i3 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;>
    cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP4_i3, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s0123 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2301 ![false, true, false, true]
  | true, true, false => .p7 sigmaEven1032 ![false, true, false, true]
  | true, false, true => .p7 sigmaEven0123 ![false, true, false, true]
  | true, false, false => .p7 sigmaEven3210 ![false, true, false, true]
  | false, true, true => .p7 sigmaEven3210 ![true, false, true, false]
  | false, true, false => .p7 sigmaEven0123 ![true, false, true, false]
  | false, false, true => .p7 sigmaEven1032 ![true, false, true, false]
  | false, false, false => .p7 sigmaEven2301 ![true, false, true, false]

private theorem r2_P5_s0123 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven0123 s) = (r2TargetP5_s0123 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s0123, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s0231 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven0231 ![true, true, true, true]
  | true, true, false => .p7 sigmaEven1320 ![false, false, false, false]
  | true, false, true => .p7 sigmaEven3102 ![true, true, true, true]
  | true, false, false => .p7 sigmaEven2013 ![false, false, false, false]
  | false, true, true => .p7 sigmaEven2013 ![true, true, true, true]
  | false, true, false => .p7 sigmaEven3102 ![false, false, false, false]
  | false, false, true => .p7 sigmaEven1320 ![true, true, true, true]
  | false, false, false => .p7 sigmaEven0231 ![false, false, false, false]

private theorem r2_P5_s0231 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven0231 s) = (r2TargetP5_s0231 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s0231, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s0312 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven3021 ![false, false, true, true]
  | true, true, false => .p7 sigmaEven1203 ![false, false, true, true]
  | true, false, true => .p7 sigmaEven2130 ![true, true, false, false]
  | true, false, false => .p7 sigmaEven0312 ![true, true, false, false]
  | false, true, true => .p7 sigmaEven0312 ![false, false, true, true]
  | false, true, false => .p7 sigmaEven2130 ![false, false, true, true]
  | false, false, true => .p7 sigmaEven1203 ![true, true, false, false]
  | false, false, false => .p7 sigmaEven3021 ![true, true, false, false]

private theorem r2_P5_s0312 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven0312 s) = (r2TargetP5_s0312 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s0312, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s1032 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2301 ![true, false, false, true]
  | true, true, false => .p7 sigmaEven1032 ![false, true, true, false]
  | true, false, true => .p7 sigmaEven0123 ![false, true, true, false]
  | true, false, false => .p7 sigmaEven3210 ![true, false, false, true]
  | false, true, true => .p7 sigmaEven3210 ![false, true, true, false]
  | false, true, false => .p7 sigmaEven0123 ![true, false, false, true]
  | false, false, true => .p7 sigmaEven1032 ![true, false, false, true]
  | false, false, false => .p7 sigmaEven2301 ![false, true, true, false]

private theorem r2_P5_s1032 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven1032 s) = (r2TargetP5_s1032 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s1032, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s1203 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven3021 ![true, false, false, true]
  | true, true, false => .p7 sigmaEven1203 ![false, true, true, false]
  | true, false, true => .p7 sigmaEven2130 ![false, true, true, false]
  | true, false, false => .p7 sigmaEven0312 ![true, false, false, true]
  | false, true, true => .p7 sigmaEven0312 ![false, true, true, false]
  | false, true, false => .p7 sigmaEven2130 ![true, false, false, true]
  | false, false, true => .p7 sigmaEven1203 ![true, false, false, true]
  | false, false, false => .p7 sigmaEven3021 ![false, true, true, false]

private theorem r2_P5_s1203 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven1203 s) = (r2TargetP5_s1203 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s1203, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s1320 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven0231 ![true, false, false, true]
  | true, true, false => .p7 sigmaEven1320 ![false, true, true, false]
  | true, false, true => .p7 sigmaEven3102 ![false, true, true, false]
  | true, false, false => .p7 sigmaEven2013 ![true, false, false, true]
  | false, true, true => .p7 sigmaEven2013 ![false, true, true, false]
  | false, true, false => .p7 sigmaEven3102 ![true, false, false, true]
  | false, false, true => .p7 sigmaEven1320 ![true, false, false, true]
  | false, false, false => .p7 sigmaEven0231 ![false, true, true, false]

private theorem r2_P5_s1320 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven1320 s) = (r2TargetP5_s1320 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s1320, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s2013 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven0231 ![false, false, true, true]
  | true, true, false => .p7 sigmaEven1320 ![false, false, true, true]
  | true, false, true => .p7 sigmaEven3102 ![true, true, false, false]
  | true, false, false => .p7 sigmaEven2013 ![true, true, false, false]
  | false, true, true => .p7 sigmaEven2013 ![false, false, true, true]
  | false, true, false => .p7 sigmaEven3102 ![false, false, true, true]
  | false, false, true => .p7 sigmaEven1320 ![true, true, false, false]
  | false, false, false => .p7 sigmaEven0231 ![true, true, false, false]

private theorem r2_P5_s2013 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven2013 s) = (r2TargetP5_s2013 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s2013, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s2130 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven3021 ![false, true, false, true]
  | true, true, false => .p7 sigmaEven1203 ![false, true, false, true]
  | true, false, true => .p7 sigmaEven2130 ![false, true, false, true]
  | true, false, false => .p7 sigmaEven0312 ![false, true, false, true]
  | false, true, true => .p7 sigmaEven0312 ![true, false, true, false]
  | false, true, false => .p7 sigmaEven2130 ![true, false, true, false]
  | false, false, true => .p7 sigmaEven1203 ![true, false, true, false]
  | false, false, false => .p7 sigmaEven3021 ![true, false, true, false]

private theorem r2_P5_s2130 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven2130 s) = (r2TargetP5_s2130 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s2130, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s2301 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2301 ![true, true, true, true]
  | true, true, false => .p7 sigmaEven1032 ![false, false, false, false]
  | true, false, true => .p7 sigmaEven0123 ![true, true, true, true]
  | true, false, false => .p7 sigmaEven3210 ![false, false, false, false]
  | false, true, true => .p7 sigmaEven3210 ![true, true, true, true]
  | false, true, false => .p7 sigmaEven0123 ![false, false, false, false]
  | false, false, true => .p7 sigmaEven1032 ![true, true, true, true]
  | false, false, false => .p7 sigmaEven2301 ![false, false, false, false]

private theorem r2_P5_s2301 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven2301 s) = (r2TargetP5_s2301 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s2301, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s3021 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven3021 ![true, true, true, true]
  | true, true, false => .p7 sigmaEven1203 ![false, false, false, false]
  | true, false, true => .p7 sigmaEven2130 ![true, true, true, true]
  | true, false, false => .p7 sigmaEven0312 ![false, false, false, false]
  | false, true, true => .p7 sigmaEven0312 ![true, true, true, true]
  | false, true, false => .p7 sigmaEven2130 ![false, false, false, false]
  | false, false, true => .p7 sigmaEven1203 ![true, true, true, true]
  | false, false, false => .p7 sigmaEven3021 ![false, false, false, false]

private theorem r2_P5_s3021 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven3021 s) = (r2TargetP5_s3021 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s3021, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s3102 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven0231 ![false, true, false, true]
  | true, true, false => .p7 sigmaEven1320 ![false, true, false, true]
  | true, false, true => .p7 sigmaEven3102 ![false, true, false, true]
  | true, false, false => .p7 sigmaEven2013 ![false, true, false, true]
  | false, true, true => .p7 sigmaEven2013 ![true, false, true, false]
  | false, true, false => .p7 sigmaEven3102 ![true, false, true, false]
  | false, false, true => .p7 sigmaEven1320 ![true, false, true, false]
  | false, false, false => .p7 sigmaEven0231 ![true, false, true, false]

private theorem r2_P5_s3102 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven3102 s) = (r2TargetP5_s3102 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s3102, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP5_s3210 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2301 ![false, false, true, true]
  | true, true, false => .p7 sigmaEven1032 ![false, false, true, true]
  | true, false, true => .p7 sigmaEven0123 ![true, true, false, false]
  | true, false, false => .p7 sigmaEven3210 ![true, true, false, false]
  | false, true, true => .p7 sigmaEven3210 ![false, false, true, true]
  | false, true, false => .p7 sigmaEven0123 ![false, false, true, true]
  | false, false, true => .p7 sigmaEven1032 ![true, true, false, false]
  | false, false, false => .p7 sigmaEven2301 ![true, true, false, false]

private theorem r2_P5_s3210 (s : Fin 3 → Bool) :
    r2_120 (vertP5 sigmaEven3210 s) = (r2TargetP5_s3210 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP5_s3210, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s0123 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2301 ![true, false, true]
  | true, true, false => .p6 sigmaEven1032 ![true, false, true]
  | true, false, true => .p6 sigmaEven0123 ![true, false, true]
  | true, false, false => .p6 sigmaEven3210 ![true, false, true]
  | false, true, true => .p6 sigmaEven3210 ![false, true, false]
  | false, true, false => .p6 sigmaEven0123 ![false, true, false]
  | false, false, true => .p6 sigmaEven1032 ![false, true, false]
  | false, false, false => .p6 sigmaEven2301 ![false, true, false]

private theorem r2_P6_s0123 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven0123 s) = (r2TargetP6_s0123 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s0123, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s0231 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven0231 ![true, true, true]
  | true, true, false => .p6 sigmaEven1320 ![false, false, false]
  | true, false, true => .p6 sigmaEven3102 ![true, true, true]
  | true, false, false => .p6 sigmaEven2013 ![false, false, false]
  | false, true, true => .p6 sigmaEven2013 ![true, true, true]
  | false, true, false => .p6 sigmaEven3102 ![false, false, false]
  | false, false, true => .p6 sigmaEven1320 ![true, true, true]
  | false, false, false => .p6 sigmaEven0231 ![false, false, false]

private theorem r2_P6_s0231 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven0231 s) = (r2TargetP6_s0231 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s0231, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s0312 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven3021 ![false, true, true]
  | true, true, false => .p6 sigmaEven1203 ![false, true, true]
  | true, false, true => .p6 sigmaEven2130 ![true, false, false]
  | true, false, false => .p6 sigmaEven0312 ![true, false, false]
  | false, true, true => .p6 sigmaEven0312 ![false, true, true]
  | false, true, false => .p6 sigmaEven2130 ![false, true, true]
  | false, false, true => .p6 sigmaEven1203 ![true, false, false]
  | false, false, false => .p6 sigmaEven3021 ![true, false, false]

private theorem r2_P6_s0312 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven0312 s) = (r2TargetP6_s0312 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s0312, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s1032 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2301 ![false, false, true]
  | true, true, false => .p6 sigmaEven1032 ![true, true, false]
  | true, false, true => .p6 sigmaEven0123 ![true, true, false]
  | true, false, false => .p6 sigmaEven3210 ![false, false, true]
  | false, true, true => .p6 sigmaEven3210 ![true, true, false]
  | false, true, false => .p6 sigmaEven0123 ![false, false, true]
  | false, false, true => .p6 sigmaEven1032 ![false, false, true]
  | false, false, false => .p6 sigmaEven2301 ![true, true, false]

private theorem r2_P6_s1032 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven1032 s) = (r2TargetP6_s1032 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s1032, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s1203 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven3021 ![false, false, true]
  | true, true, false => .p6 sigmaEven1203 ![true, true, false]
  | true, false, true => .p6 sigmaEven2130 ![true, true, false]
  | true, false, false => .p6 sigmaEven0312 ![false, false, true]
  | false, true, true => .p6 sigmaEven0312 ![true, true, false]
  | false, true, false => .p6 sigmaEven2130 ![false, false, true]
  | false, false, true => .p6 sigmaEven1203 ![false, false, true]
  | false, false, false => .p6 sigmaEven3021 ![true, true, false]

private theorem r2_P6_s1203 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven1203 s) = (r2TargetP6_s1203 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s1203, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s1320 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven0231 ![false, false, true]
  | true, true, false => .p6 sigmaEven1320 ![true, true, false]
  | true, false, true => .p6 sigmaEven3102 ![true, true, false]
  | true, false, false => .p6 sigmaEven2013 ![false, false, true]
  | false, true, true => .p6 sigmaEven2013 ![true, true, false]
  | false, true, false => .p6 sigmaEven3102 ![false, false, true]
  | false, false, true => .p6 sigmaEven1320 ![false, false, true]
  | false, false, false => .p6 sigmaEven0231 ![true, true, false]

private theorem r2_P6_s1320 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven1320 s) = (r2TargetP6_s1320 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s1320, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s2013 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven0231 ![false, true, true]
  | true, true, false => .p6 sigmaEven1320 ![false, true, true]
  | true, false, true => .p6 sigmaEven3102 ![true, false, false]
  | true, false, false => .p6 sigmaEven2013 ![true, false, false]
  | false, true, true => .p6 sigmaEven2013 ![false, true, true]
  | false, true, false => .p6 sigmaEven3102 ![false, true, true]
  | false, false, true => .p6 sigmaEven1320 ![true, false, false]
  | false, false, false => .p6 sigmaEven0231 ![true, false, false]

private theorem r2_P6_s2013 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven2013 s) = (r2TargetP6_s2013 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s2013, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s2130 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven3021 ![true, false, true]
  | true, true, false => .p6 sigmaEven1203 ![true, false, true]
  | true, false, true => .p6 sigmaEven2130 ![true, false, true]
  | true, false, false => .p6 sigmaEven0312 ![true, false, true]
  | false, true, true => .p6 sigmaEven0312 ![false, true, false]
  | false, true, false => .p6 sigmaEven2130 ![false, true, false]
  | false, false, true => .p6 sigmaEven1203 ![false, true, false]
  | false, false, false => .p6 sigmaEven3021 ![false, true, false]

private theorem r2_P6_s2130 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven2130 s) = (r2TargetP6_s2130 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s2130, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s2301 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2301 ![true, true, true]
  | true, true, false => .p6 sigmaEven1032 ![false, false, false]
  | true, false, true => .p6 sigmaEven0123 ![true, true, true]
  | true, false, false => .p6 sigmaEven3210 ![false, false, false]
  | false, true, true => .p6 sigmaEven3210 ![true, true, true]
  | false, true, false => .p6 sigmaEven0123 ![false, false, false]
  | false, false, true => .p6 sigmaEven1032 ![true, true, true]
  | false, false, false => .p6 sigmaEven2301 ![false, false, false]

private theorem r2_P6_s2301 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven2301 s) = (r2TargetP6_s2301 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s2301, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s3021 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven3021 ![true, true, true]
  | true, true, false => .p6 sigmaEven1203 ![false, false, false]
  | true, false, true => .p6 sigmaEven2130 ![true, true, true]
  | true, false, false => .p6 sigmaEven0312 ![false, false, false]
  | false, true, true => .p6 sigmaEven0312 ![true, true, true]
  | false, true, false => .p6 sigmaEven2130 ![false, false, false]
  | false, false, true => .p6 sigmaEven1203 ![true, true, true]
  | false, false, false => .p6 sigmaEven3021 ![false, false, false]

private theorem r2_P6_s3021 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven3021 s) = (r2TargetP6_s3021 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s3021, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s3102 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven0231 ![true, false, true]
  | true, true, false => .p6 sigmaEven1320 ![true, false, true]
  | true, false, true => .p6 sigmaEven3102 ![true, false, true]
  | true, false, false => .p6 sigmaEven2013 ![true, false, true]
  | false, true, true => .p6 sigmaEven2013 ![false, true, false]
  | false, true, false => .p6 sigmaEven3102 ![false, true, false]
  | false, false, true => .p6 sigmaEven1320 ![false, true, false]
  | false, false, false => .p6 sigmaEven0231 ![false, true, false]

private theorem r2_P6_s3102 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven3102 s) = (r2TargetP6_s3102 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s3102, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP6_s3210 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2301 ![false, true, true]
  | true, true, false => .p6 sigmaEven1032 ![false, true, true]
  | true, false, true => .p6 sigmaEven0123 ![true, false, false]
  | true, false, false => .p6 sigmaEven3210 ![true, false, false]
  | false, true, true => .p6 sigmaEven3210 ![false, true, true]
  | false, true, false => .p6 sigmaEven0123 ![false, true, true]
  | false, false, true => .p6 sigmaEven1032 ![true, false, false]
  | false, false, false => .p6 sigmaEven2301 ![true, false, false]

private theorem r2_P6_s3210 (s : Fin 3 → Bool) :
    r2_120 (vertP6 sigmaEven3210 s) = (r2TargetP6_s3210 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r2TargetP6_s3210, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s0123 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven2301 ![true, false, true]
  | true, true, true, false => .p7 sigmaEven1032 ![true, true, false, true]
  | true, true, false, true => .p7 sigmaEven0123 ![true, true, false, true]
  | true, true, false, false => .p5 sigmaEven3210 ![true, false, true]
  | true, false, true, true => .p7 sigmaEven3210 ![false, false, true, false]
  | true, false, true, false => .p5 sigmaEven0123 ![false, true, false]
  | true, false, false, true => .p5 sigmaEven1032 ![false, true, false]
  | true, false, false, false => .p7 sigmaEven2301 ![false, false, true, false]
  | false, true, true, true => .p7 sigmaEven2301 ![true, true, false, true]
  | false, true, true, false => .p5 sigmaEven1032 ![true, false, true]
  | false, true, false, true => .p5 sigmaEven0123 ![true, false, true]
  | false, true, false, false => .p7 sigmaEven3210 ![true, true, false, true]
  | false, false, true, true => .p5 sigmaEven3210 ![false, true, false]
  | false, false, true, false => .p7 sigmaEven0123 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven1032 ![false, false, true, false]
  | false, false, false, false => .p5 sigmaEven2301 ![false, true, false]

private theorem r2_P7_s0123 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven0123 s) = (r2TargetP7_s0123 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s0123, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s0231 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven0231 ![true, true, true]
  | true, true, true, false => .p7 sigmaEven1320 ![true, false, false, false]
  | true, true, false, true => .p7 sigmaEven3102 ![false, true, true, true]
  | true, true, false, false => .p5 sigmaEven2013 ![false, false, false]
  | true, false, true, true => .p7 sigmaEven2013 ![false, true, true, true]
  | true, false, true, false => .p5 sigmaEven3102 ![false, false, false]
  | true, false, false, true => .p5 sigmaEven1320 ![true, true, true]
  | true, false, false, false => .p7 sigmaEven0231 ![true, false, false, false]
  | false, true, true, true => .p7 sigmaEven0231 ![false, true, true, true]
  | false, true, true, false => .p5 sigmaEven1320 ![false, false, false]
  | false, true, false, true => .p5 sigmaEven3102 ![true, true, true]
  | false, true, false, false => .p7 sigmaEven2013 ![true, false, false, false]
  | false, false, true, true => .p5 sigmaEven2013 ![true, true, true]
  | false, false, true, false => .p7 sigmaEven3102 ![true, false, false, false]
  | false, false, false, true => .p7 sigmaEven1320 ![false, true, true, true]
  | false, false, false, false => .p5 sigmaEven0231 ![false, false, false]

private theorem r2_P7_s0231 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven0231 s) = (r2TargetP7_s0231 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s0231, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s0312 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3021 ![false, true, true]
  | true, true, true, false => .p7 sigmaEven1203 ![true, false, true, true]
  | true, true, false, true => .p7 sigmaEven2130 ![false, true, false, false]
  | true, true, false, false => .p5 sigmaEven0312 ![true, false, false]
  | true, false, true, true => .p7 sigmaEven0312 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven2130 ![false, true, true]
  | true, false, false, true => .p5 sigmaEven1203 ![true, false, false]
  | true, false, false, false => .p7 sigmaEven3021 ![false, true, false, false]
  | false, true, true, true => .p7 sigmaEven3021 ![true, false, true, true]
  | false, true, true, false => .p5 sigmaEven1203 ![false, true, true]
  | false, true, false, true => .p5 sigmaEven2130 ![true, false, false]
  | false, true, false, false => .p7 sigmaEven0312 ![false, true, false, false]
  | false, false, true, true => .p5 sigmaEven0312 ![false, true, true]
  | false, false, true, false => .p7 sigmaEven2130 ![true, false, true, true]
  | false, false, false, true => .p7 sigmaEven1203 ![false, true, false, false]
  | false, false, false, false => .p5 sigmaEven3021 ![true, false, false]

private theorem r2_P7_s0312 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven0312 s) = (r2TargetP7_s0312 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s0312, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s1032 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven2301 ![false, false, true]
  | true, true, true, false => .p7 sigmaEven1032 ![true, true, true, false]
  | true, true, false, true => .p7 sigmaEven0123 ![true, true, true, false]
  | true, true, false, false => .p5 sigmaEven3210 ![false, false, true]
  | true, false, true, true => .p7 sigmaEven3210 ![true, true, true, false]
  | true, false, true, false => .p5 sigmaEven0123 ![false, false, true]
  | true, false, false, true => .p5 sigmaEven1032 ![false, false, true]
  | true, false, false, false => .p7 sigmaEven2301 ![true, true, true, false]
  | false, true, true, true => .p7 sigmaEven2301 ![false, false, false, true]
  | false, true, true, false => .p5 sigmaEven1032 ![true, true, false]
  | false, true, false, true => .p5 sigmaEven0123 ![true, true, false]
  | false, true, false, false => .p7 sigmaEven3210 ![false, false, false, true]
  | false, false, true, true => .p5 sigmaEven3210 ![true, true, false]
  | false, false, true, false => .p7 sigmaEven0123 ![false, false, false, true]
  | false, false, false, true => .p7 sigmaEven1032 ![false, false, false, true]
  | false, false, false, false => .p5 sigmaEven2301 ![true, true, false]

private theorem r2_P7_s1032 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven1032 s) = (r2TargetP7_s1032 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s1032, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s1203 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3021 ![false, false, true]
  | true, true, true, false => .p7 sigmaEven1203 ![true, true, true, false]
  | true, true, false, true => .p7 sigmaEven2130 ![true, true, true, false]
  | true, true, false, false => .p5 sigmaEven0312 ![false, false, true]
  | true, false, true, true => .p7 sigmaEven0312 ![true, true, true, false]
  | true, false, true, false => .p5 sigmaEven2130 ![false, false, true]
  | true, false, false, true => .p5 sigmaEven1203 ![false, false, true]
  | true, false, false, false => .p7 sigmaEven3021 ![true, true, true, false]
  | false, true, true, true => .p7 sigmaEven3021 ![false, false, false, true]
  | false, true, true, false => .p5 sigmaEven1203 ![true, true, false]
  | false, true, false, true => .p5 sigmaEven2130 ![true, true, false]
  | false, true, false, false => .p7 sigmaEven0312 ![false, false, false, true]
  | false, false, true, true => .p5 sigmaEven0312 ![true, true, false]
  | false, false, true, false => .p7 sigmaEven2130 ![false, false, false, true]
  | false, false, false, true => .p7 sigmaEven1203 ![false, false, false, true]
  | false, false, false, false => .p5 sigmaEven3021 ![true, true, false]

private theorem r2_P7_s1203 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven1203 s) = (r2TargetP7_s1203 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s1203, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s1320 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven0231 ![false, false, true]
  | true, true, true, false => .p7 sigmaEven1320 ![true, true, true, false]
  | true, true, false, true => .p7 sigmaEven3102 ![true, true, true, false]
  | true, true, false, false => .p5 sigmaEven2013 ![false, false, true]
  | true, false, true, true => .p7 sigmaEven2013 ![true, true, true, false]
  | true, false, true, false => .p5 sigmaEven3102 ![false, false, true]
  | true, false, false, true => .p5 sigmaEven1320 ![false, false, true]
  | true, false, false, false => .p7 sigmaEven0231 ![true, true, true, false]
  | false, true, true, true => .p7 sigmaEven0231 ![false, false, false, true]
  | false, true, true, false => .p5 sigmaEven1320 ![true, true, false]
  | false, true, false, true => .p5 sigmaEven3102 ![true, true, false]
  | false, true, false, false => .p7 sigmaEven2013 ![false, false, false, true]
  | false, false, true, true => .p5 sigmaEven2013 ![true, true, false]
  | false, false, true, false => .p7 sigmaEven3102 ![false, false, false, true]
  | false, false, false, true => .p7 sigmaEven1320 ![false, false, false, true]
  | false, false, false, false => .p5 sigmaEven0231 ![true, true, false]

set_option maxHeartbeats 1000000 in
private theorem r2_P7_s1320 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven1320 s) = (r2TargetP7_s1320 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s1320, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s2013 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven0231 ![false, true, true]
  | true, true, true, false => .p7 sigmaEven1320 ![true, false, true, true]
  | true, true, false, true => .p7 sigmaEven3102 ![false, true, false, false]
  | true, true, false, false => .p5 sigmaEven2013 ![true, false, false]
  | true, false, true, true => .p7 sigmaEven2013 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven3102 ![false, true, true]
  | true, false, false, true => .p5 sigmaEven1320 ![true, false, false]
  | true, false, false, false => .p7 sigmaEven0231 ![false, true, false, false]
  | false, true, true, true => .p7 sigmaEven0231 ![true, false, true, true]
  | false, true, true, false => .p5 sigmaEven1320 ![false, true, true]
  | false, true, false, true => .p5 sigmaEven3102 ![true, false, false]
  | false, true, false, false => .p7 sigmaEven2013 ![false, true, false, false]
  | false, false, true, true => .p5 sigmaEven2013 ![false, true, true]
  | false, false, true, false => .p7 sigmaEven3102 ![true, false, true, true]
  | false, false, false, true => .p7 sigmaEven1320 ![false, true, false, false]
  | false, false, false, false => .p5 sigmaEven0231 ![true, false, false]

private theorem r2_P7_s2013 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven2013 s) = (r2TargetP7_s2013 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s2013, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s2130 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3021 ![true, false, true]
  | true, true, true, false => .p7 sigmaEven1203 ![true, true, false, true]
  | true, true, false, true => .p7 sigmaEven2130 ![true, true, false, true]
  | true, true, false, false => .p5 sigmaEven0312 ![true, false, true]
  | true, false, true, true => .p7 sigmaEven0312 ![false, false, true, false]
  | true, false, true, false => .p5 sigmaEven2130 ![false, true, false]
  | true, false, false, true => .p5 sigmaEven1203 ![false, true, false]
  | true, false, false, false => .p7 sigmaEven3021 ![false, false, true, false]
  | false, true, true, true => .p7 sigmaEven3021 ![true, true, false, true]
  | false, true, true, false => .p5 sigmaEven1203 ![true, false, true]
  | false, true, false, true => .p5 sigmaEven2130 ![true, false, true]
  | false, true, false, false => .p7 sigmaEven0312 ![true, true, false, true]
  | false, false, true, true => .p5 sigmaEven0312 ![false, true, false]
  | false, false, true, false => .p7 sigmaEven2130 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven1203 ![false, false, true, false]
  | false, false, false, false => .p5 sigmaEven3021 ![false, true, false]

private theorem r2_P7_s2130 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven2130 s) = (r2TargetP7_s2130 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s2130, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s2301 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven2301 ![true, true, true]
  | true, true, true, false => .p7 sigmaEven1032 ![true, false, false, false]
  | true, true, false, true => .p7 sigmaEven0123 ![false, true, true, true]
  | true, true, false, false => .p5 sigmaEven3210 ![false, false, false]
  | true, false, true, true => .p7 sigmaEven3210 ![false, true, true, true]
  | true, false, true, false => .p5 sigmaEven0123 ![false, false, false]
  | true, false, false, true => .p5 sigmaEven1032 ![true, true, true]
  | true, false, false, false => .p7 sigmaEven2301 ![true, false, false, false]
  | false, true, true, true => .p7 sigmaEven2301 ![false, true, true, true]
  | false, true, true, false => .p5 sigmaEven1032 ![false, false, false]
  | false, true, false, true => .p5 sigmaEven0123 ![true, true, true]
  | false, true, false, false => .p7 sigmaEven3210 ![true, false, false, false]
  | false, false, true, true => .p5 sigmaEven3210 ![true, true, true]
  | false, false, true, false => .p7 sigmaEven0123 ![true, false, false, false]
  | false, false, false, true => .p7 sigmaEven1032 ![false, true, true, true]
  | false, false, false, false => .p5 sigmaEven2301 ![false, false, false]

private theorem r2_P7_s2301 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven2301 s) = (r2TargetP7_s2301 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s2301, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s3021 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3021 ![true, true, true]
  | true, true, true, false => .p7 sigmaEven1203 ![true, false, false, false]
  | true, true, false, true => .p7 sigmaEven2130 ![false, true, true, true]
  | true, true, false, false => .p5 sigmaEven0312 ![false, false, false]
  | true, false, true, true => .p7 sigmaEven0312 ![false, true, true, true]
  | true, false, true, false => .p5 sigmaEven2130 ![false, false, false]
  | true, false, false, true => .p5 sigmaEven1203 ![true, true, true]
  | true, false, false, false => .p7 sigmaEven3021 ![true, false, false, false]
  | false, true, true, true => .p7 sigmaEven3021 ![false, true, true, true]
  | false, true, true, false => .p5 sigmaEven1203 ![false, false, false]
  | false, true, false, true => .p5 sigmaEven2130 ![true, true, true]
  | false, true, false, false => .p7 sigmaEven0312 ![true, false, false, false]
  | false, false, true, true => .p5 sigmaEven0312 ![true, true, true]
  | false, false, true, false => .p7 sigmaEven2130 ![true, false, false, false]
  | false, false, false, true => .p7 sigmaEven1203 ![false, true, true, true]
  | false, false, false, false => .p5 sigmaEven3021 ![false, false, false]

private theorem r2_P7_s3021 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven3021 s) = (r2TargetP7_s3021 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s3021, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s3102 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven0231 ![true, false, true]
  | true, true, true, false => .p7 sigmaEven1320 ![true, true, false, true]
  | true, true, false, true => .p7 sigmaEven3102 ![true, true, false, true]
  | true, true, false, false => .p5 sigmaEven2013 ![true, false, true]
  | true, false, true, true => .p7 sigmaEven2013 ![false, false, true, false]
  | true, false, true, false => .p5 sigmaEven3102 ![false, true, false]
  | true, false, false, true => .p5 sigmaEven1320 ![false, true, false]
  | true, false, false, false => .p7 sigmaEven0231 ![false, false, true, false]
  | false, true, true, true => .p7 sigmaEven0231 ![true, true, false, true]
  | false, true, true, false => .p5 sigmaEven1320 ![true, false, true]
  | false, true, false, true => .p5 sigmaEven3102 ![true, false, true]
  | false, true, false, false => .p7 sigmaEven2013 ![true, true, false, true]
  | false, false, true, true => .p5 sigmaEven2013 ![false, true, false]
  | false, false, true, false => .p7 sigmaEven3102 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven1320 ![false, false, true, false]
  | false, false, false, false => .p5 sigmaEven0231 ![false, true, false]

private theorem r2_P7_s3102 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven3102 s) = (r2TargetP7_s3102 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s3102, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r2TargetP7_s3210 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven2301 ![false, true, true]
  | true, true, true, false => .p7 sigmaEven1032 ![true, false, true, true]
  | true, true, false, true => .p7 sigmaEven0123 ![false, true, false, false]
  | true, true, false, false => .p5 sigmaEven3210 ![true, false, false]
  | true, false, true, true => .p7 sigmaEven3210 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven0123 ![false, true, true]
  | true, false, false, true => .p5 sigmaEven1032 ![true, false, false]
  | true, false, false, false => .p7 sigmaEven2301 ![false, true, false, false]
  | false, true, true, true => .p7 sigmaEven2301 ![true, false, true, true]
  | false, true, true, false => .p5 sigmaEven1032 ![false, true, true]
  | false, true, false, true => .p5 sigmaEven0123 ![true, false, false]
  | false, true, false, false => .p7 sigmaEven3210 ![false, true, false, false]
  | false, false, true, true => .p5 sigmaEven3210 ![false, true, true]
  | false, false, true, false => .p7 sigmaEven0123 ![true, false, true, true]
  | false, false, false, true => .p7 sigmaEven1032 ![false, true, false, false]
  | false, false, false, false => .p5 sigmaEven2301 ![true, false, false]

private theorem r2_P7_s3210 (s : Fin 4 → Bool) :
    r2_120 (vertP7 sigmaEven3210 s) = (r2TargetP7_s3210 s).eval := by
  ext k
  rw [r2_120_apply]
  fin_cases k
  all_goals cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r2TargetP7_s3210, delta2_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro, vertP2_apply,
    vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff,
    h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r2_P1_mem (c : CodiceVentiquattro) :
    r2_120 (vertP1 c) ∈ centoventiVertici := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  · change r2_120 (vertP1
      (codiceVentiquattro 0 1 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_01 si sj]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP1
      (codiceVentiquattro 0 2 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_02 si sj]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP1
      (codiceVentiquattro 0 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_03 si sj]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP1
      (codiceVentiquattro 1 2 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_12 si sj]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP1
      (codiceVentiquattro 1 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_13 si sj]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP1
      (codiceVentiquattro 2 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r2_P1_23 si sj]; exact VertexCode120.eval_mem _

private theorem r2_P2_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r2_120 (vertP2 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r2_120 (vertP2 0 s) ∈ centoventiVertici
    rw [r2_P2_i0 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP2 1 s) ∈ centoventiVertici
    rw [r2_P2_i1 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP2 2 s) ∈ centoventiVertici
    rw [r2_P2_i2 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP2 3 s) ∈ centoventiVertici
    rw [r2_P2_i3 s]; exact VertexCode120.eval_mem _

private theorem r2_P3_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r2_120 (vertP3 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r2_120 (vertP3 0 s) ∈ centoventiVertici
    rw [r2_P3_i0 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP3 1 s) ∈ centoventiVertici
    rw [r2_P3_i1 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP3 2 s) ∈ centoventiVertici
    rw [r2_P3_i2 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP3 3 s) ∈ centoventiVertici
    rw [r2_P3_i3 s]; exact VertexCode120.eval_mem _

private theorem r2_P4_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r2_120 (vertP4 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r2_120 (vertP4 0 s) ∈ centoventiVertici
    rw [r2_P4_i0 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP4 1 s) ∈ centoventiVertici
    rw [r2_P4_i1 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP4 2 s) ∈ centoventiVertici
    rw [r2_P4_i2 s]; exact VertexCode120.eval_mem _
  · change r2_120 (vertP4 3 s) ∈ centoventiVertici
    rw [r2_P4_i3 s]; exact VertexCode120.eval_mem _

private theorem r2_P5_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : r2_120 (vertP5 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r2_P5_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r2_P5_s3210 s]; exact VertexCode120.eval_mem _

private theorem r2_P6_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : r2_120 (vertP6 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r2_P6_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r2_P6_s3210 s]; exact VertexCode120.eval_mem _

private theorem r2_P7_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : r2_120 (vertP7 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r2_P7_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r2_P7_s3210 s]; exact VertexCode120.eval_mem _

private theorem r2_mem120 {v : E4} (hv : v ∈ centoventiVertici) :
    r2_120 v ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
      ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact r2_P1_mem c
  · exact r2_P2_mem p.1 p.2
  · exact r2_P3_mem p.1 p.2
  · exact r2_P4_mem p.1 p.2
  · exact r2_P5_mem p.1 p.2
  · exact r2_P6_mem p.1 p.2
  · exact r2_P7_mem p.1 p.2

private theorem r2_image_vertices120 :
    (r2_120 : E4 → E4) '' (centoventiVertici : Set E4) =
      (centoventiVertici : Set E4) := by
  have hfin : Finset.image (r2_120 : E4 → E4) centoventiVertici =
      centoventiVertici := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact r2_mem120 hu
    · rw [Finset.card_image_of_injective _ r2_120.injective]
  rw [← Finset.coe_image, hfin]

theorem r2_120_isSymmetry : centoventi.isSymmetry r2_120 := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (r2_120 : E4 → E4) ''
        convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((r2_120 : E4 → E4) ''
        ((centoventi.vertices : Finset E4) : Set E4)) := by
          exact r2_120.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) := by
      rw [show ((centoventi.vertices : Finset E4) : Set E4) =
          (centoventiVertici : Set E4) by rfl, r2_image_vertices120]

private def r0TargetP1_01 : Bool → Bool → VertexCode120
  | true, true => .p6 sigmaEven2301 ![true, true, true]
  | true, false => .p5 sigmaEven2013 ![true, false, true]
  | false, true => .p5 sigmaEven2013 ![false, true, false]
  | false, false => .p6 sigmaEven2301 ![false, false, false]

private theorem r0_P1_01 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 0 1 (by omega) si sj)) =
      (r0TargetP1_01 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_01, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP1_02 : Bool → Bool → VertexCode120
  | true, true => .p7 sigmaEven1032 ![true, true, true, true]
  | true, false => .p7 sigmaEven1032 ![true, true, true, false]
  | false, true => .p7 sigmaEven1032 ![false, false, false, true]
  | false, false => .p7 sigmaEven1032 ![false, false, false, false]

private theorem r0_P1_02 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 0 2 (by omega) si sj)) =
      (r0TargetP1_02 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_02, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP1_03 : Bool → Bool → VertexCode120
  | true, true => .p5 sigmaEven2130 ![false, true, true]
  | true, false => .p6 sigmaEven2013 ![false, true, true]
  | false, true => .p6 sigmaEven2013 ![true, false, false]
  | false, false => .p5 sigmaEven2130 ![true, false, false]

private theorem r0_P1_03 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 0 3 (by omega) si sj)) =
      (r0TargetP1_03 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_03, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP1_12 : Bool → Bool → VertexCode120
  | true, true => .p7 sigmaEven0312 ![true, false, true, true]
  | true, false => .p7 sigmaEven0312 ![true, false, true, false]
  | false, true => .p7 sigmaEven0312 ![false, true, false, true]
  | false, false => .p7 sigmaEven0312 ![false, true, false, false]

private theorem r0_P1_12 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 1 2 (by omega) si sj)) =
      (r0TargetP1_12 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_12, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP1_13 : Bool → Bool → VertexCode120
  | true, true => .p6 sigmaEven2130 ![true, false, true]
  | true, false => .p5 sigmaEven2301 ![false, false, true]
  | false, true => .p5 sigmaEven2301 ![true, true, false]
  | false, false => .p6 sigmaEven2130 ![false, true, false]

private theorem r0_P1_13 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 1 3 (by omega) si sj)) =
      (r0TargetP1_13 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_13, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP1_23 : Bool → Bool → VertexCode120
  | true, true => .p7 sigmaEven3102 ![false, false, true, true]
  | true, false => .p7 sigmaEven3102 ![true, true, false, true]
  | false, true => .p7 sigmaEven3102 ![false, false, true, false]
  | false, false => .p7 sigmaEven3102 ![true, true, false, false]

private theorem r0_P1_23 (si sj : Bool) :
    r0_120 (vertP1 (codiceVentiquattro 2 3 (by omega) si sj)) =
      (r0TargetP1_23 si sj).eval := by
  cases si <;> cases sj
  all_goals ext k
  all_goals rw [r0_120_apply]
  all_goals fin_cases k
  all_goals simp [r0TargetP1_23, delta0_120, VertexCode120.eval,
    vertP1, vertVentiquattro, segnoVentiquattro,
    vertP2_apply, vertP3_apply, vertP4_apply, vertP5_apply, vertP6_apply,
    vertP7_apply, base5, base6, base7, segnoZeroTesta, segnoPieno,
    sqrt_five_eq_aureo, sigmaEven0123, sigmaEven0231,
    sigmaEven0312, sigmaEven1032, sigmaEven1203, sigmaEven1320,
    sigmaEven2013, sigmaEven2130, sigmaEven2301, sigmaEven3021,
    sigmaEven3102, sigmaEven3210, Equiv.swap_apply_def, Fin.ext_iff]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private def r0TargetP2_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 0 ![true, true, true, true]
  | true, true, true, false => .p7 sigmaEven0231 ![true, true, true, true]
  | true, true, false, true => .p2 0 ![true, true, false, true]
  | true, true, false, false => .p7 sigmaEven0231 ![true, false, true, true]
  | true, false, true, true => .p7 sigmaEven1203 ![false, true, true, true]
  | true, false, true, false => .p5 sigmaEven0123 ![true, true, true]
  | true, false, false, true => .p7 sigmaEven1203 ![false, false, true, true]
  | true, false, false, false => .p5 sigmaEven0123 ![true, false, true]
  | false, true, true, true => .p5 sigmaEven0123 ![false, true, false]
  | false, true, true, false => .p7 sigmaEven1203 ![true, true, false, false]
  | false, true, false, true => .p5 sigmaEven0123 ![false, false, false]
  | false, true, false, false => .p7 sigmaEven1203 ![true, false, false, false]
  | false, false, true, true => .p7 sigmaEven0231 ![false, true, false, false]
  | false, false, true, false => .p2 0 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven0231 ![false, false, false, false]
  | false, false, false, false => .p2 0 ![false, false, false, false]

private theorem r0_P2_i0_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP2 0 s) = (r0TargetP2_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i0_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP2 0 s) = (r0TargetP2_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i0 (s : Fin 4 → Bool) :
    r0_120 (vertP2 0 s) = (r0TargetP2_i0 s).eval := by
  cases h0 : s 0
  · exact r0_P2_i0_false s h0
  · exact r0_P2_i0_true s h0

private def r0TargetP2_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven3210 ![false, true, true, true]
  | true, true, true, false => .p5 sigmaEven3021 ![true, true, true]
  | true, true, false, true => .p7 sigmaEven3210 ![false, false, true, true]
  | true, true, false, false => .p5 sigmaEven3021 ![true, false, true]
  | true, false, true, true => .p7 sigmaEven0231 ![true, true, true, false]
  | true, false, true, false => .p2 3 ![false, false, true, true]
  | true, false, false, true => .p7 sigmaEven0231 ![true, false, true, false]
  | true, false, false, false => .p2 3 ![false, false, false, true]
  | false, true, true, true => .p2 3 ![true, true, true, false]
  | false, true, true, false => .p7 sigmaEven0231 ![false, true, false, true]
  | false, true, false, true => .p2 3 ![true, true, false, false]
  | false, true, false, false => .p7 sigmaEven0231 ![false, false, false, true]
  | false, false, true, true => .p5 sigmaEven3021 ![false, true, false]
  | false, false, true, false => .p7 sigmaEven3210 ![true, true, false, false]
  | false, false, false, true => .p5 sigmaEven3021 ![false, false, false]
  | false, false, false, false => .p7 sigmaEven3210 ![true, false, false, false]

private theorem r0_P2_i1_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP2 1 s) = (r0TargetP2_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i1_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP2 1 s) = (r0TargetP2_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i1 (s : Fin 4 → Bool) :
    r0_120 (vertP2 1 s) = (r0TargetP2_i1 s).eval := by
  cases h0 : s 0
  · exact r0_P2_i1_false s h0
  · exact r0_P2_i1_true s h0

private def r0TargetP2_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p6 sigmaEven3102 ![true, true, true]
  | true, true, true, false => .p6 sigmaEven0312 ![true, true, true]
  | true, true, false, true => .p6 sigmaEven3102 ![true, true, false]
  | true, true, false, false => .p6 sigmaEven0312 ![true, true, false]
  | true, false, true, true => .p2 2 ![true, false, true, true]
  | true, false, true, false => .p6 sigmaEven1032 ![false, true, true]
  | true, false, false, true => .p2 2 ![true, false, false, true]
  | true, false, false, false => .p6 sigmaEven1032 ![false, true, false]
  | false, true, true, true => .p6 sigmaEven1032 ![true, false, true]
  | false, true, true, false => .p2 2 ![false, true, true, false]
  | false, true, false, true => .p6 sigmaEven1032 ![true, false, false]
  | false, true, false, false => .p2 2 ![false, true, false, false]
  | false, false, true, true => .p6 sigmaEven0312 ![false, false, true]
  | false, false, true, false => .p6 sigmaEven3102 ![false, false, true]
  | false, false, false, true => .p6 sigmaEven0312 ![false, false, false]
  | false, false, false, false => .p6 sigmaEven3102 ![false, false, false]

private theorem r0_P2_i2_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP2 2 s) = (r0TargetP2_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i2_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP2 2 s) = (r0TargetP2_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i2 (s : Fin 4 → Bool) :
    r0_120 (vertP2 2 s) = (r0TargetP2_i2 s).eval := by
  cases h0 : s 0
  · exact r0_P2_i2_false s h0
  · exact r0_P2_i2_true s h0

private def r0TargetP2_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven1320 ![false, true, true]
  | true, true, true, false => .p2 1 ![false, true, true, true]
  | true, true, false, true => .p5 sigmaEven1320 ![false, false, true]
  | true, true, false, false => .p2 1 ![false, true, false, true]
  | true, false, true, true => .p7 sigmaEven3210 ![true, true, false, true]
  | true, false, true, false => .p7 sigmaEven1203 ![true, true, false, true]
  | true, false, false, true => .p7 sigmaEven3210 ![true, false, false, true]
  | true, false, false, false => .p7 sigmaEven1203 ![true, false, false, true]
  | false, true, true, true => .p7 sigmaEven1203 ![false, true, true, false]
  | false, true, true, false => .p7 sigmaEven3210 ![false, true, true, false]
  | false, true, false, true => .p7 sigmaEven1203 ![false, false, true, false]
  | false, true, false, false => .p7 sigmaEven3210 ![false, false, true, false]
  | false, false, true, true => .p2 1 ![true, false, true, false]
  | false, false, true, false => .p5 sigmaEven1320 ![true, true, false]
  | false, false, false, true => .p2 1 ![true, false, false, false]
  | false, false, false, false => .p5 sigmaEven1320 ![true, false, false]

private theorem r0_P2_i3_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP2 3 s) = (r0TargetP2_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i3_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP2 3 s) = (r0TargetP2_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP2_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P2_i3 (s : Fin 4 → Bool) :
    r0_120 (vertP2 3 s) = (r0TargetP2_i3 s).eval := by
  cases h0 : s 0
  · exact r0_P2_i3_false s h0
  · exact r0_P2_i3_true s h0

private def r0TargetP3_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven1320 ![true, false, true, true]
  | true, true, true, false => .p6 sigmaEven3021 ![false, true, true]
  | true, true, false, true => .p7 sigmaEven1320 ![true, false, false, true]
  | true, true, false, false => .p6 sigmaEven3021 ![false, false, true]
  | true, false, true, true => .p7 sigmaEven3021 ![true, true, true, false]
  | true, false, true, false => .p3 1 ![false, false, true, true]
  | true, false, false, true => .p7 sigmaEven3021 ![true, true, false, false]
  | true, false, false, false => .p3 1 ![false, false, false, true]
  | false, true, true, true => .p3 1 ![true, true, true, false]
  | false, true, true, false => .p7 sigmaEven3021 ![false, false, true, true]
  | false, true, false, true => .p3 1 ![true, true, false, false]
  | false, true, false, false => .p7 sigmaEven3021 ![false, false, false, true]
  | false, false, true, true => .p6 sigmaEven3021 ![true, true, false]
  | false, false, true, false => .p7 sigmaEven1320 ![false, true, true, false]
  | false, false, false, true => .p6 sigmaEven3021 ![true, false, false]
  | false, false, false, false => .p7 sigmaEven1320 ![false, true, false, false]

private theorem r0_P3_i0_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP3 0 s) = (r0TargetP3_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i0_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP3 0 s) = (r0TargetP3_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i0 (s : Fin 4 → Bool) :
    r0_120 (vertP3 0 s) = (r0TargetP3_i0 s).eval := by
  cases h0 : s 0
  · exact r0_P3_i0_false s h0
  · exact r0_P3_i0_true s h0

private def r0TargetP3_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p6 sigmaEven1320 ![true, true, true]
  | true, true, true, false => .p3 0 ![false, true, true, true]
  | true, true, false, true => .p6 sigmaEven1320 ![true, false, true]
  | true, true, false, false => .p3 0 ![false, true, false, true]
  | true, false, true, true => .p7 sigmaEven1320 ![false, true, true, true]
  | true, false, true, false => .p7 sigmaEven0123 ![false, true, true, true]
  | true, false, false, true => .p7 sigmaEven1320 ![false, true, false, true]
  | true, false, false, false => .p7 sigmaEven0123 ![false, true, false, true]
  | false, true, true, true => .p7 sigmaEven0123 ![true, false, true, false]
  | false, true, true, false => .p7 sigmaEven1320 ![true, false, true, false]
  | false, true, false, true => .p7 sigmaEven0123 ![true, false, false, false]
  | false, true, false, false => .p7 sigmaEven1320 ![true, false, false, false]
  | false, false, true, true => .p3 0 ![true, false, true, false]
  | false, false, true, false => .p6 sigmaEven1320 ![false, true, false]
  | false, false, false, true => .p3 0 ![true, false, false, false]
  | false, false, false, false => .p6 sigmaEven1320 ![false, false, false]

private theorem r0_P3_i1_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP3 1 s) = (r0TargetP3_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i1_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP3 1 s) = (r0TargetP3_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i1 (s : Fin 4 → Bool) :
    r0_120 (vertP3 1 s) = (r0TargetP3_i1 s).eval := by
  cases h0 : s 0
  · exact r0_P3_i1_false s h0
  · exact r0_P3_i1_true s h0

private def r0TargetP3_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3210 ![true, true, true]
  | true, true, true, false => .p5 sigmaEven0231 ![true, true, true]
  | true, true, false, true => .p5 sigmaEven3210 ![false, true, true]
  | true, true, false, false => .p5 sigmaEven0231 ![false, true, true]
  | true, false, true, true => .p3 2 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven1203 ![true, false, true]
  | true, false, false, true => .p3 2 ![true, false, false, true]
  | true, false, false, false => .p5 sigmaEven1203 ![false, false, true]
  | false, true, true, true => .p5 sigmaEven1203 ![true, true, false]
  | false, true, true, false => .p3 2 ![false, true, true, false]
  | false, true, false, true => .p5 sigmaEven1203 ![false, true, false]
  | false, true, false, false => .p3 2 ![false, true, false, false]
  | false, false, true, true => .p5 sigmaEven0231 ![true, false, false]
  | false, false, true, false => .p5 sigmaEven3210 ![true, false, false]
  | false, false, false, true => .p5 sigmaEven0231 ![false, false, false]
  | false, false, false, false => .p5 sigmaEven3210 ![false, false, false]

private theorem r0_P3_i2_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP3 2 s) = (r0TargetP3_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i2_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP3 2 s) = (r0TargetP3_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i2 (s : Fin 4 → Bool) :
    r0_120 (vertP3 2 s) = (r0TargetP3_i2 s).eval := by
  cases h0 : s 0
  · exact r0_P3_i2_false s h0
  · exact r0_P3_i2_true s h0

private def r0TargetP3_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p3 3 ![true, true, true, true]
  | true, true, true, false => .p7 sigmaEven3021 ![true, true, true, true]
  | true, true, false, true => .p3 3 ![true, true, false, true]
  | true, true, false, false => .p7 sigmaEven3021 ![true, true, false, true]
  | true, false, true, true => .p7 sigmaEven0123 ![true, false, true, true]
  | true, false, true, false => .p6 sigmaEven0123 ![false, true, true]
  | true, false, false, true => .p7 sigmaEven0123 ![true, false, false, true]
  | true, false, false, false => .p6 sigmaEven0123 ![false, false, true]
  | false, true, true, true => .p6 sigmaEven0123 ![true, true, false]
  | false, true, true, false => .p7 sigmaEven0123 ![false, true, true, false]
  | false, true, false, true => .p6 sigmaEven0123 ![true, false, false]
  | false, true, false, false => .p7 sigmaEven0123 ![false, true, false, false]
  | false, false, true, true => .p7 sigmaEven3021 ![false, false, true, false]
  | false, false, true, false => .p3 3 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven3021 ![false, false, false, false]
  | false, false, false, false => .p3 3 ![false, false, false, false]

private theorem r0_P3_i3_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP3 3 s) = (r0TargetP3_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i3_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP3 3 s) = (r0TargetP3_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP3_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P3_i3 (s : Fin 4 → Bool) :
    r0_120 (vertP3 3 s) = (r0TargetP3_i3 s).eval := by
  cases h0 : s 0
  · exact r0_P3_i3_false s h0
  · exact r0_P3_i3_true s h0

private def r0TargetP4_i0 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven2130 ![true, true, true, true]
  | true, true, true, false => .p7 sigmaEven2013 ![true, true, true, true]
  | true, true, false, true => .p7 sigmaEven2130 ![false, true, true, true]
  | true, true, false, false => .p7 sigmaEven2013 ![false, true, true, true]
  | true, false, true, true => .p6 sigmaEven1203 ![true, true, true]
  | true, false, true, false => .p4 3 ![true, true, true, true]
  | true, false, false, true => .p6 sigmaEven1203 ![false, true, true]
  | true, false, false, false => .p4 3 ![true, true, false, true]
  | false, true, true, true => .p4 3 ![false, false, true, false]
  | false, true, true, false => .p6 sigmaEven1203 ![true, false, false]
  | false, true, false, true => .p4 3 ![false, false, false, false]
  | false, true, false, false => .p6 sigmaEven1203 ![false, false, false]
  | false, false, true, true => .p7 sigmaEven2013 ![true, false, false, false]
  | false, false, true, false => .p7 sigmaEven2130 ![true, false, false, false]
  | false, false, false, true => .p7 sigmaEven2013 ![false, false, false, false]
  | false, false, false, false => .p7 sigmaEven2130 ![false, false, false, false]

private theorem r0_P4_i0_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP4 0 s) = (r0TargetP4_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i0_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP4 0 s) = (r0TargetP4_i0 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i0, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i0 (s : Fin 4 → Bool) :
    r0_120 (vertP4 0 s) = (r0TargetP4_i0 s).eval := by
  cases h0 : s 0
  · exact r0_P4_i0_false s h0
  · exact r0_P4_i0_true s h0

private def r0TargetP4_i1 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven2301 ![true, false, true, true]
  | true, true, true, false => .p4 1 ![true, true, true, false]
  | true, true, false, true => .p7 sigmaEven2301 ![false, false, true, true]
  | true, true, false, false => .p4 1 ![true, true, false, false]
  | true, false, true, true => .p6 sigmaEven0231 ![true, true, false]
  | true, false, true, false => .p7 sigmaEven2013 ![true, false, false, true]
  | true, false, false, true => .p6 sigmaEven0231 ![false, true, false]
  | true, false, false, false => .p7 sigmaEven2013 ![false, false, false, true]
  | false, true, true, true => .p7 sigmaEven2013 ![true, true, true, false]
  | false, true, true, false => .p6 sigmaEven0231 ![true, false, true]
  | false, true, false, true => .p7 sigmaEven2013 ![false, true, true, false]
  | false, true, false, false => .p6 sigmaEven0231 ![false, false, true]
  | false, false, true, true => .p4 1 ![false, false, true, true]
  | false, false, true, false => .p7 sigmaEven2301 ![true, true, false, false]
  | false, false, false, true => .p4 1 ![false, false, false, true]
  | false, false, false, false => .p7 sigmaEven2301 ![false, true, false, false]

private theorem r0_P4_i1_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP4 1 s) = (r0TargetP4_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i1_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP4 1 s) = (r0TargetP4_i1 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i1, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i1 (s : Fin 4 → Bool) :
    r0_120 (vertP4 1 s) = (r0TargetP4_i1 s).eval := by
  cases h0 : s 0
  · exact r0_P4_i1_false s h0
  · exact r0_P4_i1_true s h0

private def r0TargetP4_i2 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven3102 ![true, true, true]
  | true, true, true, false => .p5 sigmaEven0312 ![true, true, true]
  | true, true, false, true => .p5 sigmaEven3102 ![true, true, false]
  | true, true, false, false => .p5 sigmaEven0312 ![true, true, false]
  | true, false, true, true => .p4 2 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven1032 ![false, true, true]
  | true, false, false, true => .p4 2 ![true, false, false, true]
  | true, false, false, false => .p5 sigmaEven1032 ![false, true, false]
  | false, true, true, true => .p5 sigmaEven1032 ![true, false, true]
  | false, true, true, false => .p4 2 ![false, true, true, false]
  | false, true, false, true => .p5 sigmaEven1032 ![true, false, false]
  | false, true, false, false => .p4 2 ![false, true, false, false]
  | false, false, true, true => .p5 sigmaEven0312 ![false, false, true]
  | false, false, true, false => .p5 sigmaEven3102 ![false, false, true]
  | false, false, false, true => .p5 sigmaEven0312 ![false, false, false]
  | false, false, false, false => .p5 sigmaEven3102 ![false, false, false]

private theorem r0_P4_i2_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP4 2 s) = (r0TargetP4_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i2_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP4 2 s) = (r0TargetP4_i2 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i2, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i2 (s : Fin 4 → Bool) :
    r0_120 (vertP4 2 s) = (r0TargetP4_i2 s).eval := by
  cases h0 : s 0
  · exact r0_P4_i2_false s h0
  · exact r0_P4_i2_true s h0

private def r0TargetP4_i3 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 0 ![true, false, true, false]
  | true, true, true, false => .p7 sigmaEven2301 ![true, true, false, true]
  | true, true, false, true => .p4 0 ![true, false, false, false]
  | true, true, false, false => .p7 sigmaEven2301 ![false, true, false, true]
  | true, false, true, true => .p6 sigmaEven3210 ![true, false, true]
  | true, false, true, false => .p7 sigmaEven2130 ![true, true, true, false]
  | true, false, false, true => .p6 sigmaEven3210 ![false, false, true]
  | true, false, false, false => .p7 sigmaEven2130 ![false, true, true, false]
  | false, true, true, true => .p7 sigmaEven2130 ![true, false, false, true]
  | false, true, true, false => .p6 sigmaEven3210 ![true, true, false]
  | false, true, false, true => .p7 sigmaEven2130 ![false, false, false, true]
  | false, true, false, false => .p6 sigmaEven3210 ![false, true, false]
  | false, false, true, true => .p7 sigmaEven2301 ![true, false, true, false]
  | false, false, true, false => .p4 0 ![false, true, true, true]
  | false, false, false, true => .p7 sigmaEven2301 ![false, false, true, false]
  | false, false, false, false => .p4 0 ![false, true, false, true]

private theorem r0_P4_i3_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP4 3 s) = (r0TargetP4_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i3_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP4 3 s) = (r0TargetP4_i3 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP4_i3, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P4_i3 (s : Fin 4 → Bool) :
    r0_120 (vertP4 3 s) = (r0TargetP4_i3 s).eval := by
  cases h0 : s 0
  · exact r0_P4_i3_false s h0
  · exact r0_P4_i3_true s h0

private def r0TargetP5_s0123 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p2 0 ![true, false, true, false]
  | true, true, false => .p7 sigmaEven3210 ![true, true, true, false]
  | true, false, true => .p2 0 ![true, false, false, false]
  | true, false, false => .p7 sigmaEven3210 ![true, false, true, false]
  | false, true, true => .p7 sigmaEven3210 ![false, true, false, true]
  | false, true, false => .p2 0 ![false, true, true, true]
  | false, false, true => .p7 sigmaEven3210 ![false, false, false, true]
  | false, false, false => .p2 0 ![false, true, false, true]

private theorem r0_P5_s0123_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven0123 s) = (r0TargetP5_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0123_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven0123 s) = (r0TargetP5_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0123 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven0123 s) = (r0TargetP5_s0123 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s0123_false s h0
  · exact r0_P5_s0123_true s h0

private def r0TargetP5_s0231 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p3 2 ![true, true, true, false]
  | true, true, false => .p5 sigmaEven0231 ![true, true, false]
  | true, false, true => .p5 sigmaEven0231 ![true, false, true]
  | true, false, false => .p3 2 ![false, false, true, true]
  | false, true, true => .p3 2 ![true, true, false, false]
  | false, true, false => .p5 sigmaEven0231 ![false, true, false]
  | false, false, true => .p5 sigmaEven0231 ![false, false, true]
  | false, false, false => .p3 2 ![false, false, false, true]

private theorem r0_P5_s0231_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven0231 s) = (r0TargetP5_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0231_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven0231 s) = (r0TargetP5_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0231 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven0231 s) = (r0TargetP5_s0231 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s0231_false s h0
  · exact r0_P5_s0231_true s h0

private def r0TargetP5_s0312 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p4 2 ![true, true, true, false]
  | true, true, false => .p4 2 ![true, true, false, false]
  | true, false, true => .p5 sigmaEven0312 ![true, false, true]
  | true, false, false => .p5 sigmaEven0312 ![true, false, false]
  | false, true, true => .p5 sigmaEven0312 ![false, true, true]
  | false, true, false => .p5 sigmaEven0312 ![false, true, false]
  | false, false, true => .p4 2 ![false, false, true, true]
  | false, false, false => .p4 2 ![false, false, false, true]

private theorem r0_P5_s0312_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven0312 s) = (r0TargetP5_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0312_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven0312 s) = (r0TargetP5_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s0312 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven0312 s) = (r0TargetP5_s0312 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s0312_false s h0
  · exact r0_P5_s0312_true s h0

private def r0TargetP5_s1032 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p5 sigmaEven3102 ![false, true, true]
  | true, true, false => .p5 sigmaEven3102 ![false, true, false]
  | true, false, true => .p4 2 ![false, true, true, true]
  | true, false, false => .p4 2 ![false, true, false, true]
  | false, true, true => .p4 2 ![true, false, true, false]
  | false, true, false => .p4 2 ![true, false, false, false]
  | false, false, true => .p5 sigmaEven3102 ![true, false, true]
  | false, false, false => .p5 sigmaEven3102 ![true, false, false]

private theorem r0_P5_s1032_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven1032 s) = (r0TargetP5_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1032_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven1032 s) = (r0TargetP5_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1032 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven1032 s) = (r0TargetP5_s1032 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s1032_false s h0
  · exact r0_P5_s1032_true s h0

private def r0TargetP5_s1203 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p5 sigmaEven3210 ![true, false, true]
  | true, true, false => .p3 2 ![false, true, true, true]
  | true, false, true => .p3 2 ![true, false, true, false]
  | true, false, false => .p5 sigmaEven3210 ![true, true, false]
  | false, true, true => .p5 sigmaEven3210 ![false, false, true]
  | false, true, false => .p3 2 ![false, true, false, true]
  | false, false, true => .p3 2 ![true, false, false, false]
  | false, false, false => .p5 sigmaEven3210 ![false, true, false]

private theorem r0_P5_s1203_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven1203 s) = (r0TargetP5_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1203_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven1203 s) = (r0TargetP5_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1203 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven1203 s) = (r0TargetP5_s1203 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s1203_false s h0
  · exact r0_P5_s1203_true s h0

private def r0TargetP5_s1320 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven1203 ![true, true, true, true]
  | true, true, false => .p2 3 ![false, false, true, false]
  | true, false, true => .p7 sigmaEven1203 ![true, false, true, true]
  | true, false, false => .p2 3 ![false, false, false, false]
  | false, true, true => .p2 3 ![true, true, true, true]
  | false, true, false => .p7 sigmaEven1203 ![false, true, false, false]
  | false, false, true => .p2 3 ![true, true, false, true]
  | false, false, false => .p7 sigmaEven1203 ![false, false, false, false]

private theorem r0_P5_s1320_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven1320 s) = (r0TargetP5_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1320_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven1320 s) = (r0TargetP5_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s1320 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven1320 s) = (r0TargetP5_s1320 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s1320_false s h0
  · exact r0_P5_s1320_true s h0

private def r0TargetP5_s2013 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p5 sigmaEven2130 ![false, false, true]
  | true, true, false => .p6 sigmaEven2301 ![true, false, true]
  | true, false, true => .p1 (codiceVentiquattro 0 1 (by omega) true false)
  | true, false, false => .p6 sigmaEven2130 ![true, true, false]
  | false, true, true => .p6 sigmaEven2130 ![false, false, true]
  | false, true, false => .p1 (codiceVentiquattro 0 1 (by omega) false true)
  | false, false, true => .p6 sigmaEven2301 ![false, true, false]
  | false, false, false => .p5 sigmaEven2130 ![true, true, false]

private theorem r0_P5_s2013_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven2013 s) = (r0TargetP5_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2013_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven2013 s) = (r0TargetP5_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2013 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven2013 s) = (r0TargetP5_s2013 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s2013_false s h0
  · exact r0_P5_s2013_true s h0

private def r0TargetP5_s2130 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2130 ![true, true, true]
  | true, true, false => .p5 sigmaEven2013 ![false, false, false]
  | true, false, true => .p6 sigmaEven2013 ![true, true, true]
  | true, false, false => .p1 (codiceVentiquattro 0 3 (by omega) false false)
  | false, true, true => .p1 (codiceVentiquattro 0 3 (by omega) true true)
  | false, true, false => .p6 sigmaEven2013 ![false, false, false]
  | false, false, true => .p5 sigmaEven2013 ![true, true, true]
  | false, false, false => .p6 sigmaEven2130 ![false, false, false]

private theorem r0_P5_s2130_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven2130 s) = (r0TargetP5_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2130_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven2130 s) = (r0TargetP5_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2130 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven2130 s) = (r0TargetP5_s2130 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s2130_false s h0
  · exact r0_P5_s2130_true s h0

private def r0TargetP5_s2301 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven2301 ![false, true, true]
  | true, true, false => .p1 (codiceVentiquattro 1 3 (by omega) false true)
  | true, false, true => .p6 sigmaEven2013 ![true, true, false]
  | true, false, false => .p5 sigmaEven2301 ![true, false, false]
  | false, true, true => .p5 sigmaEven2301 ![false, true, true]
  | false, true, false => .p6 sigmaEven2013 ![false, false, true]
  | false, false, true => .p1 (codiceVentiquattro 1 3 (by omega) true false)
  | false, false, false => .p6 sigmaEven2301 ![true, false, false]

private theorem r0_P5_s2301_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven2301 s) = (r0TargetP5_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2301_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven2301 s) = (r0TargetP5_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s2301 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven2301 s) = (r0TargetP5_s2301 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s2301_false s h0
  · exact r0_P5_s2301_true s h0

private def r0TargetP5_s3021 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p2 1 ![true, true, true, false]
  | true, true, false => .p7 sigmaEven0231 ![false, true, true, false]
  | true, false, true => .p2 1 ![true, true, false, false]
  | true, false, false => .p7 sigmaEven0231 ![false, false, true, false]
  | false, true, true => .p7 sigmaEven0231 ![true, true, false, true]
  | false, true, false => .p2 1 ![false, false, true, true]
  | false, false, true => .p7 sigmaEven0231 ![true, false, false, true]
  | false, false, false => .p2 1 ![false, false, false, true]

private theorem r0_P5_s3021_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven3021 s) = (r0TargetP5_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3021_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven3021 s) = (r0TargetP5_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3021 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven3021 s) = (r0TargetP5_s3021 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s3021_false s h0
  · exact r0_P5_s3021_true s h0

private def r0TargetP5_s3102 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p4 2 ![true, true, true, true]
  | true, true, false => .p4 2 ![true, true, false, true]
  | true, false, true => .p5 sigmaEven1032 ![false, false, true]
  | true, false, false => .p5 sigmaEven1032 ![false, false, false]
  | false, true, true => .p5 sigmaEven1032 ![true, true, true]
  | false, true, false => .p5 sigmaEven1032 ![true, true, false]
  | false, false, true => .p4 2 ![false, false, true, false]
  | false, false, false => .p4 2 ![false, false, false, false]

private theorem r0_P5_s3102_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven3102 s) = (r0TargetP5_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3102_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven3102 s) = (r0TargetP5_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3102 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven3102 s) = (r0TargetP5_s3102 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s3102_false s h0
  · exact r0_P5_s3102_true s h0

private def r0TargetP5_s3210 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p3 2 ![true, true, true, true]
  | true, true, false => .p5 sigmaEven1203 ![true, false, false]
  | true, false, true => .p5 sigmaEven1203 ![true, true, true]
  | true, false, false => .p3 2 ![false, false, true, false]
  | false, true, true => .p3 2 ![true, true, false, true]
  | false, true, false => .p5 sigmaEven1203 ![false, false, false]
  | false, false, true => .p5 sigmaEven1203 ![false, true, true]
  | false, false, false => .p3 2 ![false, false, false, false]

private theorem r0_P5_s3210_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP5 sigmaEven3210 s) = (r0TargetP5_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3210_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP5 sigmaEven3210 s) = (r0TargetP5_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP5_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P5_s3210 (s : Fin 3 → Bool) :
    r0_120 (vertP5 sigmaEven3210 s) = (r0TargetP5_s3210 s).eval := by
  cases h0 : s 0
  · exact r0_P5_s3210_false s h0
  · exact r0_P5_s3210_true s h0

private def r0TargetP6_s0123 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven1320 ![false, false, true, true]
  | true, true, false => .p3 3 ![false, true, true, true]
  | true, false, true => .p7 sigmaEven1320 ![false, false, false, true]
  | true, false, false => .p3 3 ![false, true, false, true]
  | false, true, true => .p3 3 ![true, false, true, false]
  | false, true, false => .p7 sigmaEven1320 ![true, true, true, false]
  | false, false, true => .p3 3 ![true, false, false, false]
  | false, false, false => .p7 sigmaEven1320 ![true, true, false, false]

private theorem r0_P6_s0123_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven0123 s) = (r0TargetP6_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0123_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven0123 s) = (r0TargetP6_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0123 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven0123 s) = (r0TargetP6_s0123 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s0123_false s h0
  · exact r0_P6_s0123_true s h0

private def r0TargetP6_s0231 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2130 ![true, true, false, true]
  | true, true, false => .p4 1 ![true, false, true, true]
  | true, false, true => .p4 1 ![false, true, true, false]
  | true, false, false => .p7 sigmaEven2130 ![true, false, true, false]
  | false, true, true => .p7 sigmaEven2130 ![false, true, false, true]
  | false, true, false => .p4 1 ![true, false, false, true]
  | false, false, true => .p4 1 ![false, true, false, false]
  | false, false, false => .p7 sigmaEven2130 ![false, false, true, false]

private theorem r0_P6_s0231_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven0231 s) = (r0TargetP6_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0231_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven0231 s) = (r0TargetP6_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0231 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven0231 s) = (r0TargetP6_s0231 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s0231_false s h0
  · exact r0_P6_s0231_true s h0

private def r0TargetP6_s0312 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p2 2 ![true, true, true, false]
  | true, true, false => .p2 2 ![true, true, false, false]
  | true, false, true => .p6 sigmaEven0312 ![true, false, true]
  | true, false, false => .p6 sigmaEven0312 ![true, false, false]
  | false, true, true => .p6 sigmaEven0312 ![false, true, true]
  | false, true, false => .p6 sigmaEven0312 ![false, true, false]
  | false, false, true => .p2 2 ![false, false, true, true]
  | false, false, false => .p2 2 ![false, false, false, true]

private theorem r0_P6_s0312_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven0312 s) = (r0TargetP6_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0312_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven0312 s) = (r0TargetP6_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s0312 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven0312 s) = (r0TargetP6_s0312 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s0312_false s h0
  · exact r0_P6_s0312_true s h0

private def r0TargetP6_s1032 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p6 sigmaEven3102 ![false, true, true]
  | true, true, false => .p6 sigmaEven3102 ![false, true, false]
  | true, false, true => .p2 2 ![false, true, true, true]
  | true, false, false => .p2 2 ![false, true, false, true]
  | false, true, true => .p2 2 ![true, false, true, false]
  | false, true, false => .p2 2 ![true, false, false, false]
  | false, false, true => .p6 sigmaEven3102 ![true, false, true]
  | false, false, false => .p6 sigmaEven3102 ![true, false, false]

private theorem r0_P6_s1032_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven1032 s) = (r0TargetP6_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1032_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven1032 s) = (r0TargetP6_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1032 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven1032 s) = (r0TargetP6_s1032 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s1032_false s h0
  · exact r0_P6_s1032_true s h0

private def r0TargetP6_s1203 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p4 0 ![true, false, true, true]
  | true, true, false => .p7 sigmaEven2013 ![true, false, true, true]
  | true, false, true => .p7 sigmaEven2013 ![true, true, false, false]
  | true, false, false => .p4 0 ![false, true, true, false]
  | false, true, true => .p4 0 ![true, false, false, true]
  | false, true, false => .p7 sigmaEven2013 ![false, false, true, true]
  | false, false, true => .p7 sigmaEven2013 ![false, true, false, false]
  | false, false, false => .p4 0 ![false, true, false, false]

private theorem r0_P6_s1203_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven1203 s) = (r0TargetP6_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1203_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven1203 s) = (r0TargetP6_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1203 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven1203 s) = (r0TargetP6_s1203 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s1203_false s h0
  · exact r0_P6_s1203_true s h0

private def r0TargetP6_s1320 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p3 1 ![true, true, true, true]
  | true, true, false => .p7 sigmaEven0123 ![false, false, true, false]
  | true, false, true => .p3 1 ![true, true, false, true]
  | true, false, false => .p7 sigmaEven0123 ![false, false, false, false]
  | false, true, true => .p7 sigmaEven0123 ![true, true, true, true]
  | false, true, false => .p3 1 ![false, false, true, false]
  | false, false, true => .p7 sigmaEven0123 ![true, true, false, true]
  | false, false, false => .p3 1 ![false, false, false, false]

private theorem r0_P6_s1320_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven1320 s) = (r0TargetP6_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1320_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven1320 s) = (r0TargetP6_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s1320 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven1320 s) = (r0TargetP6_s1320 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s1320_false s h0
  · exact r0_P6_s1320_true s h0

private def r0TargetP6_s2013 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p5 sigmaEven2130 ![true, false, true]
  | true, true, false => .p5 sigmaEven2301 ![true, false, true]
  | true, false, true => .p6 sigmaEven2301 ![true, true, false]
  | true, false, false => .p1 (codiceVentiquattro 0 3 (by omega) false true)
  | false, true, true => .p1 (codiceVentiquattro 0 3 (by omega) true false)
  | false, true, false => .p6 sigmaEven2301 ![false, false, true]
  | false, false, true => .p5 sigmaEven2301 ![false, true, false]
  | false, false, false => .p5 sigmaEven2130 ![false, true, false]

private theorem r0_P6_s2013_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven2013 s) = (r0TargetP6_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2013_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven2013 s) = (r0TargetP6_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2013 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven2013 s) = (r0TargetP6_s2013 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s2013_false s h0
  · exact r0_P6_s2013_true s h0

private def r0TargetP6_s2130 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p5 sigmaEven2130 ![true, true, true]
  | true, true, false => .p5 sigmaEven2013 ![true, false, false]
  | true, false, true => .p1 (codiceVentiquattro 1 3 (by omega) true true)
  | true, false, false => .p6 sigmaEven2130 ![true, false, false]
  | false, true, true => .p6 sigmaEven2130 ![false, true, true]
  | false, true, false => .p1 (codiceVentiquattro 1 3 (by omega) false false)
  | false, false, true => .p5 sigmaEven2013 ![false, true, true]
  | false, false, false => .p5 sigmaEven2130 ![false, false, false]

private theorem r0_P6_s2130_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven2130 s) = (r0TargetP6_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2130_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven2130 s) = (r0TargetP6_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2130 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven2130 s) = (r0TargetP6_s2130 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s2130_false s h0
  · exact r0_P6_s2130_true s h0

private def r0TargetP6_s2301 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p1 (codiceVentiquattro 0 1 (by omega) true true)
  | true, true, false => .p6 sigmaEven2013 ![true, false, true]
  | true, false, true => .p5 sigmaEven2013 ![true, true, false]
  | true, false, false => .p5 sigmaEven2301 ![false, false, false]
  | false, true, true => .p5 sigmaEven2301 ![true, true, true]
  | false, true, false => .p5 sigmaEven2013 ![false, false, true]
  | false, false, true => .p6 sigmaEven2013 ![false, true, false]
  | false, false, false => .p1 (codiceVentiquattro 0 1 (by omega) false false)

private theorem r0_P6_s2301_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven2301 s) = (r0TargetP6_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2301_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven2301 s) = (r0TargetP6_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s2301 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven2301 s) = (r0TargetP6_s2301 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s2301_false s h0
  · exact r0_P6_s2301_true s h0

private def r0TargetP6_s3021 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven3021 ![false, true, true, true]
  | true, true, false => .p3 0 ![false, false, true, true]
  | true, false, true => .p7 sigmaEven3021 ![false, true, false, true]
  | true, false, false => .p3 0 ![false, false, false, true]
  | false, true, true => .p3 0 ![true, true, true, false]
  | false, true, false => .p7 sigmaEven3021 ![true, false, true, false]
  | false, false, true => .p3 0 ![true, true, false, false]
  | false, false, false => .p7 sigmaEven3021 ![true, false, false, false]

private theorem r0_P6_s3021_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven3021 s) = (r0TargetP6_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3021_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven3021 s) = (r0TargetP6_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3021 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven3021 s) = (r0TargetP6_s3021 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s3021_false s h0
  · exact r0_P6_s3021_true s h0

private def r0TargetP6_s3102 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p2 2 ![true, true, true, true]
  | true, true, false => .p2 2 ![true, true, false, true]
  | true, false, true => .p6 sigmaEven1032 ![false, false, true]
  | true, false, false => .p6 sigmaEven1032 ![false, false, false]
  | false, true, true => .p6 sigmaEven1032 ![true, true, true]
  | false, true, false => .p6 sigmaEven1032 ![true, true, false]
  | false, false, true => .p2 2 ![false, false, true, false]
  | false, false, false => .p2 2 ![false, false, false, false]

private theorem r0_P6_s3102_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven3102 s) = (r0TargetP6_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3102_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven3102 s) = (r0TargetP6_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3102 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven3102 s) = (r0TargetP6_s3102 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s3102_false s h0
  · exact r0_P6_s3102_true s h0

private def r0TargetP6_s3210 (s : Fin 3 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2 with
  | true, true, true => .p7 sigmaEven2301 ![true, true, true, true]
  | true, true, false => .p4 3 ![false, true, true, false]
  | true, false, true => .p4 3 ![true, false, true, true]
  | true, false, false => .p7 sigmaEven2301 ![true, false, false, false]
  | false, true, true => .p7 sigmaEven2301 ![false, true, true, true]
  | false, true, false => .p4 3 ![false, true, false, false]
  | false, false, true => .p4 3 ![true, false, false, true]
  | false, false, false => .p7 sigmaEven2301 ![false, false, false, false]

private theorem r0_P6_s3210_false (s : Fin 3 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP6 sigmaEven3210 s) = (r0TargetP6_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3210_true (s : Fin 3 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP6 sigmaEven3210 s) = (r0TargetP6_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2
  all_goals simp [r0TargetP6_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P6_s3210 (s : Fin 3 → Bool) :
    r0_120 (vertP6 sigmaEven3210 s) = (r0TargetP6_s3210 s).eval := by
  cases h0 : s 0
  · exact r0_P6_s3210_false s h0
  · exact r0_P6_s3210_true s h0

private def r0TargetP7_s0123 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p6 sigmaEven1320 ![false, true, true]
  | true, true, true, false => .p7 sigmaEven3021 ![true, false, true, true]
  | true, true, false, true => .p6 sigmaEven1320 ![false, false, true]
  | true, true, false, false => .p7 sigmaEven3021 ![true, false, false, true]
  | true, false, true, true => .p3 3 ![true, false, true, true]
  | true, false, true, false => .p3 1 ![false, true, true, true]
  | true, false, false, true => .p3 3 ![true, false, false, true]
  | true, false, false, false => .p3 1 ![false, true, false, true]
  | false, true, true, true => .p3 1 ![true, false, true, false]
  | false, true, true, false => .p3 3 ![false, true, true, false]
  | false, true, false, true => .p3 1 ![true, false, false, false]
  | false, true, false, false => .p3 3 ![false, true, false, false]
  | false, false, true, true => .p7 sigmaEven3021 ![false, true, true, false]
  | false, false, true, false => .p6 sigmaEven1320 ![true, true, false]
  | false, false, false, true => .p7 sigmaEven3021 ![false, true, false, false]
  | false, false, false, false => .p6 sigmaEven1320 ![true, false, false]

private theorem r0_P7_s0123_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven0123 s) = (r0TargetP7_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0123_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven0123 s) = (r0TargetP7_s0123 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0123, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0123 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven0123 s) = (r0TargetP7_s0123 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s0123_false s h0
  · exact r0_P7_s0123_true s h0

private def r0TargetP7_s0231 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p2 0 ![true, true, true, false]
  | true, true, true, false => .p2 1 ![true, false, true, true]
  | true, true, false, true => .p5 sigmaEven3021 ![false, true, true]
  | true, true, false, false => .p7 sigmaEven1203 ![false, true, false, true]
  | true, false, true, true => .p2 0 ![true, true, false, false]
  | true, false, true, false => .p2 1 ![true, false, false, true]
  | true, false, false, true => .p5 sigmaEven3021 ![false, false, true]
  | true, false, false, false => .p7 sigmaEven1203 ![false, false, false, true]
  | false, true, true, true => .p7 sigmaEven1203 ![true, true, true, false]
  | false, true, true, false => .p5 sigmaEven3021 ![true, true, false]
  | false, true, false, true => .p2 1 ![false, true, true, false]
  | false, true, false, false => .p2 0 ![false, false, true, true]
  | false, false, true, true => .p7 sigmaEven1203 ![true, false, true, false]
  | false, false, true, false => .p5 sigmaEven3021 ![true, false, false]
  | false, false, false, true => .p2 1 ![false, true, false, false]
  | false, false, false, false => .p2 0 ![false, false, false, true]

private theorem r0_P7_s0231_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven0231 s) = (r0TargetP7_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0231_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven0231 s) = (r0TargetP7_s0231 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0231, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0231 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven0231 s) = (r0TargetP7_s0231 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s0231_false s h0
  · exact r0_P7_s0231_true s h0

private def r0TargetP7_s0312 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven3102 ![false, true, true, true]
  | true, true, true, false => .p7 sigmaEven3102 ![false, true, true, false]
  | true, true, false, true => .p7 sigmaEven0312 ![true, true, false, true]
  | true, true, false, false => .p7 sigmaEven0312 ![true, true, false, false]
  | true, false, true, true => .p1 (codiceVentiquattro 1 2 (by omega) true true)
  | true, false, true, false => .p1 (codiceVentiquattro 1 2 (by omega) true false)
  | true, false, false, true => .p7 sigmaEven1032 ![false, false, true, true]
  | true, false, false, false => .p7 sigmaEven1032 ![false, false, true, false]
  | false, true, true, true => .p7 sigmaEven1032 ![true, true, false, true]
  | false, true, true, false => .p7 sigmaEven1032 ![true, true, false, false]
  | false, true, false, true => .p1 (codiceVentiquattro 1 2 (by omega) false true)
  | false, true, false, false => .p1 (codiceVentiquattro 1 2 (by omega) false false)
  | false, false, true, true => .p7 sigmaEven0312 ![false, false, true, true]
  | false, false, true, false => .p7 sigmaEven0312 ![false, false, true, false]
  | false, false, false, true => .p7 sigmaEven3102 ![true, false, false, true]
  | false, false, false, false => .p7 sigmaEven3102 ![true, false, false, false]

private theorem r0_P7_s0312_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven0312 s) = (r0TargetP7_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0312_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven0312 s) = (r0TargetP7_s0312 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s0312, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s0312 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven0312 s) = (r0TargetP7_s0312 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s0312_false s h0
  · exact r0_P7_s0312_true s h0

private def r0TargetP7_s1032 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p1 (codiceVentiquattro 0 2 (by omega) true true)
  | true, true, true, false => .p1 (codiceVentiquattro 0 2 (by omega) true false)
  | true, true, false, true => .p7 sigmaEven0312 ![false, true, true, true]
  | true, true, false, false => .p7 sigmaEven0312 ![false, true, true, false]
  | true, false, true, true => .p7 sigmaEven1032 ![false, true, false, true]
  | true, false, true, false => .p7 sigmaEven1032 ![false, true, false, false]
  | true, false, false, true => .p7 sigmaEven3102 ![false, true, false, true]
  | true, false, false, false => .p7 sigmaEven3102 ![false, true, false, false]
  | false, true, true, true => .p7 sigmaEven3102 ![true, false, true, true]
  | false, true, true, false => .p7 sigmaEven3102 ![true, false, true, false]
  | false, true, false, true => .p7 sigmaEven1032 ![true, false, true, true]
  | false, true, false, false => .p7 sigmaEven1032 ![true, false, true, false]
  | false, false, true, true => .p7 sigmaEven0312 ![true, false, false, true]
  | false, false, true, false => .p7 sigmaEven0312 ![true, false, false, false]
  | false, false, false, true => .p1 (codiceVentiquattro 0 2 (by omega) false true)
  | false, false, false, false => .p1 (codiceVentiquattro 0 2 (by omega) false false)

private theorem r0_P7_s1032_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven1032 s) = (r0TargetP7_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1032_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven1032 s) = (r0TargetP7_s1032 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1032, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1032 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven1032 s) = (r0TargetP7_s1032 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s1032_false s h0
  · exact r0_P7_s1032_true s h0

private def r0TargetP7_s1203 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p5 sigmaEven1320 ![true, true, true]
  | true, true, true, false => .p7 sigmaEven0231 ![false, true, true, true]
  | true, true, false, true => .p2 3 ![true, false, true, false]
  | true, true, false, false => .p2 0 ![false, true, true, false]
  | true, false, true, true => .p5 sigmaEven1320 ![true, false, true]
  | true, false, true, false => .p7 sigmaEven0231 ![false, false, true, true]
  | true, false, false, true => .p2 3 ![true, false, false, false]
  | true, false, false, false => .p2 0 ![false, true, false, false]
  | false, true, true, true => .p2 0 ![true, false, true, true]
  | false, true, true, false => .p2 3 ![false, true, true, true]
  | false, true, false, true => .p7 sigmaEven0231 ![true, true, false, false]
  | false, true, false, false => .p5 sigmaEven1320 ![false, true, false]
  | false, false, true, true => .p2 0 ![true, false, false, true]
  | false, false, true, false => .p2 3 ![false, true, false, true]
  | false, false, false, true => .p7 sigmaEven0231 ![true, false, false, false]
  | false, false, false, false => .p5 sigmaEven1320 ![false, false, false]

private theorem r0_P7_s1203_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven1203 s) = (r0TargetP7_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1203_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven1203 s) = (r0TargetP7_s1203 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1203, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1203 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven1203 s) = (r0TargetP7_s1203 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s1203_false s h0
  · exact r0_P7_s1203_true s h0

private def r0TargetP7_s1320 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven1320 ![true, true, true, true]
  | true, true, true, false => .p6 sigmaEven0123 ![false, true, false]
  | true, true, false, true => .p7 sigmaEven1320 ![true, true, false, true]
  | true, true, false, false => .p6 sigmaEven0123 ![false, false, false]
  | true, false, true, true => .p3 0 ![true, true, true, true]
  | true, false, true, false => .p3 1 ![false, true, true, false]
  | true, false, false, true => .p3 0 ![true, true, false, true]
  | true, false, false, false => .p3 1 ![false, true, false, false]
  | false, true, true, true => .p3 1 ![true, false, true, true]
  | false, true, true, false => .p3 0 ![false, false, true, false]
  | false, true, false, true => .p3 1 ![true, false, false, true]
  | false, true, false, false => .p3 0 ![false, false, false, false]
  | false, false, true, true => .p6 sigmaEven0123 ![true, true, true]
  | false, false, true, false => .p7 sigmaEven1320 ![false, false, true, false]
  | false, false, false, true => .p6 sigmaEven0123 ![true, false, true]
  | false, false, false, false => .p7 sigmaEven1320 ![false, false, false, false]

private theorem r0_P7_s1320_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven1320 s) = (r0TargetP7_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1320_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven1320 s) = (r0TargetP7_s1320 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s1320, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s1320 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven1320 s) = (r0TargetP7_s1320 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s1320_false s h0
  · exact r0_P7_s1320_true s h0

private def r0TargetP7_s2013 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 0 ![true, true, true, false]
  | true, true, true, false => .p4 1 ![false, true, true, true]
  | true, true, false, true => .p7 sigmaEven2301 ![true, true, true, false]
  | true, true, false, false => .p6 sigmaEven1203 ![true, false, true]
  | true, false, true, true => .p6 sigmaEven1203 ![true, true, false]
  | true, false, true, false => .p7 sigmaEven2301 ![true, false, false, true]
  | true, false, false, true => .p4 1 ![true, false, true, false]
  | true, false, false, false => .p4 0 ![false, false, true, true]
  | false, true, true, true => .p4 0 ![true, true, false, false]
  | false, true, true, false => .p4 1 ![false, true, false, true]
  | false, true, false, true => .p7 sigmaEven2301 ![false, true, true, false]
  | false, true, false, false => .p6 sigmaEven1203 ![false, false, true]
  | false, false, true, true => .p6 sigmaEven1203 ![false, true, false]
  | false, false, true, false => .p7 sigmaEven2301 ![false, false, false, true]
  | false, false, false, true => .p4 1 ![true, false, false, false]
  | false, false, false, false => .p4 0 ![false, false, false, true]

private theorem r0_P7_s2013_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven2013 s) = (r0TargetP7_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2013_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven2013 s) = (r0TargetP7_s2013 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2013, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2013 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven2013 s) = (r0TargetP7_s2013 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s2013_false s h0
  · exact r0_P7_s2013_true s h0

private def r0TargetP7_s2130 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p4 0 ![true, true, true, true]
  | true, true, true, false => .p4 3 ![true, false, true, false]
  | true, true, false, true => .p6 sigmaEven0231 ![true, true, true]
  | true, true, false, false => .p7 sigmaEven2130 ![true, true, false, false]
  | true, false, true, true => .p7 sigmaEven2130 ![true, false, true, true]
  | true, false, true, false => .p6 sigmaEven0231 ![true, false, false]
  | true, false, false, true => .p4 3 ![false, true, true, true]
  | true, false, false, false => .p4 0 ![false, false, true, false]
  | false, true, true, true => .p4 0 ![true, true, false, true]
  | false, true, true, false => .p4 3 ![true, false, false, false]
  | false, true, false, true => .p6 sigmaEven0231 ![false, true, true]
  | false, true, false, false => .p7 sigmaEven2130 ![false, true, false, false]
  | false, false, true, true => .p7 sigmaEven2130 ![false, false, true, true]
  | false, false, true, false => .p6 sigmaEven0231 ![false, false, false]
  | false, false, false, true => .p4 3 ![false, true, false, true]
  | false, false, false, false => .p4 0 ![false, false, false, false]

private theorem r0_P7_s2130_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven2130 s) = (r0TargetP7_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2130_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven2130 s) = (r0TargetP7_s2130 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2130, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2130 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven2130 s) = (r0TargetP7_s2130 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s2130_false s h0
  · exact r0_P7_s2130_true s h0

private def r0TargetP7_s2301 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p6 sigmaEven3210 ![true, true, true]
  | true, true, true, false => .p7 sigmaEven2013 ![true, true, false, true]
  | true, true, false, true => .p4 3 ![true, true, true, false]
  | true, true, false, false => .p4 1 ![false, false, true, false]
  | true, false, true, true => .p4 1 ![true, true, true, true]
  | true, false, true, false => .p4 3 ![false, false, true, true]
  | true, false, false, true => .p7 sigmaEven2013 ![true, false, true, false]
  | true, false, false, false => .p6 sigmaEven3210 ![true, false, false]
  | false, true, true, true => .p6 sigmaEven3210 ![false, true, true]
  | false, true, true, false => .p7 sigmaEven2013 ![false, true, false, true]
  | false, true, false, true => .p4 3 ![true, true, false, false]
  | false, true, false, false => .p4 1 ![false, false, false, false]
  | false, false, true, true => .p4 1 ![true, true, false, true]
  | false, false, true, false => .p4 3 ![false, false, false, true]
  | false, false, false, true => .p7 sigmaEven2013 ![false, false, true, false]
  | false, false, false, false => .p6 sigmaEven3210 ![false, false, false]

private theorem r0_P7_s2301_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven2301 s) = (r0TargetP7_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2301_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven2301 s) = (r0TargetP7_s2301 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s2301, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s2301 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven2301 s) = (r0TargetP7_s2301 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s2301_false s h0
  · exact r0_P7_s2301_true s h0

private def r0TargetP7_s3021 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p3 3 ![true, true, true, false]
  | true, true, true, false => .p3 0 ![true, false, true, true]
  | true, true, false, true => .p3 3 ![true, true, false, false]
  | true, true, false, false => .p3 0 ![true, false, false, true]
  | true, false, true, true => .p7 sigmaEven0123 ![true, true, true, false]
  | true, false, true, false => .p6 sigmaEven3021 ![false, true, false]
  | true, false, false, true => .p7 sigmaEven0123 ![true, true, false, false]
  | true, false, false, false => .p6 sigmaEven3021 ![false, false, false]
  | false, true, true, true => .p6 sigmaEven3021 ![true, true, true]
  | false, true, true, false => .p7 sigmaEven0123 ![false, false, true, true]
  | false, true, false, true => .p6 sigmaEven3021 ![true, false, true]
  | false, true, false, false => .p7 sigmaEven0123 ![false, false, false, true]
  | false, false, true, true => .p3 0 ![false, true, true, false]
  | false, false, true, false => .p3 3 ![false, false, true, true]
  | false, false, false, true => .p3 0 ![false, true, false, false]
  | false, false, false, false => .p3 3 ![false, false, false, true]

private theorem r0_P7_s3021_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven3021 s) = (r0TargetP7_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3021_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven3021 s) = (r0TargetP7_s3021 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3021, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3021 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven3021 s) = (r0TargetP7_s3021 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s3021_false s h0
  · exact r0_P7_s3021_true s h0

private def r0TargetP7_s3102 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven3102 ![true, true, true, true]
  | true, true, true, false => .p7 sigmaEven3102 ![true, true, true, false]
  | true, true, false, true => .p1 (codiceVentiquattro 2 3 (by omega) true false)
  | true, true, false, false => .p1 (codiceVentiquattro 2 3 (by omega) false false)
  | true, false, true, true => .p7 sigmaEven1032 ![false, true, true, true]
  | true, false, true, false => .p7 sigmaEven1032 ![false, true, true, false]
  | true, false, false, true => .p7 sigmaEven0312 ![false, false, false, true]
  | true, false, false, false => .p7 sigmaEven0312 ![false, false, false, false]
  | false, true, true, true => .p7 sigmaEven0312 ![true, true, true, true]
  | false, true, true, false => .p7 sigmaEven0312 ![true, true, true, false]
  | false, true, false, true => .p7 sigmaEven1032 ![true, false, false, true]
  | false, true, false, false => .p7 sigmaEven1032 ![true, false, false, false]
  | false, false, true, true => .p1 (codiceVentiquattro 2 3 (by omega) true true)
  | false, false, true, false => .p1 (codiceVentiquattro 2 3 (by omega) false true)
  | false, false, false, true => .p7 sigmaEven3102 ![false, false, false, true]
  | false, false, false, false => .p7 sigmaEven3102 ![false, false, false, false]

private theorem r0_P7_s3102_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven3102 s) = (r0TargetP7_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3102_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven3102 s) = (r0TargetP7_s3102 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3102, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3102 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven3102 s) = (r0TargetP7_s3102 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s3102_false s h0
  · exact r0_P7_s3102_true s h0

private def r0TargetP7_s3210 (s : Fin 4 → Bool) : VertexCode120 :=
  match s 0, s 1, s 2, s 3 with
  | true, true, true, true => .p7 sigmaEven3210 ![true, true, true, true]
  | true, true, true, false => .p5 sigmaEven0123 ![true, true, false]
  | true, true, false, true => .p2 3 ![true, false, true, true]
  | true, true, false, false => .p2 1 ![false, false, true, false]
  | true, false, true, true => .p7 sigmaEven3210 ![true, false, true, true]
  | true, false, true, false => .p5 sigmaEven0123 ![true, false, false]
  | true, false, false, true => .p2 3 ![true, false, false, true]
  | true, false, false, false => .p2 1 ![false, false, false, false]
  | false, true, true, true => .p2 1 ![true, true, true, true]
  | false, true, true, false => .p2 3 ![false, true, true, false]
  | false, true, false, true => .p5 sigmaEven0123 ![false, true, true]
  | false, true, false, false => .p7 sigmaEven3210 ![false, true, false, false]
  | false, false, true, true => .p2 1 ![true, true, false, true]
  | false, false, true, false => .p2 3 ![false, true, false, false]
  | false, false, false, true => .p5 sigmaEven0123 ![false, false, true]
  | false, false, false, false => .p7 sigmaEven3210 ![false, false, false, false]

private theorem r0_P7_s3210_false (s : Fin 4 → Bool)
    (h0 : s 0 = false) :
    r0_120 (vertP7 sigmaEven3210 s) = (r0TargetP7_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3210_true (s : Fin 4 → Bool)
    (h0 : s 0 = true) :
    r0_120 (vertP7 sigmaEven3210 s) = (r0TargetP7_s3210 s).eval := by
  ext k
  rw [r0_120_apply]
  fin_cases k
  all_goals cases h1 : s 1 <;> cases h2 : s 2 <;> cases h3 : s 3
  all_goals simp [r0TargetP7_s3210, delta0_120, VertexCode120.eval, vertP1, vertVentiquattro,
    segnoVentiquattro, vertP2_apply, vertP3_apply, vertP4_apply,
    vertP5_apply, vertP6_apply, vertP7_apply, base5, base6, base7,
    segnoZeroTesta, segnoPieno, sqrt_five_eq_aureo,
    sigmaEven0123, sigmaEven0231, sigmaEven0312, sigmaEven1032,
    sigmaEven1203, sigmaEven1320, sigmaEven2013, sigmaEven2130,
    sigmaEven2301, sigmaEven3021, sigmaEven3102, sigmaEven3210,
    Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]
  all_goals
    first
      | nlinarith [aureo_sq, sqrt_five_eq_aureo]
      | (left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; left; nlinarith [aureo_sq, sqrt_five_eq_aureo])
      | (right; right; nlinarith [aureo_sq, sqrt_five_eq_aureo])

private theorem r0_P7_s3210 (s : Fin 4 → Bool) :
    r0_120 (vertP7 sigmaEven3210 s) = (r0TargetP7_s3210 s).eval := by
  cases h0 : s 0
  · exact r0_P7_s3210_false s h0
  · exact r0_P7_s3210_true s h0

private theorem r0_P1_mem (c : CodiceVentiquattro) :
    r0_120 (vertP1 c) ∈ centoventiVertici := by
  rcases c with ⟨⟨⟨i, j⟩, hij⟩, ⟨si, sj⟩⟩
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  · change r0_120 (vertP1
      (codiceVentiquattro 0 1 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_01 si sj]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP1
      (codiceVentiquattro 0 2 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_02 si sj]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP1
      (codiceVentiquattro 0 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_03 si sj]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP1
      (codiceVentiquattro 1 2 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_12 si sj]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP1
      (codiceVentiquattro 1 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_13 si sj]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP1
      (codiceVentiquattro 2 3 (by omega) si sj)) ∈ centoventiVertici
    rw [r0_P1_23 si sj]; exact VertexCode120.eval_mem _

private theorem r0_P2_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r0_120 (vertP2 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r0_120 (vertP2 0 s) ∈ centoventiVertici
    rw [r0_P2_i0 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP2 1 s) ∈ centoventiVertici
    rw [r0_P2_i1 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP2 2 s) ∈ centoventiVertici
    rw [r0_P2_i2 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP2 3 s) ∈ centoventiVertici
    rw [r0_P2_i3 s]; exact VertexCode120.eval_mem _

private theorem r0_P3_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r0_120 (vertP3 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r0_120 (vertP3 0 s) ∈ centoventiVertici
    rw [r0_P3_i0 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP3 1 s) ∈ centoventiVertici
    rw [r0_P3_i1 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP3 2 s) ∈ centoventiVertici
    rw [r0_P3_i2 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP3 3 s) ∈ centoventiVertici
    rw [r0_P3_i3 s]; exact VertexCode120.eval_mem _

private theorem r0_P4_mem (i : Fin 4) (s : Fin 4 → Bool) :
    r0_120 (vertP4 i s) ∈ centoventiVertici := by
  fin_cases i
  · change r0_120 (vertP4 0 s) ∈ centoventiVertici
    rw [r0_P4_i0 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP4 1 s) ∈ centoventiVertici
    rw [r0_P4_i1 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP4 2 s) ∈ centoventiVertici
    rw [r0_P4_i2 s]; exact VertexCode120.eval_mem _
  · change r0_120 (vertP4 3 s) ∈ centoventiVertici
    rw [r0_P4_i3 s]; exact VertexCode120.eval_mem _

private theorem r0_P5_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : r0_120 (vertP5 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_P5_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r0_P5_s3210 s]; exact VertexCode120.eval_mem _

private theorem r0_P6_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : r0_120 (vertP6 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_P6_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r0_P6_s3210 s]; exact VertexCode120.eval_mem _

private theorem r0_P7_mem (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : r0_120 (vertP7 sigma s) ∈ centoventiVertici := by
  rcases alternating_eq_cases sigma with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · rw [r0_P7_s0123 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s0231 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s0312 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s1032 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s1203 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s1320 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s2013 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s2130 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s2301 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s3021 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s3102 s]; exact VertexCode120.eval_mem _
  · rw [r0_P7_s3210 s]; exact VertexCode120.eval_mem _

private theorem r0_mem120 {v : E4} (hv : v ∈ centoventiVertici) :
    r0_120 v ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
      ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact r0_P1_mem c
  · exact r0_P2_mem p.1 p.2
  · exact r0_P3_mem p.1 p.2
  · exact r0_P4_mem p.1 p.2
  · exact r0_P5_mem p.1 p.2
  · exact r0_P6_mem p.1 p.2
  · exact r0_P7_mem p.1 p.2

private theorem r0_image_vertices120 :
    (r0_120 : E4 → E4) '' (centoventiVertici : Set E4) =
      (centoventiVertici : Set E4) := by
  have hfin : Finset.image (r0_120 : E4 → E4) centoventiVertici =
      centoventiVertici := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact r0_mem120 hu
    · rw [Finset.card_image_of_injective _ r0_120.injective]
  rw [← Finset.coe_image, hfin]

theorem r0_120_isSymmetry : centoventi.isSymmetry r0_120 := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (r0_120 : E4 → E4) ''
        convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((r0_120 : E4 → E4) ''
        ((centoventi.vertices : Finset E4) : Set E4)) := by
          exact r0_120.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) := by
      rw [show ((centoventi.vertices : Finset E4) : Set E4) =
          (centoventiVertici : Set E4) by rfl, r0_image_vertices120]

private def flipSign120 (q : Fin 4) : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun j => if j = q then ⟨-1, by simp⟩ else ⟨1, by simp⟩

private def flip120 (q : Fin 4) : Isom 4 :=
  segnoPerm 4 (Equiv.refl (Fin 4)) (flipSign120 q)

@[simp] private theorem flip120_apply (q j : Fin 4) (x : E4) :
    flip120 q x j = (if j = q then -(x j) else x j) := by
  by_cases h : j = q <;>
    simp [flip120, flipSign120, segnoPerm_apply, segnoLinear, h]

private def flipBits4 (q : Fin 4) (s : Fin 4 → Bool) : Fin 4 → Bool :=
  fun j => if j = q then !s j else s j

private def flipBits3Slot (q : Fin 4) (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : Fin 3 → Bool :=
  fun k => if (sigma : Equiv.Perm (Fin 4)) (Fin.succ k) = q
    then !s k else s k

private def flipBits4Slot (q : Fin 4) (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : Fin 4 → Bool :=
  fun k => if (sigma : Equiv.Perm (Fin 4)) k = q then !s k else s k

private theorem flip120_P1 (q : Fin 4) (c : CodiceVentiquattro) :
    flip120 q (vertP1 c) =
      vertP1 (codiceVentiquattro (indicePrimoVentiquattro c)
        (indiceSecondoVentiquattro c) (indicePrimo_lt_indiceSecondo c)
        (segnoBoolDaReale (flipSign120 q (indicePrimoVentiquattro c))
          (segnoPrimoVentiquattro c))
        (segnoBoolDaReale (flipSign120 q (indiceSecondoVentiquattro c))
          (segnoSecondoVentiquattro c))) := by
  change segnoPerm 4 (Equiv.refl (Fin 4)) (flipSign120 q)
      ((2 : ℝ) • vertVentiquattro c) = _
  rw [segnoPerm_apply, map_smul]
  exact congrArg ((2 : ℝ) • ·)
    (segnoPerm_refl_vertVentiquattro (flipSign120 q) c)

private theorem flip120_P2 (q i : Fin 4) (s : Fin 4 → Bool) :
    flip120 q (vertP2 i s) = vertP2 i (flipBits4 q s) := by
  ext j
  rw [flip120_apply, vertP2_apply, vertP2_apply]
  by_cases h : j = q
  · subst h
    cases hs : s j <;> simp [flipBits4, hs] <;> split_ifs <;> norm_num
  · cases hs : s j <;> simp [flipBits4, h, hs]

private theorem flip120_P3 (q i : Fin 4) (s : Fin 4 → Bool) :
    flip120 q (vertP3 i s) = vertP3 i (flipBits4 q s) := by
  ext j
  rw [flip120_apply, vertP3_apply, vertP3_apply]
  by_cases h : j = q
  · subst h
    cases hs : s j <;> simp [flipBits4, hs] <;> split_ifs <;> norm_num
  · cases hs : s j <;> simp [flipBits4, h, hs]

private theorem flip120_P4 (q i : Fin 4) (s : Fin 4 → Bool) :
    flip120 q (vertP4 i s) = vertP4 i (flipBits4 q s) := by
  ext j
  rw [flip120_apply, vertP4_apply, vertP4_apply]
  by_cases h : j = q
  · subst h
    cases hs : s j <;> simp [flipBits4, hs] <;> split_ifs <;> norm_num
  · cases hs : s j <;> simp [flipBits4, h, hs]

private theorem flip120_P5 (q : Fin 4) (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) :
    flip120 q (vertP5 sigma s) = vertP5 sigma (flipBits3Slot q sigma s) := by
  ext j
  have hj : j = (sigma : Equiv.Perm (Fin 4))
      ((sigma : Equiv.Perm (Fin 4)).symm j) :=
    ((sigma : Equiv.Perm (Fin 4)).apply_symm_apply j).symm
  conv_lhs => rw [hj]
  conv_rhs => rw [hj]
  generalize (sigma : Equiv.Perm (Fin 4)).symm j = k at hj
  fin_cases k
  · simp [base5]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 1 = q
    · cases hs : s 0 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 0 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 2 = q
    · cases hs : s 1 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 1 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 3 = q
    · cases hs : s 2 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 2 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]

private theorem flip120_P6 (q : Fin 4) (sigma : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) :
    flip120 q (vertP6 sigma s) = vertP6 sigma (flipBits3Slot q sigma s) := by
  ext j
  have hj : j = (sigma : Equiv.Perm (Fin 4))
      ((sigma : Equiv.Perm (Fin 4)).symm j) :=
    ((sigma : Equiv.Perm (Fin 4)).apply_symm_apply j).symm
  conv_lhs => rw [hj]
  conv_rhs => rw [hj]
  generalize (sigma : Equiv.Perm (Fin 4)).symm j = k at hj
  fin_cases k
  · simp [base6]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 1 = q
    · cases hs : s 0 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 0 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 2 = q
    · cases hs : s 1 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 1 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 3 = q
    · cases hs : s 2 <;>
        simp [flipBits3Slot, segnoZeroTesta, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 2 <;> simp [flipBits3Slot, segnoZeroTesta, h, hs]

private theorem flip120_P7 (q : Fin 4) (sigma : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) :
    flip120 q (vertP7 sigma s) = vertP7 sigma (flipBits4Slot q sigma s) := by
  ext j
  have hj : j = (sigma : Equiv.Perm (Fin 4))
      ((sigma : Equiv.Perm (Fin 4)).symm j) :=
    ((sigma : Equiv.Perm (Fin 4)).apply_symm_apply j).symm
  conv_lhs => rw [hj]
  conv_rhs => rw [hj]
  generalize (sigma : Equiv.Perm (Fin 4)).symm j = k at hj
  fin_cases k
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 0 = q
    · cases hs : s 0 <;>
        simp [flipBits4Slot, segnoPieno, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 0 <;> simp [flipBits4Slot, segnoPieno, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 1 = q
    · cases hs : s 1 <;>
        simp [flipBits4Slot, segnoPieno, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 1 <;> simp [flipBits4Slot, segnoPieno, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 2 = q
    · cases hs : s 2 <;>
        simp [flipBits4Slot, segnoPieno, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 2 <;> simp [flipBits4Slot, segnoPieno, h, hs]
  · by_cases h : (sigma : Equiv.Perm (Fin 4)) 3 = q
    · cases hs : s 3 <;>
        simp [flipBits4Slot, segnoPieno, ← h, hs] <;> split_ifs <;> norm_num
    · cases hs : s 3 <;> simp [flipBits4Slot, segnoPieno, h, hs]

private theorem flip120_mem (q : Fin 4) {v : E4}
    (hv : v ∈ centoventiVertici) : flip120 q v ∈ centoventiVertici := by
  classical
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩) |
      ⟨p, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · rw [flip120_P1]
    exact vertP1_mem120 _
  · rw [flip120_P2]
    exact vertP2_mem120 _ _
  · rw [flip120_P3]
    exact vertP3_mem120 _ _
  · rw [flip120_P4]
    exact vertP4_mem120 _ _
  · rw [flip120_P5]
    exact vertP5_mem120 _ _
  · rw [flip120_P6]
    exact vertP6_mem120 _ _
  · rw [flip120_P7]
    exact vertP7_mem120 _ _

private theorem flip120_image_vertices (q : Fin 4) :
    (flip120 q : E4 → E4) '' (centoventiVertici : Set E4) =
      (centoventiVertici : Set E4) := by
  have hfin : Finset.image (flip120 q : E4 → E4) centoventiVertici =
      centoventiVertici := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact flip120_mem q hu
    · rw [Finset.card_image_of_injective _ (flip120 q).injective]
  rw [← Finset.coe_image, hfin]

private theorem flip120_isSymmetry (q : Fin 4) :
    centoventi.isSymmetry (flip120 q) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (flip120 q : E4 → E4) ''
        convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((flip120 q : E4 → E4) ''
        ((centoventi.vertices : Finset E4) : Set E4)) := by
          exact (flip120 q).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((centoventi.vertices : Finset E4) : Set E4) := by
      rw [show ((centoventi.vertices : Finset E4) : Set E4) =
          (centoventiVertici : Set E4) by rfl, flip120_image_vertices]

/-- Parete 1: negazione della quarta coordinata.-/
def r1_120 : Isom 4 := flip120 3

/-- Parete 3: negazione della terza coordinata.-/
def r3_120 : Isom 4 := flip120 2

theorem r1_120_isSymmetry : centoventi.isSymmetry r1_120 :=
  flip120_isSymmetry 3

theorem r3_120_isSymmetry : centoventi.isSymmetry r3_120 :=
  flip120_isSymmetry 2

private theorem mem_F0_120_iff {x : E4} :
    x ∈ F0_120 ↔ x ∈ centoventi.toSet ∧ l0_120 x = 8 := by
  constructor
  · intro hx
    have hx0 : x = v0_120 := by
      simpa [F0_120, generatoriF0_120] using hx
    subst x
    exact ⟨subset_convexHull ℝ _ (by exact_mod_cast vertP1_mem120 _),
      fundamental_values.1⟩
  · rintro ⟨hxP, hl⟩
    have hx := faccia_argmax centoventiVertici l0_120 hxP (by
      intro y hy
      rw [hl]
      exact li_toSet_le.1 y hy)
    rw [hl, argmax_l0_120] at hx
    exact hx

private theorem mem_F1_120_iff {x : E4} :
    x ∈ F1_120 ↔ x ∈ centoventi.toSet ∧
      l1_120 x = 6 + 6 * aureo := by
  constructor
  · intro hx
    exact ⟨F1_120_isFace.1.subset hx, l1_eq_on_F1_120 hx⟩
  · rintro ⟨hxP, hl⟩
    have hx := faccia_argmax centoventiVertici l1_120 hxP (by
      intro y hy
      rw [hl]
      exact li_toSet_le.2.1 y hy)
    rw [hl, argmax_l1_120] at hx
    exact hx

private theorem mem_F2_120_iff {x : E4} :
    x ∈ F2_120 ↔ x ∈ centoventi.toSet ∧
      l2_120 x = 2 + 4 * aureo := by
  constructor
  · intro hx
    exact ⟨F2_120_isFace.1.subset hx, l2_eq_on_F2_120 hx⟩
  · rintro ⟨hxP, hl⟩
    have hx := faccia_argmax centoventiVertici l2_120 hxP (by
      intro y hy
      rw [hl]
      exact li_toSet_le.2.2.1 y hy)
    rw [hl, argmax_l2_120] at hx
    exact hx

private theorem mem_F3_120_iff {x : E4} :
    x ∈ F3_120 ↔ x ∈ centoventi.toSet ∧
      l3_120 x = 2 + 4 * aureo := by
  constructor
  · intro hx
    exact ⟨F3_120_isFace.1.subset hx, l3_eq_on_F3_120 hx⟩
  · rintro ⟨hxP, hl⟩
    have hx := faccia_argmax centoventiVertici l3_120 hxP (by
      intro y hy
      rw [hl]
      exact li_toSet_le.2.2.2 y hy)
    rw [hl, argmax_l3_120] at hx
    exact hx

private theorem image_level_face (g : Isom 4) (F : Set E4)
    (l : E4 →L[ℝ] ℝ) (c : ℝ)
    (hP : (g : E4 → E4) '' centoventi.toSet = centoventi.toSet)
    (hl : ∀ x, l (g x) = l x)
    (hF : ∀ x, x ∈ F ↔ x ∈ centoventi.toSet ∧ l x = c) :
    (g : E4 → E4) '' F = F := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hF]
    refine ⟨?_, ?_⟩
    · rw [← hP]
      exact ⟨x, (hF x).mp hx |>.1, rfl⟩
    · rw [hl]
      exact (hF x).mp hx |>.2
  · intro hy
    have hyP := (hF y).mp hy |>.1
    rw [← hP] at hyP
    obtain ⟨x, hxP, hxy⟩ := hyP
    subst y
    refine ⟨x, (hF x).mpr ⟨hxP, ?_⟩, rfl⟩
    rw [← hl x]
    exact (hF (g x)).mp hy |>.2

private theorem l1_r0_120 (x : E4) : l1_120 (r0_120 x) = l1_120 x := by
  norm_num [l1_120]
  rw [r0_120_apply_zero, r0_120_apply_one, r0_120_apply_three]
  linear_combination (3 * delta0_120 x / 2) * aureo_sq

private theorem l2_r0_120 (x : E4) : l2_120 (r0_120 x) = l2_120 x := by
  norm_num [l2_120]
  rw [r0_120_apply_zero, r0_120_apply_one]
  linear_combination (delta0_120 x / 2) * aureo_sq

private theorem l3_r0_120 (x : E4) : l3_120 (r0_120 x) = l3_120 x := by
  norm_num [l3_120]
  rw [r0_120_apply_zero, r0_120_apply_one, r0_120_apply_two]
  linear_combination (delta0_120 x / 2) * aureo_sq

private theorem l0_r2_120 (x : E4) : l0_120 (r2_120 x) = l0_120 x := by
  norm_num [l0_120]
  rw [r2_120_apply_zero, r2_120_apply_one]
  ring

private theorem l1_r2_120 (x : E4) : l1_120 (r2_120 x) = l1_120 x := by
  norm_num [l1_120]
  rw [r2_120_apply_zero, r2_120_apply_one, r2_120_apply_three]
  ring

private theorem l3_r2_120 (x : E4) : l3_120 (r2_120 x) = l3_120 x := by
  norm_num [l3_120]
  rw [r2_120_apply_zero, r2_120_apply_one, r2_120_apply_two]
  ring

private theorem l0_r1_120 (x : E4) : l0_120 (r1_120 x) = l0_120 x := by
  norm_num [l0_120, r1_120, Fin.ext_iff]

private theorem l2_r1_120 (x : E4) : l2_120 (r1_120 x) = l2_120 x := by
  norm_num [l2_120, r1_120, Fin.ext_iff]

private theorem l3_r1_120 (x : E4) : l3_120 (r1_120 x) = l3_120 x := by
  norm_num [l3_120, r1_120, Fin.ext_iff]

private theorem l0_r3_120 (x : E4) : l0_120 (r3_120 x) = l0_120 x := by
  norm_num [l0_120, r3_120, Fin.ext_iff]

private theorem l1_r3_120 (x : E4) : l1_120 (r3_120 x) = l1_120 x := by
  norm_num [l1_120, r3_120, Fin.ext_iff]

private theorem l2_r3_120 (x : E4) : l2_120 (r3_120 x) = l2_120 x := by
  norm_num [l2_120, r3_120, Fin.ext_iff]

private theorem r0_image_F1_120 :
    (r0_120 : E4 → E4) '' F1_120 = F1_120 :=
  image_level_face r0_120 F1_120 l1_120 (6 + 6 * aureo)
    r0_120_isSymmetry l1_r0_120 (fun _ => mem_F1_120_iff)

private theorem r0_image_F2_120 :
    (r0_120 : E4 → E4) '' F2_120 = F2_120 :=
  image_level_face r0_120 F2_120 l2_120 (2 + 4 * aureo)
    r0_120_isSymmetry l2_r0_120 (fun _ => mem_F2_120_iff)

private theorem r0_image_F3_120 :
    (r0_120 : E4 → E4) '' F3_120 = F3_120 :=
  image_level_face r0_120 F3_120 l3_120 (2 + 4 * aureo)
    r0_120_isSymmetry l3_r0_120 (fun _ => mem_F3_120_iff)

private theorem r1_image_F0_120 :
    (r1_120 : E4 → E4) '' F0_120 = F0_120 :=
  image_level_face r1_120 F0_120 l0_120 8
    r1_120_isSymmetry l0_r1_120 (fun _ => mem_F0_120_iff)

private theorem r1_image_F2_120 :
    (r1_120 : E4 → E4) '' F2_120 = F2_120 :=
  image_level_face r1_120 F2_120 l2_120 (2 + 4 * aureo)
    r1_120_isSymmetry l2_r1_120 (fun _ => mem_F2_120_iff)

private theorem r1_image_F3_120 :
    (r1_120 : E4 → E4) '' F3_120 = F3_120 :=
  image_level_face r1_120 F3_120 l3_120 (2 + 4 * aureo)
    r1_120_isSymmetry l3_r1_120 (fun _ => mem_F3_120_iff)

private theorem r2_image_F0_120 :
    (r2_120 : E4 → E4) '' F0_120 = F0_120 :=
  image_level_face r2_120 F0_120 l0_120 8
    r2_120_isSymmetry l0_r2_120 (fun _ => mem_F0_120_iff)

private theorem r2_image_F1_120 :
    (r2_120 : E4 → E4) '' F1_120 = F1_120 :=
  image_level_face r2_120 F1_120 l1_120 (6 + 6 * aureo)
    r2_120_isSymmetry l1_r2_120 (fun _ => mem_F1_120_iff)

private theorem r2_image_F3_120 :
    (r2_120 : E4 → E4) '' F3_120 = F3_120 :=
  image_level_face r2_120 F3_120 l3_120 (2 + 4 * aureo)
    r2_120_isSymmetry l3_r2_120 (fun _ => mem_F3_120_iff)

private theorem r3_image_F0_120 :
    (r3_120 : E4 → E4) '' F0_120 = F0_120 :=
  image_level_face r3_120 F0_120 l0_120 8
    r3_120_isSymmetry l0_r3_120 (fun _ => mem_F0_120_iff)

private theorem r3_image_F1_120 :
    (r3_120 : E4 → E4) '' F1_120 = F1_120 :=
  image_level_face r3_120 F1_120 l1_120 (6 + 6 * aureo)
    r3_120_isSymmetry l1_r3_120 (fun _ => mem_F1_120_iff)

private theorem r3_image_F2_120 :
    (r3_120 : E4 → E4) '' F2_120 = F2_120 :=
  image_level_face r3_120 F2_120 l2_120 (2 + 4 * aureo)
    r3_120_isSymmetry l2_r3_120 (fun _ => mem_F2_120_iff)

private theorem sigmaA_eq_sigmaEven2301 : sigmaA = sigmaEven2301 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

private theorem sigmaC_eq_sigmaEven3210 : sigmaC = sigmaEven3210 := by
  apply Subtype.ext
  ext i
  fin_cases i <;> decide

private theorem r0_v0_120 : r0_120 v0_120 = w0_120 := by
  simpa [v0_120, w0_120, r0TargetP1_01, VertexCode120.eval,
    sigmaA_eq_sigmaEven2301] using r0_P1_01 true true

private theorem r1_w0_120 : r1_120 w0_120 = w1_120 := by
  have hb : flipBits3Slot 3 sigmaA ![true, true, true] =
      ![false, true, true] := by
    funext k
    fin_cases k <;>
      simp [flipBits3Slot, sigmaA, permA, Equiv.swap_apply_def,
        Fin.ext_iff]
  have h := flip120_P6 3 sigmaA ![true, true, true]
  rw [hb] at h
  simpa [r1_120, w0_120, w1_120] using h

private theorem r2_w1_120 : r2_120 w1_120 = w2_120 := by
  simpa [w1_120, w2_120, r2TargetP6_s2301, VertexCode120.eval,
    sigmaA_eq_sigmaEven2301, sigmaC_eq_sigmaEven3210] using
      r2_P6_s2301 ![false, true, true]

private theorem r0_moves_F0_120 :
    (r0_120 : E4 → E4) '' F0_120 ≠ F0_120 := by
  intro h
  have hw : w0_120 ∈ (r0_120 : E4 → E4) '' F0_120 :=
    ⟨v0_120, subset_convexHull ℝ _ (by simp [generatoriF0_120]),
      r0_v0_120⟩
  rw [h, F0_120, generatoriF0_120] at hw
  have heq : w0_120 = v0_120 := by simpa using hw
  exact v0_ne_w0_120 heq.symm

private theorem r1_moves_F1_120 :
    (r1_120 : E4 → E4) '' F1_120 ≠ F1_120 := by
  intro h
  have hw : w1_120 ∈ (r1_120 : E4 → E4) '' F1_120 :=
    ⟨w0_120, subset_convexHull ℝ _ (by simp [generatoriF1_120]),
      r1_w0_120⟩
  rw [h] at hw
  have hl := l1_eq_on_F1_120 hw
  exact w1_ne_w0_120 (P6_l1_eq_w0 sigmaA ![false, true, true] hl)

private theorem r2_moves_F2_120 :
    (r2_120 : E4 → E4) '' F2_120 ≠ F2_120 := by
  intro h
  have hw : w2_120 ∈ (r2_120 : E4 → E4) '' F2_120 :=
    ⟨w1_120, subset_convexHull ℝ _ (by simp [generatoriF2_120]),
      r2_w1_120⟩
  rw [h] at hw
  have hl := l2_eq_on_F2_120 hw
  rcases P6_l2_eq_pair sigmaC ![true, true, true] hl with heq | heq
  · exact w2_ne_w0_120 heq
  · exact w2_ne_w1_120 heq

private theorem l3_r3_cellVertex1 :
    l3_120 (r3_120 (cellVertex120 1)) = 4 * aureo := by
  norm_num [l3_120, r3_120, cellVertex120, Fin.ext_iff,
    sqrt_five_eq_aureo,
    show (![true, true, true, true] : Fin 4 → Bool) 2 = true from rfl]
  nlinarith [aureo_sq]

private theorem r3_moves_F3_120 :
    (r3_120 : E4 → E4) '' F3_120 ≠ F3_120 := by
  intro h
  have hv : r3_120 (cellVertex120 1) ∈
      (r3_120 : E4 → E4) '' F3_120 :=
    ⟨cellVertex120 1, subset_convexHull ℝ _ (by
      exact_mod_cast cellVertex_mem_generatoriF3 1), rfl⟩
  rw [h] at hv
  have hl := l3_eq_on_F3_120 hv
  rw [l3_r3_cellVertex1] at hl
  norm_num at hl

theorem r0_120_flagAdjacent :
    FlagAdjacentAt centoventi centoventiFlag
      (mapFlag centoventi r0_120_isSymmetry centoventiFlag) 0 := by
  constructor
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact r0_image_F1_120
    · exact r0_image_F2_120
    · exact r0_image_F3_120
  · exact r0_moves_F0_120

theorem r1_120_flagAdjacent :
    FlagAdjacentAt centoventi centoventiFlag
      (mapFlag centoventi r1_120_isSymmetry centoventiFlag) 1 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r1_image_F0_120
    · exact (hj rfl).elim
    · exact r1_image_F2_120
    · exact r1_image_F3_120
  · exact r1_moves_F1_120

theorem r2_120_flagAdjacent :
    FlagAdjacentAt centoventi centoventiFlag
      (mapFlag centoventi r2_120_isSymmetry centoventiFlag) 2 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r2_image_F0_120
    · exact r2_image_F1_120
    · exact (hj rfl).elim
    · exact r2_image_F3_120
  · exact r2_moves_F2_120

theorem r3_120_flagAdjacent :
    FlagAdjacentAt centoventi centoventiFlag
      (mapFlag centoventi r3_120_isSymmetry centoventiFlag) 3 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r3_image_F0_120
    · exact r3_image_F1_120
    · exact r3_image_F2_120
    · exact (hj rfl).elim
  · exact r3_moves_F3_120

end LeanEval.Geometry.PlatonicClassification
