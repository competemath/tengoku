import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq.lean`: removed 3 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_casimir_commute_archDeriv_and_sum_reversed_cubic_eq

set_option autoImplicit false

noncomputable section

namespace R1CasimirCentral

section Formal

variable {R : Type*} [Ring R] (D : Fin 3 → Fin 3 → R)
  (hD : ∀ a b c d : Fin 3, ⁅D a b, D c d⁆ = (if b = c then D a d else 0) - (if d = a then D c b else 0))

/--
@isnad1 id=eq.0h4v.s6.30cba3c33d6e from=translated src=- shape=5da7be7d vocab=bfda4450
-/
theorem lie_mul₂ (x y z : R) : ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

/--
@isnad1 id=eq.0h3v.s7.da4050f581e1 from=translated src=- shape=af0019c1 vocab=6d4315f5
-/
theorem sum_sum_ite_eq_outer (b : Fin 3) (f : Fin 3 → Fin 3 → R) :
    (∑ i : Fin 3, ∑ j : Fin 3, if b = i then f i j else 0) = ∑ j : Fin 3, f b j := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

/--
@isnad1 id=eq.0h3v.s7.4673d97594ee from=translated src=- shape=197b589a vocab=6d4315f5
-/
theorem sum_sum_ite_eq_outer' (b : Fin 3) (f : Fin 3 → Fin 3 → R) :
    (∑ i : Fin 3, ∑ j : Fin 3, if i = b then f i j else 0) = ∑ j : Fin 3, f b j := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/--
@isnad1 id=eq.0h3v.s7.67acc830a862 from=translated src=- shape=cc722fff vocab=6d4315f5
-/
theorem sum_sum_sum_ite_eq_outer (b : Fin 3) (f : Fin 3 → Fin 3 → Fin 3 → R) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, if b = i then f i j k else 0) = ∑ j : Fin 3, ∑ k : Fin 3, f b j k := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

/--
@isnad1 id=eq.0h3v.s7.92ba9983dae8 from=translated src=- shape=08833a25 vocab=6d4315f5
-/
theorem sum_sum_sum_ite_eq_outer' (b : Fin 3) (f : Fin 3 → Fin 3 → Fin 3 → R) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, if i = b then f i j k else 0) = ∑ j : Fin 3, ∑ k : Fin 3, f b j k := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi; simp [hi]
  · simp

private theorem lie_sum' {ι : Type*} (a : R) (s : Finset ι) (f : ι → R) :
    ⁅a, ∑ i ∈ s, f i⁆ = ∑ i ∈ s, ⁅a, f i⁆ := by
  simp only [Ring.lie_def, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

include hD

/--
@isnad1 id=eq.1h4v.s7.9671a285def0 from=translated src=- shape=b011058a vocab=d8f42cb6
-/
theorem lie_K1 (a b : Fin 3) : ⁅D a b, ∑ i : Fin 3, D i i⁆ = 0 := by
  rw [lie_sum']
  simp only [hD]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp

/--
@isnad1 id=eq.1h4v.s8.7342b6411da7 from=translated src=- shape=f9c7dba5 vocab=e29b4677
-/
theorem lie_K2 (a b : Fin 3) : ⁅D a b, ∑ i : Fin 3, ∑ j : Fin 3, D i j * D j i⁆ = 0 := by
  simp only [lie_sum', lie_mul₂, hD, sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, sum_sum_ite_eq_outer, sum_sum_ite_eq_outer']
  abel

/--
@isnad1 id=eq.1h4v.s8.90856f1ac6d8 from=translated src=- shape=b2cd4435 vocab=e29b4677
-/
theorem lie_K3 (a b : Fin 3) : ⁅D a b, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D i j * D j k * D k i⁆ = 0 := by
  simp only [lie_sum', mul_assoc]
  simp only [lie_mul₂, hD, sub_mul, mul_sub, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, sum_sum_ite_eq_outer, sum_sum_ite_eq_outer', sum_sum_sum_ite_eq_outer, sum_sum_sum_ite_eq_outer']
  abel

/--
@isnad1 id=eq.1h6v.s8.346b2f883cb8 from=translated src=- shape=348bc190 vocab=a01f3db2
-/
theorem mul_comm_rule (a b c d : Fin 3) :
    D a b * D c d = D c d * D a b + ((if b = c then D a d else 0) - (if d = a then D c b else 0)) := by
  rw [← hD, Ring.lie_def]; abel

/--
@isnad1 id=eq.1h2v.s9.bfdc50ee3633 from=translated src=- shape=bbf13651 vocab=a7076447
-/
theorem sum_reversed_eq :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D j i * D k j * D i k) =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D i j * D j k * D k i) +
        (∑ i : Fin 3, D i i) * (∑ i : Fin 3, D i i) - (3 : ℕ) • ∑ i : Fin 3, ∑ j : Fin 3, D i j * D j i := by

  have hterm : ∀ i j k : Fin 3, D j i * D k j * D i k =
      D j i * D i k * D k j + ((if j = i then D j i * D k k else 0) - D j i * D i j) := by
    intro i j k
    rw [mul_assoc, mul_comm_rule D hD k j i k, ite_eq_left rfl, mul_add, ← mul_assoc, mul_sub, mul_ite, mul_zero]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]

  have h1 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D j i * D i k * D k j) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D i j * D j k * D k i := by
    rw [Finset.sum_comm]
  have h2 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, if j = i then D j i * D k k else 0) =
      (∑ i : Fin 3, D i i) * (∑ i : Fin 3, D i i) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_sum_ite_eq_outer']
  have h3 : (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D j i * D i j) =
      (3 : ℕ) • ∑ i : Fin 3, ∑ j : Fin 3, D i j * D j i := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
  rw [h1, h2, h3]
  abel

end Formal

open LanglandsTunnell.CubicInduction.WhittakerBlock

/--
@isnad1 id=eq.0h5v.s9.97c538bddae0 from=translated src=- shape=23ad7d66 vocab=b36bebc6
-/
theorem single_mul_single_sub {S : Type} [Ring S] (i j k l : Fin 3) :
    Matrix.single i j (1 : S) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1 =
      (if j = k then Matrix.single i l (1 : S) else 0) - (if l = i then Matrix.single k j (1 : S) else 0) := by
  congr 1
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h)]
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h)]

/--
@isnad1 id=eq.0h2v.s14.68a6af9df7be from=translated src=- shape=648d564f vocab=a70db667
-/
theorem lie_derivAction3 (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    ⁅derivAction3 X, derivAction3 Y⁆ = derivAction3 (X * Y - Y * X) := by
  rw [← derivAction3_lie]; rfl

/--
@isnad1 id=eq.0h4v.s14.5ed75162a665 from=translated src=- shape=f4903759 vocab=019de93c
-/
theorem lie_archDerivₗ (a b c d : Fin 3) :
    ⁅(archDerivₗ a b : Module.End ℂ smoothFunctions3), archDerivₗ c d⁆ =
      (if b = c then archDerivₗ a d else 0) - (if d = a then archDerivₗ c b else 0) := by
  rw [← derivAction3_single a b, ← derivAction3_single c d, lie_derivAction3, single_mul_single_sub, map_sub]
  congr 1 <;> split_ifs <;> simp only [derivAction3_single, map_zero]

end R1CasimirCentral

open LanglandsTunnell.CubicInduction.WhittakerBlock R1CasimirCentral in
/--
@isnad1 id=and.0h0v.s16.c3115c86ebaa from=translated src=- shape=54850ffc vocab=0cd5f674
-/
theorem solution :
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, archDerivₗ i i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3, Commute (∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) (archDerivₗ a b)) ∧
    (∀ a b : Fin 3,
      Commute (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i)
        (archDerivₗ a b)) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ j i * archDerivₗ k j * archDerivₗ i k =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, archDerivₗ i j * archDerivₗ j k * archDerivₗ k i) +
        (∑ i : Fin 3, archDerivₗ i i) * (∑ i : Fin 3, archDerivₗ i i) -
        (3 : ℂ) • ∑ i : Fin 3, ∑ j : Fin 3, archDerivₗ i j * archDerivₗ j i) := by
  have hD : ∀ a b c d : Fin 3, ⁅(archDerivₗ a b : Module.End ℂ smoothFunctions3), archDerivₗ c d⁆ =
      (if b = c then archDerivₗ a d else 0) - (if d = a then archDerivₗ c b else 0) := lie_archDerivₗ
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, ?_⟩
  · exact (Commute.symm ((commute_iff_lie_eq).mpr (lie_K1 (fun a b => archDerivₗ a b) hD a b)))
  · exact (Commute.symm ((commute_iff_lie_eq).mpr (lie_K2 (fun a b => archDerivₗ a b) hD a b)))
  · exact (Commute.symm ((commute_iff_lie_eq).mpr (lie_K3 (fun a b => archDerivₗ a b) hD a b)))
  · rw [sum_reversed_eq (fun a b => archDerivₗ a b) hD, ← Nat.cast_smul_eq_nsmul ℂ]
    norm_num
