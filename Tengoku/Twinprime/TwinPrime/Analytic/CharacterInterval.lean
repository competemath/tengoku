import Tengoku.Twinprime.TwinPrime.Analytic.CharacterLargeSieveTransfer
import Tengoku.Twinprime.TwinPrime.Analytic.AdditiveLargeSieve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A primitive-character Pólya--Vinogradov interval bound

All nonzero residue frequencies at one positive modulus have spacing `1/q`.
Their additive interval kernels have total norm at most `q * H_q`. Gauss-sum
factorization and the exact primitive Gauss norm therefore give the bound
`sqrt(q) * H_q`, and hence `sqrt(q) * (1 + log q)`.

The character is primitive and the modulus exceeds one; these conditions
exclude the principal character. Composite moduli and arbitrary natural
interval endpoints are included. No character-cancellation input is assumed.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- At a fixed modulus, distinct residues have spacing `1/q`, not `1/q²`.
@isnad1 id=le.1h3v.s8.caad608dab2f from=translated src=- shape=976c04fe vocab=63606762
-/
theorem residue_frequency_dist_ge_inv {q : ℕ} [NeZero q] (a b : ZMod q) (hab : a ≠ b) :
    (1 : ℝ) / q ≤ dist (ZMod.toAddCircle a) (ZMod.toAddCircle b) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
  have hc : 0 < (a - b).val :=
    Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr (sub_ne_zero.mpr hab))
  have hqc : 0 < q - (a - b).val := Nat.sub_pos_of_lt (ZMod.val_lt _)
  have hmin : 1 ≤ min (a - b).val (q - (a - b).val) := le_min hc hqc
  have hnorm : ‖ZMod.toAddCircle (a - b)‖ =
      ((min (a - b).val (q - (a - b).val) : ℕ) : ℝ) / q := by
    rw [ZMod.toAddCircle_apply]
    simpa only [mul_one, one_mul, Nat.mod_eq_of_lt (ZMod.val_lt (a - b))] using
      (AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := (a - b).val) (n := q))
  rw [dist_eq_norm, ← map_sub, hnorm]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmin) (Nat.cast_nonneg q)

/-- The phase convention for an arbitrary residue, with no unit restriction.
@isnad1 id=eq.0h3v.s7.ba8110fdff3a from=translated src=- shape=d7fb9fa9 vocab=795cac26
-/
theorem stdAddChar_mul_nat_eq_additivePhase {q : ℕ} [NeZero q]
    (u : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (u * (n : ZMod q)) =
      additivePhase ((n : ℝ) * (u.val / (q : ℝ))) := by
  have hbase : ZMod.stdAddChar u = additivePhase (u.val / (q : ℝ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp]
    rfl
  rw [← additivePhase_pow, ← hbase, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, mul_comm]

/-- The total norm of all nonzero residue kernels at one modulus.
@isnad1 id=le.0h3v.s7.d55214b54575 from=translated src=- shape=74df4b00 vocab=1d1dd22e
-/
theorem sum_norm_nonzero_residue_kernels_le {q : ℕ} [NeZero q] (M N : ℕ) :
    (∑ u ∈ (univ : Finset (ZMod q)).erase 0,
      ‖∑ n ∈ Ico M N, ZMod.stdAddChar (u * (n : ZMod q))‖) ≤
      (q : ℝ) * (harmonic q : ℝ) := by
  classical
  let θ : ZMod q → ℝ := fun u => u.val / (q : ℝ)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsep : ∀ u ∈ (univ : Finset (ZMod q)), ∀ v ∈ univ, u ≠ v →
      (1 : ℝ) / q ≤ dist (θ u : UnitAddCircle) (θ v : UnitAddCircle) := by
    intro u _ v _ huv
    simpa only [ZMod.toAddCircle_apply, θ] using residue_frequency_dist_ge_inv u v huv
  have hrecip := sum_reciprocal_unitAddCircle_dist_le univ θ (1 / (q : ℝ))
    (by positivity) hsep 0 (mem_univ _)
  have hzero : θ 0 = 0 := by simp [θ]
  simp only [hzero, AddCircle.coe_zero, dist_zero_left, card_univ, ZMod.card] at hrecip
  calc
    _ ≤ ∑ u ∈ (univ : Finset (ZMod q)).erase 0,
        1 / (2 * ‖(θ u : UnitAddCircle)‖) := by
      apply sum_le_sum
      intro u hu
      have hune : (θ u : UnitAddCircle) ≠ 0 := by
        have h : ZMod.toAddCircle u ≠ 0 :=
          fun heq => (ne_of_mem_erase hu) (ZMod.toAddCircle_eq_zero.mp heq)
        simpa only [ZMod.toAddCircle_apply, θ] using h
      have h := norm_sum_Ico_additivePhase_le_min M N (θ u) hune
      simp only [stdAddChar_mul_nat_eq_additivePhase, θ]
      exact h.trans (min_le_right _ _)
    _ = (∑ u ∈ (univ : Finset (ZMod q)).erase 0,
        1 / ‖(θ u : UnitAddCircle)‖) / 2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (2 * (harmonic q : ℝ) / (1 / (q : ℝ))) / 2 :=
      div_le_div_of_nonneg_right hrecip (by norm_num)
    _ = _ := by simp only [one_div, div_inv_eq_mul]; ring

/-- The inverse convention supplied directly by primitive Gauss factorization.
@isnad1 id=le.2h4v.s7.cf90e6b0f0fb from=translated src=- shape=f5568a51 vocab=db54b5a3
-/
theorem norm_sum_primitive_character_inv_Ico_le_harmonic {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (M N : ℕ) :
    ‖∑ n ∈ Ico M N, χ⁻¹ (n : ZMod q)‖ ≤ Real.sqrt q * (harmonic q : ℝ) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq0
  let K : ZMod q → ℂ := fun u => ∑ n ∈ Ico M N, ZMod.stdAddChar (u * (n : ZMod q))
  have hfac : gaussSum χ ZMod.stdAddChar * (∑ n ∈ Ico M N, χ⁻¹ (n : ZMod q)) =
      ∑ u : ZMod q, χ u * K u := by
    have h := primitive_character_additive_factorization χ hχ (Ico M N) (fun _ => 1)
    simp only [one_mul] at h
    exact h.trans (sum_units_character_mul_eq χ K)
  have hz : χ (0 : ZMod q) = 0 := χ.map_zero' (by omega)
  have hbound : Real.sqrt q * ‖∑ n ∈ Ico M N, χ⁻¹ (n : ZMod q)‖ ≤
      (q : ℝ) * (harmonic q : ℝ) := by
    calc
      _ = ‖gaussSum χ ZMod.stdAddChar * (∑ n ∈ Ico M N, χ⁻¹ (n : ZMod q))‖ := by
        rw [norm_mul, norm_primitive_gaussSum χ hχ]
      _ = ‖∑ u ∈ (univ : Finset (ZMod q)).erase 0, χ u * K u‖ := by
        rw [hfac, ← sum_erase_add univ _ (mem_univ (0 : ZMod q))]
        simp only [hz, zero_mul, add_zero]
      _ ≤ ∑ u ∈ (univ : Finset (ZMod q)).erase 0, ‖χ u * K u‖ := norm_sum_le _ _
      _ ≤ ∑ u ∈ (univ : Finset (ZMod q)).erase 0, ‖K u‖ := by
        apply sum_le_sum
        intro u _
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one u)
      _ ≤ _ := sum_norm_nonzero_residue_kernels_le M N
  apply (mul_le_mul_iff_right₀ hs).mp
  calc
    _ = Real.sqrt q * ‖∑ n ∈ Ico M N, χ⁻¹ (n : ZMod q)‖ := by ring
    _ ≤ (q : ℝ) * (harmonic q : ℝ) := hbound
    _ = Real.sqrt q * (Real.sqrt q * (harmonic q : ℝ)) := by
      calc
        _ = (Real.sqrt q) ^ 2 * (harmonic q : ℝ) := by rw [Real.sq_sqrt hq0.le]
        _ = _ := by ring

/-- A primitive character at modulus greater than one is nonprincipal.
@isnad1 id=ne.2h2v.s6.db17fce5a9b8 from=translated src=- shape=84d18b1a vocab=4b50390a
-/
theorem primitive_character_ne_one {q : ℕ} (hq : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  letI : NeZero q := ⟨by omega⟩
  intro heq
  have hc : χ.conductor = q := hχ
  rw [heq, DirichletCharacter.conductor_one] at hc
  omega

/-- Pólya--Vinogradov with the exact harmonic factor, for every natural interval.
@isnad1 id=le.2h4v.s6.5f3f5088cdd7 from=translated src=- shape=2fe84837 vocab=9daea3d6
-/
theorem norm_sum_primitive_character_Ico_le_harmonic {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (M N : ℕ) :
    ‖∑ n ∈ Ico M N, χ (n : ZMod q)‖ ≤ Real.sqrt q * (harmonic q : ℝ) := by
  have hinv : χ⁻¹.IsPrimitive := by
    change χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv]
    exact hχ
  simpa only [inv_inv] using norm_sum_primitive_character_inv_Ico_le_harmonic hq χ⁻¹ hinv M N

/-- An unconditional interval bound with absolute constant one.
@isnad1 id=le.2h4v.s7.788518c2e942 from=translated src=- shape=6abfb1b2 vocab=db59e631
-/
theorem norm_sum_primitive_character_Ico_le {q : ℕ}
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (M N : ℕ) :
    ‖∑ n ∈ Ico M N, χ (n : ZMod q)‖ ≤ Real.sqrt q * (1 + Real.log q) :=
  (norm_sum_primitive_character_Ico_le_harmonic hq χ hχ M N).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log q) (Real.sqrt_nonneg _))

end TwinPrime.Analytic
