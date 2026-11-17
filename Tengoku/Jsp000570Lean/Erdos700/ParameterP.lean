import Tengoku.Jsp000570Lean.Erdos700.Bounds
import Tengoku.Jsp000570Lean.Erdos700.PairPDigits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos700.FourPrime.ParameterP

/-- The explicit size requirements of both pairs starting from P follow
from the original parameter assumptions, uniformly for every 0<=d<=c.-/
theorem source_p_size_bounds
    (a b c d q : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hd0 : 0 ≤ d) (hdc : d ≤ c) (hq : 12 * c ^ 3 ≤ q) :
    a + b + c < q ∧
    d ^ 2 * (a + b + c) + a * b * c < q ∧
    b * (b - a) * (c - b) + d * (a * b + a * c + b * c) < q ∧
    d * (a * b + a * c + b * c) < q ∧
    2 * d * (a + b + c) < q ∧
    2 * d * (a + b + c) + (3 * c ^ 2 - 2 * c * (a + b) + a * b) < q := by
  let S := a + b + c
  let T := a * b + a * c + b * c
  let Z := a * b * c
  let C := b * (b - a) * (c - b)
  let U := 3 * c ^ 2 - 2 * c * (a + b) + a * b
  have hc9 := Bounds.c_at_least_9 a b c ha hb hc
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hc0 : 0 ≤ c := by omega
  have hS0 : 0 ≤ S := by
    have hs := Bounds.S_positive a b c ha hb hc
    dsimp [S]
    linarith only [hs]
  have hSupper : S ≤ 3 * c := by
    have hs := Bounds.S_less_3c a b c ha hb hc
    dsimp [S]
    linarith only [hs]
  have hT0 : 0 ≤ T := by
    have ht := Bounds.T_positive a b c ha hb hc
    dsimp [T]
    linarith only [ht]
  have hTupper : T ≤ 3 * c ^ 2 := by
    have ht := Bounds.T_less_3c_squared a b c ha hb hc
    dsimp [T]
    linarith only [ht]
  have hZupper : Z < c ^ 3 := by
    have hz := Bounds.Z_less_c_cubed a b c ha hb hc
    dsimp [Z]
    nlinarith only [hz]
  have hCupper : C < c ^ 3 := by
    have hh := Bounds.C_less_c_cubed a b c ha hb hc
    dsimp [C]
    nlinarith only [hh]
  have hUupper : U < 3 * c ^ 2 := by
    have hh := Bounds.U_less_than_3c_squared a b c ha hb hc
    dsimp [U]
    nlinarith only [hh]
  have hds : d * S ≤ 3 * c ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hdc hS0
    have h₂ := mul_le_mul_of_nonneg_left hSupper hc0
    nlinarith only [h₁, h₂]
  have hd2 : d ^ 2 ≤ c ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hdc) (add_nonneg hc0 hd0)
    nlinarith only [hh]
  have hd2s : d ^ 2 * S ≤ 3 * c ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hd2 hS0
    have h₂ := mul_le_mul_of_nonneg_left hSupper (sq_nonneg c)
    nlinarith only [h₁, h₂]
  have hdt : d * T ≤ 3 * c ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_right hdc hT0
    have h₂ := mul_le_mul_of_nonneg_left hTupper hc0
    nlinarith only [h₁, h₂]
  have hbase := Bounds.large_base_thresholds c q hc2 hq
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by omega : 0 < c)
  have hc3 : 0 < c ^ 3 := pow_pos (by omega : 0 < c) 3
  have hcc : c ≤ c ^ 2 := by
    have hh := mul_nonneg hc0 (show (0 : ℤ) ≤ c - 1 by omega)
    nlinarith only [hh]
  change S < q ∧ d ^ 2 * S + Z < q ∧ C + d * T < q ∧
    d * T < q ∧ 2 * d * S < q ∧ 2 * d * S + U < q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hSupper, hcc, hbase.2.1, hc2]
  · linarith only [hd2s, hZupper, hbase.1, hc3]
  · linarith only [hCupper, hdt, hbase.1, hc3]
  · linarith only [hdt, hbase.1, hc3]
  · nlinarith only [hds, hbase.2.1, hc2]
  · nlinarith only [hds, hUupper, hbase.2.1, hc2]

/-- The pair `(P,P+b)` exclusion under just the original global
parameters and actual source/target digit hypotheses.-/
theorem pairPB_global_digits (a b c q u v w k : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hq : 12 * c ^ 3 ≤ q)
    (hu0 : 0 ≤ u) (hu : u ≤ a + b + c)
    (hv0 : 0 ≤ v) (hv : v ≤ a * b + a * c + b * c)
    (hw0 : 0 ≤ w) (hw : w ≤ a * b * c)
    (hdiv : q ∣ u * (q - b) ^ 2 + v * (q - b) + w)
    (hk : k = (q - b) * (u * (q - b) ^ 2 + v * (q - b) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ b * (b - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤
      q - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2))
    (hhigh : (k / q / q / q) % q ≤ a + c - 3 * b - 1) : False := by
  have hab' := Bounds.a_less_b a b c ha hb hc
  have hbc' := Bounds.b_less_c a b c ha hb hc
  have hab : a < b := by linarith only [hab']
  have hbc : b < c := by linarith only [hbc']
  have hs := source_p_size_bounds a b c b q ha hb hc (by omega) hbc.le hq
  exact PairPDigits.pairPB_actual_digits a b c q u v w k (by omega) hab hbc
    hu0 hu hv0 hv hw0 hw hs.2.1 hs.2.2.1 hs.2.2.2.2.1 hs.1
    hdiv hk hk_ne hlow hmiddle hhigh

/-- The pair `(P,P+c)` exclusion under the original global parameters.-/
theorem pairPC_global_digits (a b c q u v w k : ℤ)
    (ha : 1 ≤ a) (hb : 3 * a ≤ b) (hc : 3 * b - a + 1 ≤ c)
    (hq : 12 * c ^ 3 ≤ q)
    (hu0 : 0 ≤ u) (hu : u ≤ a + b + c)
    (hv0 : 0 ≤ v) (hv : v ≤ a * b + a * c + b * c)
    (hw0 : 0 ≤ w) (hw : w ≤ a * b * c)
    (hdiv : q ∣ u * (q - c) ^ 2 + v * (q - c) + w)
    (hk : k = (q - c) * (u * (q - c) ^ 2 + v * (q - c) + w))
    (hk_ne : k ≠ 0)
    (hlow : (k / q) % q ≤ q - c * (c - a) * (c - b))
    (hmiddle : (k / q / q) % q ≤ 3 * c ^ 2 - 2 * c * (a + b) + a * b - 1) :
    False := by
  have hbpos : 0 < b := by omega
  have hsep' := Bounds.c_greater_than_a_plus_b a b c ha hb hc
  have hsep : a + b < c := by linarith only [hsep']
  have hcpos : 0 ≤ c := by omega
  have hs := source_p_size_bounds a b c c q ha hb hc hcpos (le_refl _) hq
  have hU := Bounds.U_positive a b c ha hb hc
  have hU0 : 0 ≤ 3 * c ^ 2 - 2 * c * (a + b) + a * b := by
    nlinarith only [hU]
  exact PairPDigits.pairPC_actual_digits a b c q u v w k (by omega) hbpos hsep
    hu0 hu hv0 hv hw0 hw hs.2.1 hs.2.2.2.1 hs.2.2.2.2.2 hs.1 hU0
    hdiv hk hk_ne hlow hmiddle

end Erdos700.FourPrime.ParameterP
