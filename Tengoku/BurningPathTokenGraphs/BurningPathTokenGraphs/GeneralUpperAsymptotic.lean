import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.GeneralLowerAsymptotic
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathTokenUpperBound
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The constructive fixed-dimensional upper asymptotic

This file derives Part (B2) from the finite block upper bound. For fixed `k`,
it uses the integer block length

`⌈((n^k) / k!)^(1 / (k+1))⌉`

and proves both an eventual epsilon bound and the corresponding real limsup inequality.
-/

open Asymptotics Filter Topology

namespace BurningPath

/-- The positive `(k+1)`-st root of `k!`.-/
noncomputable def factorialRoot (k : ℕ) : ℝ :=
  (k.factorial : ℝ) ^ (k + 1 : ℝ)⁻¹

/-- Part (B2)'s upper constant `(k+1)/(k!)^(1/(k+1))`.-/
noncomputable def generalUpperConstant (k : ℕ) : ℝ :=
  (k + 1 : ℝ) / factorialRoot k

/-- The real block length selected by the asymptotic balancing calculation.-/
noncomputable def idealBlockLength (k n : ℕ) : ℝ :=
  (((n : ℝ) ^ k) / (k.factorial : ℝ)) ^ (k + 1 : ℝ)⁻¹

/-- The constructive integer block length used in the finite block cover.-/
noncomputable def asymptoticBlockLength (k n : ℕ) : ℕ :=
  Nat.ceil (idealBlockLength k n)

/-- The chosen integer block length differs from the balancing value by less than one.-/
theorem asymptoticBlockLength_spec (k n : ℕ) :
    idealBlockLength k n ≤ (asymptoticBlockLength k n : ℝ) ∧
      (asymptoticBlockLength k n : ℝ) < idealBlockLength k n + 1 := by
  constructor
  · exact Nat.le_ceil _
  · simpa [asymptoticBlockLength] using
      (Nat.ceil_lt_add_one (show 0 ≤ idealBlockLength k n by
        rw [idealBlockLength]
        positivity))

theorem factorialRoot_pos (k : ℕ) : 0 < factorialRoot k := by
  rw [factorialRoot]
  apply Real.rpow_pos_of_pos
  positivity

/-- The balancing block length is the standard path-token scale divided by `(k!)^(1/(k+1))`.-/
theorem idealBlockLength_eq_scale_div (k n : ℕ) :
    idealBlockLength k n = pathTokenAsymptoticScale k n / factorialRoot k := by
  rw [idealBlockLength, pathTokenAsymptoticScale, factorialRoot,
    Real.div_rpow (by positivity) (by positivity)]

@[simp]
theorem idealBlockLength_pow (k n : ℕ) :
    idealBlockLength k n ^ (k + 1) = (n : ℝ) ^ k / (k.factorial : ℝ) := by
  simpa [idealBlockLength] using
    (Real.rpow_inv_natCast_pow
      (x := (n : ℝ) ^ k / (k.factorial : ℝ)) (n := k + 1)
      (by positivity) (by omega))

theorem idealBlockLength_pos {k n : ℕ} (hn : 0 < n) :
    0 < idealBlockLength k n := by
  rw [idealBlockLength]
  apply Real.rpow_pos_of_pos
  positivity

theorem tendsto_pathTokenAsymptoticScale_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (pathTokenAsymptoticScale k) atTop atTop := by
  have hexp : 0 < (k : ℝ) / (k + 1 : ℝ) := by positivity
  apply (tendsto_congr' <| Eventually.of_forall fun n ↦
    pathTokenAsymptoticScale_eq_rpow k n).mpr
  simpa [Function.comp_def] using
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop

theorem tendsto_idealBlockLength_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (idealBlockLength k) atTop atTop := by
  rw [show idealBlockLength k = fun n ↦
      pathTokenAsymptoticScale k n / factorialRoot k by
    funext n
    exact idealBlockLength_eq_scale_div k n]
  exact (tendsto_pathTokenAsymptoticScale_atTop k hk).atTop_div_const
    (factorialRoot_pos k)

/-- The quotient `n / idealBlockLength`, which is the scale of the number of blocks.-/
noncomputable def blockAspect (k n : ℕ) : ℝ :=
  (n : ℝ) / idealBlockLength k n

theorem blockAspect_nonneg (k n : ℕ) : 0 ≤ blockAspect k n := by
  exact div_nonneg (by positivity) (by rw [idealBlockLength]; positivity)

/-- The balancing identity relating the number-of-blocks scale to the block-length scale.-/
theorem blockAspect_pow {k n : ℕ} (hn : 0 < n) :
    blockAspect k n ^ k = (k.factorial : ℝ) * idealBlockLength k n := by
  have hx : 0 < idealBlockLength k n := idealBlockLength_pos hn
  have hxpow := idealBlockLength_pow k n
  have hnPow :
      (n : ℝ) ^ k = (k.factorial : ℝ) * idealBlockLength k n ^ (k + 1) := by
    calc
      (n : ℝ) ^ k = idealBlockLength k n ^ (k + 1) * (k.factorial : ℝ) :=
        ((eq_div_iff (by positivity : (k.factorial : ℝ) ≠ 0)).mp hxpow).symm
      _ = (k.factorial : ℝ) * idealBlockLength k n ^ (k + 1) := by ring
  rw [blockAspect, div_pow, hnPow, pow_succ]
  field_simp [hx.ne']

theorem tendsto_blockAspect_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (blockAspect k) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  by_cases hM : M ≤ 0
  · exact Eventually.of_forall fun n ↦ hM.trans (blockAspect_nonneg k n)
  · have hMpos : 0 < M := lt_of_not_ge hM
    have hM0 : 0 ≤ M := hMpos.le
    have hK : 0 < (k.factorial : ℝ) := by positivity
    filter_upwards [
        (tendsto_idealBlockLength_atTop k hk).eventually_ge_atTop
          (M ^ k / (k.factorial : ℝ)),
        eventually_gt_atTop 0] with n hnlarge hn
    apply (pow_le_pow_iff_left₀ (n := k) hM0 (blockAspect_nonneg k n) hk.ne').mp
    rw [blockAspect_pow hn]
    simpa [mul_comm] using (div_le_iff₀ hK).mp hnlarge

/--
The normalized real envelope obtained from the finite block bound.  Its two summands correspond
to the block-class count and the common-radius padding term.-/
noncomputable def upperEnvelopeFactor (k n : ℕ) : ℝ :=
  ((1 + (k + 1 : ℝ) / blockAspect k n) ^ k + k) / factorialRoot k

theorem tendsto_upperEnvelopeFactor (k : ℕ) (hk : 0 < k) :
    Tendsto (upperEnvelopeFactor k) atTop (𝓝 (generalUpperConstant k)) := by
  have hzero :
      Tendsto (fun n : ℕ ↦ (k + 1 : ℝ) / blockAspect k n) atTop (𝓝 0) :=
    (tendsto_blockAspect_atTop k hk).const_div_atTop (k + 1 : ℝ)
  have hone :
      Tendsto (fun n : ℕ ↦ 1 + (k + 1 : ℝ) / blockAspect k n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hpow := hone.pow k
  have hadd :
      Tendsto (fun n : ℕ ↦
        (1 + (k + 1 : ℝ) / blockAspect k n) ^ k + k) atTop
        (𝓝 (k + 1 : ℝ)) := by
    simpa [add_comm] using hpow.add_const (k : ℝ)
  change Tendsto
    (fun n : ℕ ↦ ((1 + (k + 1 : ℝ) / blockAspect k n) ^ k + k) /
      factorialRoot k) atTop (𝓝 ((k + 1 : ℝ) / factorialRoot k))
  simpa only [Nat.cast_add, Nat.cast_one] using hadd.div_const (factorialRoot k)

theorem ceilDiv_le_div_add_one (n s : ℕ) (hs : 0 < s) :
    n ⌈/⌉ s ≤ n / s + 1 := by
  rw [ceilDiv_le_iff_le_mul hs]
  calc
    n = s * (n / s) + n % s := (Nat.div_add_mod n s).symm
    _ ≤ s * (n / s) + s := Nat.add_le_add_left (Nat.le_of_lt (Nat.mod_lt n hs)) _
    _ = s * (n / s + 1) := by ring

theorem cast_div_le_div (n s : ℕ) (hs : 0 < s) :
    ((n / s : ℕ) : ℝ) ≤ (n : ℝ) / (s : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hs)).2
  exact_mod_cast Nat.div_mul_le_self n s

theorem one_le_asymptoticBlockLength {k n : ℕ} (hn : 0 < n) :
    1 ≤ asymptoticBlockLength k n := by
  simpa [asymptoticBlockLength] using
    (Nat.ceil_pos.mpr (idealBlockLength_pos (k := k) hn))

theorem cast_pred_asymptoticBlockLength_lt_ideal {k n : ℕ} (hn : 0 < n) :
    ((asymptoticBlockLength k n - 1 : ℕ) : ℝ) < idealBlockLength k n := by
  have hs := one_le_asymptoticBlockLength (k := k) hn
  have hceil :
      (asymptoticBlockLength k n : ℝ) < idealBlockLength k n + 1 := by
    simpa [asymptoticBlockLength] using
      (Nat.ceil_lt_add_one (show 0 ≤ idealBlockLength k n by
        rw [idealBlockLength]
        positivity))
  rw [Nat.cast_sub hs]
  norm_num at hceil ⊢
  linarith

/--
At the constructive block length, the normalized burning number is bounded by the explicit
envelope above.-/
theorem pathTokenBurningRatio_le_upperEnvelopeFactor {k n : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) (hn : 0 < n) :
    pathTokenBurningRatio k n ≤ upperEnvelopeFactor k n := by
  let x := idealBlockLength k n
  let s := asymptoticBlockLength k n
  let m := n ⌈/⌉ s
  let A := blockAspect k n
  let S := pathTokenAsymptoticScale k n
  let D := factorialRoot k
  let K : ℝ := k.factorial
  have hx : 0 < x := idealBlockLength_pos hn
  have hs : 1 ≤ s := one_le_asymptoticBlockLength hn
  have hspos : 0 < s := by omega
  have hS : 0 < S := pathTokenAsymptoticScale_pos hn
  have hD : 0 < D := factorialRoot_pos k
  have hK : 0 < K := by positivity
  have hxs : x ≤ (s : ℝ) := by
    dsimp [x, s, asymptoticBlockLength]
    exact Nat.le_ceil _
  have hmNat : m ≤ n / s + 1 := ceilDiv_le_div_add_one n s hspos
  have hm : (m : ℝ) ≤ A + 1 := by
    have hdivCast : ((n / s : ℕ) : ℝ) ≤ (n : ℝ) / (s : ℝ) :=
      cast_div_le_div n s hspos
    have hdiv : (n : ℝ) / (s : ℝ) ≤ (n : ℝ) / x :=
      div_le_div_of_nonneg_left (by positivity) hx hxs
    have hmCast : (m : ℝ) ≤ ((n / s + 1 : ℕ) : ℝ) := by
      exact_mod_cast hmNat
    push_cast at hmCast
    dsimp [A, blockAspect]
    linarith
  have hinput : ((m + k - 1 : ℕ) : ℝ) ≤ A + (k + 1 : ℝ) := by
    have hsub : m + k - 1 ≤ m + k := Nat.sub_le _ _
    have hsubCast : ((m + k - 1 : ℕ) : ℝ) ≤ ((m + k : ℕ) : ℝ) := by
      exact_mod_cast hsub
    push_cast at hsubCast
    linarith
  have hchoose :
      ((m + k - 1).choose k : ℝ) ≤ (A + (k + 1 : ℝ)) ^ k / K := by
    calc
      ((m + k - 1).choose k : ℝ) ≤ ((m + k - 1 : ℕ) : ℝ) ^ k / K := by
        simpa [K] using (Nat.choose_le_pow_div k (m + k - 1) :
          ((m + k - 1).choose k : ℝ) ≤
            ((m + k - 1 : ℕ) : ℝ) ^ k / (k.factorial : ℝ))
      _ ≤ (A + (k + 1 : ℝ)) ^ k / K := by
        gcongr
  have hradius : ((k * (s - 1) : ℕ) : ℝ) ≤ (k : ℝ) * x := by
    have hpred := (cast_pred_asymptoticBlockLength_lt_ideal (k := k) hn).le
    simpa only [Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hpred (show 0 ≤ (k : ℝ) by positivity)
  have hburnNat : pathTokenBurningNumberTotal k n ≤ blockUpperBound n k s := by
    rw [pathTokenBurningNumberTotal_eq hkn]
    exact pathTokenBurningNumber_le_blockUpperBound hkn hs
  have hburn :
      (pathTokenBurningNumberTotal k n : ℝ) ≤
        (A + (k + 1 : ℝ)) ^ k / K + (k : ℝ) * x := by
    calc
      (pathTokenBurningNumberTotal k n : ℝ) ≤ (blockUpperBound n k s : ℝ) := by
        exact_mod_cast hburnNat
      _ = ((m + k - 1).choose k : ℝ) + (k * (s - 1) : ℕ) := by
        simp [blockUpperBound, m]
      _ ≤ (A + (k + 1 : ℝ)) ^ k / K + (k : ℝ) * x :=
        add_le_add hchoose hradius
  have hA : 0 < A := by
    dsimp [A, blockAspect]
    positivity
  have hApow : A ^ k = K * x := by
    simpa [A, K, x] using blockAspect_pow (k := k) hn
  have hxS : x = S / D := by
    simpa [x, S, D] using idealBlockLength_eq_scale_div k n
  have hfactor :
      ((A + (k + 1 : ℝ)) ^ k / K + (k : ℝ) * x) / S =
        ((1 + (k + 1 : ℝ) / A) ^ k + k) / D := by
    have hsum : A + (k + 1 : ℝ) = A * (1 + (k + 1 : ℝ) / A) := by
      field_simp [hA.ne']
    rw [hsum, mul_pow, hApow, hxS]
    field_simp [hS.ne', hD.ne', hK.ne']
  change (pathTokenBurningNumberTotal k n : ℝ) / S ≤
    ((1 + (k + 1 : ℝ) / A) ^ k + k) / D
  calc
    (pathTokenBurningNumberTotal k n : ℝ) / S ≤
        ((A + (k + 1 : ℝ)) ^ k / K + (k : ℝ) * x) / S :=
      div_le_div_of_nonneg_right hburn hS.le
    _ = ((1 + (k + 1 : ℝ) / A) ^ k + k) / D := hfactor

/--
Every epsilon above the sharp constructive constant is eventually an upper bound for the
normalized burning number.-/
theorem eventually_pathTokenBurningRatio_le_generalUpperConstant_add
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      pathTokenBurningRatio k n ≤ generalUpperConstant k + ε := by
  have henv := (tendsto_upperEnvelopeFactor k hk).eventually
    (Iio_mem_nhds (lt_add_of_pos_right (generalUpperConstant k) hε))
  filter_upwards [henv, eventually_ge_atTop k, eventually_gt_atTop 0] with n hn hkn hnpos
  exact (pathTokenBurningRatio_le_upperEnvelopeFactor hk hkn hnpos).trans hn.le

theorem limsup_pathTokenBurningRatio_le_generalUpperConstant (k : ℕ) (hk : 0 < k) :
    limsup (pathTokenBurningRatio k) atTop ≤ generalUpperConstant k := by
  have hcob :
      atTop.IsCoboundedUnder (· ≤ ·) (pathTokenBurningRatio k) :=
    isCoboundedUnder_le_of_le atTop (pathTokenBurningRatio_nonneg k)
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le hcob
    (eventually_pathTokenBurningRatio_le_generalUpperConstant_add k hk hε)

/--
Part (B2), epsilon form: for fixed `k ≥ 2`, the normalized burning number is eventually at most
`(k+1)/(k!)^(1/(k+1)) + ε`.-/
theorem generalUpperAsymptotic_eventually (k : ℕ) (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (pathTokenBurningNumberTotal k n : ℝ) /
          (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) ≤
        (k + 1 : ℝ) / (k.factorial : ℝ) ^ (k + 1 : ℝ)⁻¹ + ε := by
  simpa only [← pathTokenAsymptoticScale_eq_rpow, pathTokenBurningRatio,
    generalUpperConstant, factorialRoot] using
    eventually_pathTokenBurningRatio_le_generalUpperConstant_add k (by omega) hε

/--
Part (B2), limsup form, with the constructive block-cover constant.-/
theorem generalUpperAsymptotic_limsup (k : ℕ) (hk : 2 ≤ k) :
    limsup
        (fun n : ℕ ↦ (pathTokenBurningNumberTotal k n : ℝ) /
          (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)))
        atTop ≤
      (k + 1 : ℝ) / (k.factorial : ℝ) ^ (k + 1 : ℝ)⁻¹ := by
  simp_rw [← pathTokenAsymptoticScale_eq_rpow]
  change limsup (pathTokenBurningRatio k) atTop ≤ generalUpperConstant k
  exact limsup_pathTokenBurningRatio_le_generalUpperConstant k (by omega)

end BurningPath
