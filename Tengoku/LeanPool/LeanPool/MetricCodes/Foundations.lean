/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.MetricCodes.MatrixPerron
public import Tengoku
import Tengoku

/-!
# Foundations for binary and spherical code bounds

Elementary coding-theory definitions, projection certificates, and the finite Johnson bound.
-/

@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

section

open scoped BigOperators InnerProductSpace

instance numeralTwoAtLeast : Nat.AtLeastTwo 2 := ⟨by decide⟩

/-- The ambient used in the metric-code argument. -/
abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The binary word used in the metric-code argument. -/
abbrev BinaryWord (n : ℕ) := Fin n → Bool

/-- The hamming dist used in the metric-code argument. -/
abbrev hammingDist {n : ℕ} (x y : BinaryWord n) : ℕ :=
  _root_.hammingDist x y

theorem hammingDist_self {n : ℕ} (x : BinaryWord n) :
    hammingDist x x = 0 := by
  exact _root_.hammingDist_self x

/-- The binary weight used in the metric-code argument. -/
def binaryWeight {n : ℕ} (x : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

/-- The predicate asserting binary code. -/
def IsBinaryCode {n : ℕ} (d : ℕ) (C : Finset (BinaryWord n)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → d ≤ hammingDist x y

/-- The johnson sphere used in the Johnson-code argument. -/
abbrev JohnsonSphere (n w : ℕ) :=
  {x : BinaryWord n // binaryWeight x = w}

/-- The hamming correlation used in the metric-code argument. -/
def hammingCorrelation {n : ℕ} (x y : BinaryWord n) : ℝ :=
  1 - 2 * (hammingDist x y : ℝ) / (n : ℝ)

@[simp] theorem hammingCorrelation_self {n : ℕ} (x : BinaryWord n) :
    hammingCorrelation x x = 1 := by
  simp only [hammingCorrelation, hammingDist_self, CharP.cast_eq_zero, mul_zero, zero_div, sub_zero]

/-- The spherical entropy used in the metric-code argument. -/
def sphericalEntropy (u : ℝ) : ℝ :=
  (1 + u) * Real.logb 2 (1 + u) - u * Real.logb 2 u

@[simp] theorem sphericalEntropy_zero : sphericalEntropy 0 = 0 := by
  simp only [sphericalEntropy, add_zero, Real.logb_one, mul_zero, Real.logb_zero, sub_self]

theorem sphericalEntropy_eq_log_add {u : ℝ} (hu : 0 < u) :
    sphericalEntropy u =
      Real.logb 2 (1 + u) +
        u * Real.logb 2 ((1 + u) / u) := by
  have hu' : u ≠ 0 := hu.ne'
  have hone : 1 + u ≠ 0 := by linarith
  rw [Real.logb_div hone hu']
  unfold sphericalEntropy
  ring

/-- The binary entropy used in the metric-code argument. -/
def binaryEntropy (u : ℝ) : ℝ :=
  -(u * Real.logb 2 u) -
    (1 - u) * Real.logb 2 (1 - u)

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp only [binaryEntropy, Real.logb_zero, mul_zero, neg_zero, sub_zero, Real.logb_one, sub_self]

theorem binaryEntropy_nonneg {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    0 ≤ binaryEntropy u := by
  have h₁ : Real.logb 2 u ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu hu'
  have h₂ : Real.logb 2 (1 - u) ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2)
      (by linarith) (by linarith)
  unfold binaryEntropy
  have hleft : u * Real.logb 2 u ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu h₁
  have hright : (1 - u) * Real.logb 2 (1 - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h₂
  linarith

/-- The gamma used in the metric-code argument. -/
def Gamma (a b : ℝ) : ℝ :=
  ((a - b) * (1 + a + b)) /
    ((1 + 2 * a) * Real.sqrt (a * (1 + a)))

theorem Gamma_eq_sub (a b : ℝ) :
    Gamma a b =
      (a * (1 + a) - b * (1 + b)) /
        ((1 + 2 * a) * Real.sqrt (a * (1 + a))) := by
  unfold Gamma
  congr 1
  ring

/-- The classical threshold used in the metric-code argument. -/
def classicalThreshold (s : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - s ^ 2) - 1) / 2

@[simp] theorem classicalThreshold_zero : classicalThreshold 0 = 0 := by
  simp only [classicalThreshold, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
    Real.sqrt_one, one_ne_zero, div_self, sub_self, zero_div]

theorem classicalThreshold_pos {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    0 < classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hsqrt : 0 < Real.sqrt (1 - s ^ 2) := Real.sqrt_pos.2 hrad
  have hsqrt' : Real.sqrt (1 - s ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith
  have hrecip : 1 < 1 / Real.sqrt (1 - s ^ 2) := by
    apply (lt_div_iff₀ hsqrt).2
    simpa only [one_mul] using hsqrt'
  unfold classicalThreshold
  linarith

/-- The boolean harmonic dimension used in the metric-code argument. -/
def booleanHarmonicDimension (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => n.choose (k + 1) - n.choose k

theorem booleanHarmonicDimension_succ (n k : ℕ) :
    booleanHarmonicDimension n (k + 1) =
      n.choose (k + 1) - n.choose k := rfl

theorem sum_booleanHarmonicDimension (n L : ℕ) (hL : 2 * L ≤ n) :
    (∑ k ∈ Finset.range (L + 1), booleanHarmonicDimension n k) =
      n.choose L := by
  induction L generalizing n with
  | zero =>
      simp only [zero_add, Finset.range_one, booleanHarmonicDimension, Finset.sum_singleton,
        Nat.choose_zero_right]
  | succ L ih =>
      have hprev : 2 * L ≤ n := by omega
      have hhalf : L < n / 2 := by omega
      have hmono : n.choose L ≤ n.choose (L + 1) :=
        Nat.choose_le_succ_of_lt_half_left hhalf
      rw [Finset.sum_range_succ, ih n hprev]
      change n.choose L + (n.choose (L + 1) - n.choose L) =
        n.choose (L + 1)
      omega

/-- The hamming fibre dimension used in the metric-code argument. -/
abbrev hammingFibreDimension (n k : ℕ) : ℕ :=
  booleanHarmonicDimension n k

/-- The johnson fibre dimension used in the metric-code argument. -/
def johnsonFibreDimension (n w p q : ℕ) : ℕ :=
  booleanHarmonicDimension w p *
    booleanHarmonicDimension (n - w) q

/-- The hamming jacobi entry used in the metric-code argument. -/
def hammingJacobiEntry (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
    ((n : ℝ) * Real.sqrt (((i : ℝ) + 1) * ((n : ℝ) - (i : ℝ))))

/-- The hamming jacobi matrix used in the metric-code argument. -/
def hammingJacobiMatrix (n k L : ℕ) :
    Matrix (Fin (L - k + 1)) (Fin (L - k + 1)) ℝ :=
  fun p q =>
    if p.val + 1 = q.val then
      hammingJacobiEntry n k (k + p.val)
    else if q.val + 1 = p.val then
      hammingJacobiEntry n k (k + q.val)
    else
      0

/-- The hamming gamma used in the metric-code argument. -/
def hammingGamma (a b : ℝ) : ℝ :=
  (2 * (a - b) * (1 - a - b)) /
    Real.sqrt (a * (1 - a))

/-- The johnson j1 used in the metric-code argument. -/
def johnsonJ1 (w p : ℕ) : ℝ :=
  (w : ℝ) / 2 - (p : ℝ)

/-- The johnson j2 used in the metric-code argument. -/
def johnsonJ2 (n w q : ℕ) : ℝ :=
  ((n - w : ℕ) : ℝ) / 2 - (q : ℝ)

/-- The johnson j used in the metric-code argument. -/
def johnsonJ (n j : ℕ) : ℝ :=
  (n : ℝ) / 2 - (j : ℝ)

/-- The johnson m used in the metric-code argument. -/
def johnsonM (n w : ℕ) : ℝ :=
  (n : ℝ) / 2 - (w : ℝ)

/-- The johnson sigma used in the metric-code argument. -/
def johnsonSigma (n w p q : ℕ) : ℝ :=
  johnsonJ1 w p + johnsonJ2 n w q

/-- The johnson delta used in the metric-code argument. -/
def johnsonDelta (n w p q : ℕ) : ℝ :=
  johnsonJ2 n w q - johnsonJ1 w p

/-- The johnson last degree used in the metric-code argument. -/
def johnsonLastDegree (n w p q : ℕ) : ℕ :=
  min w (min (w - p + q) (n - w + p - q))

/-- The johnson mu used in the metric-code argument. -/
def johnsonMu (n w p q j : ℕ) : ℝ :=
  (johnsonM n w / 2) *
    (johnsonJ2 n w q * (johnsonJ2 n w q + 1) -
      johnsonJ1 w p * (johnsonJ1 w p + 1)) /
    (johnsonJ n j * (johnsonJ n j + 1))

/-- The johnson nu used in the metric-code argument. -/
def johnsonNu (n w p q j : ℕ) : ℝ :=
  Real.sqrt
      ((johnsonJ n j ^ 2 - johnsonM n w ^ 2) *
        (johnsonJ n j ^ 2 - johnsonDelta n w p q ^ 2) *
        ((johnsonSigma n w p q + 1) ^ 2 - johnsonJ n j ^ 2)) /
    (2 * johnsonJ n j *
      Real.sqrt ((2 * johnsonJ n j - 1) *
        (2 * johnsonJ n j + 1)))

/-- The johnson diagonal used in the metric-code argument. -/
def johnsonDiagonal (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonMu n w p q j - johnsonM n w ^ 2) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

/-- The johnson edge used in the metric-code argument. -/
def johnsonEdge (n w p q j : ℕ) : ℝ :=
  ((n : ℝ) * johnsonNu n w p q j) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

/-- The johnson zonal diagonal used in the metric-code argument. -/
def johnsonZonalDiagonal (n w j : ℕ) : ℝ :=
  johnsonDiagonal n w 0 0 j

/-- The johnson zonal edge used in the metric-code argument. -/
def johnsonZonalEdge (n w j : ℕ) : ℝ :=
  johnsonEdge n w 0 0 j

/-- The johnson hatted diagonal used in the metric-code argument. -/
def johnsonHattedDiagonal (n w p q j : ℕ) : ℝ :=
  if j = 0 then 0
  else johnsonDiagonal n w p q j ^ 2 / johnsonZonalDiagonal n w j

/-- The johnson hatted edge used in the metric-code argument. -/
def johnsonHattedEdge (n w p q j : ℕ) : ℝ :=
  johnsonEdge n w p q j ^ 2 / johnsonZonalEdge n w j

theorem johnsonHattedDiagonal_nonneg {n w p q j : ℕ}
    (hzero : 0 < johnsonZonalDiagonal n w j) :
    0 ≤ johnsonHattedDiagonal n w p q j := by
  unfold johnsonHattedDiagonal
  split <;> positivity

/-- The johnson jacobi matrix used in the metric-code argument. -/
def johnsonJacobiMatrix (n w p q L : ℕ) :
    Matrix (Fin (L - (p + q) + 1))
      (Fin (L - (p + q) + 1)) ℝ :=
  fun i j =>
    if i = j then
      johnsonHattedDiagonal n w p q (p + q + i.val)
    else if i.val + 1 = j.val then
      johnsonHattedEdge n w p q (p + q + i.val)
    else if j.val + 1 = i.val then
      johnsonHattedEdge n w p q (p + q + j.val)
    else
      0

@[simp] theorem johnsonJacobiMatrix_diag (n w p q L : ℕ)
    (i : Fin (L - (p + q) + 1)) :
    johnsonJacobiMatrix n w p q L i i =
      johnsonHattedDiagonal n w p q (p + q + i.val) := by
  simp only [johnsonJacobiMatrix, ↓reduceIte]

theorem johnsonJacobiMatrix_symmetric (n w p q L : ℕ) :
    (johnsonJacobiMatrix n w p q L).transpose =
      johnsonJacobiMatrix n w p q L := by
  ext i j
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    by_cases hup : i.val + 1 = j.val
    · have hdown : j.val + 1 ≠ i.val := by omega
      simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hup, hij]
    · by_cases hdown : j.val + 1 = i.val
      · simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hij, hup]
      · simp only [johnsonJacobiMatrix, hji, ↓reduceIte, hdown, hup, hij]

end

section

open scoped BigOperators

namespace Boolean

/-- The function used in the binary-code argument. -/
abbrev Function (n : ℕ) := Finset (Fin n) → ℝ

/-- The level used in the binary-code argument. -/
abbrev Level (n k : ℕ) := {S : Finset (Fin n) // S.card = k}

theorem card_level (n k : ℕ) :
    Fintype.card (Level n k) = n.choose k := by
  simp only [Level, Fintype.card_finset_len, Fintype.card_fin]

/-- The raise at used in the binary-code argument. -/
def raiseAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then f (S.erase a) else 0

/-- The lower at used in the binary-code argument. -/
def lowerAt {n : ℕ} (a : Fin n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  if a ∈ S then 0 else f (insert a S)

/-- The raise used in the binary-code argument. -/
def raise {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, raiseAt a f S

/-- The lower used in the binary-code argument. -/
def lower {n : ℕ} (f : Function n) (S : Finset (Fin n)) : ℝ :=
  ∑ a : Fin n, lowerAt a f S

/-- The predicate asserting level. -/
def IsLevel {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  ∀ S : Finset (Fin n), S.card ≠ k → f S = 0

/-- The predicate asserting harmonic. -/
def IsHarmonic {n : ℕ} (k : ℕ) (f : Function n) : Prop :=
  IsLevel k f ∧ ∀ S : Finset (Fin n), lower f S = 0

variable {n : ℕ}

theorem lowerAt_raiseAt_of_ne (f : Function n) (a b : Fin n)
    (hab : a ≠ b) (S : Finset (Fin n)) :
    lowerAt a (raiseAt b f) S = raiseAt b (lowerAt a f) S := by
  classical
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, hb, Finset.mem_erase, ne_eq, hab,
      not_false_eq_true, and_self]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, hb]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, hb, or_true,
      Finset.erase_insert_of_ne hab, Finset.mem_erase, ne_eq, hab, not_false_eq_true, and_false]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, hab.symm, hb, or_self]

theorem lowerAt_raiseAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raiseAt a f) S = if a ∈ S then 0 else f S := by
  classical
  by_cases ha : a ∈ S
  · simp only [lowerAt, ha, ↓reduceIte]
  · simp only [lowerAt, ha, ↓reduceIte, raiseAt, Finset.mem_insert, or_false,
      Finset.erase_insert ha]

theorem raiseAt_lowerAt_self (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lowerAt a f) S = if a ∈ S then f S else 0 := by
  classical
  by_cases ha : a ∈ S
  · simp only [raiseAt, ha, ↓reduceIte, lowerAt, Finset.mem_erase, ne_eq, not_true_eq_false,
      and_true, Finset.insert_erase ha]
  · simp only [raiseAt, ha, ↓reduceIte]

theorem lowerAt_raise (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    lowerAt a (raise f) S =
      ∑ b : Fin n, lowerAt a (raiseAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [lowerAt, raise, ha]

theorem raiseAt_lower (f : Function n) (a : Fin n)
    (S : Finset (Fin n)) :
    raiseAt a (lower f) S =
      ∑ b : Fin n, raiseAt a (lowerAt b f) S := by
  classical
  by_cases ha : a ∈ S <;> simp [raiseAt, lower, ha]

theorem sum_mem_indicator (S : Finset (Fin n)) (x : ℝ) :
    (∑ a : Fin n, if a ∈ S then x else 0) = (S.card : ℝ) * x := by
  classical
  calc
    (∑ a : Fin n, if a ∈ S then x else 0) = ∑ a ∈ S, x := by
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) * x := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem lower_raise_sub_raise_lower (f : Function n)
    (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (S.card : ℝ)) * f S := by
  classical
  change
    (∑ a : Fin n, lowerAt a (raise f) S) -
      (∑ a : Fin n, raiseAt a (lower f) S) = _
  simp_rw [lowerAt_raise, raiseAt_lower]
  have hswap :
      (∑ a : Fin n, ∑ b : Fin n, raiseAt a (lowerAt b f) S) =
        ∑ b : Fin n, ∑ a : Fin n, raiseAt a (lowerAt b f) S := by
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  have hcross (a : Fin n) :
      (∑ b : Fin n, lowerAt a (raiseAt b f) S) -
        (∑ b : Fin n, raiseAt b (lowerAt a f) S) =
          lowerAt a (raiseAt a f) S - raiseAt a (lowerAt a f) S := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      rw [lowerAt_raiseAt_of_ne f a b hba.symm S]
      exact sub_self _
    · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  simp_rw [hcross, lowerAt_raiseAt_self, raiseAt_lowerAt_self]
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else f S) -
          (if a ∈ S then f S else 0) =
        f S - 2 * (if a ∈ S then f S else 0) := by
    by_cases ha : a ∈ S <;> simp [ha]; ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, sum_mem_indicator]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem lower_raise_sub_raise_lower_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) (S : Finset (Fin n)) :
    lower (raise f) S - raise (lower f) S =
      ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  by_cases hS : S.card = k
  · simpa only [hS] using lower_raise_sub_raise_lower f S
  · rw [lower_raise_sub_raise_lower, hf S hS]
    simp only [mul_zero]

theorem lower_raise_of_harmonic {k : ℕ} (f : Function n)
    (hf : IsHarmonic k f) (S : Finset (Fin n)) :
    lower (raise f) S = ((n : ℝ) - 2 * (k : ℝ)) * f S := by
  have hcomm := lower_raise_sub_raise_lower_of_level f hf.1 S
  have hzero : raise (lower f) S = 0 := by
    simp only [raise, raiseAt, hf.2, ite_self, Finset.sum_const_zero]
  simpa only [hzero, sub_zero] using hcomm

theorem raise_add (f g : Function n) :
    raise (f + g) = raise f + raise g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then f (S.erase a) + g (S.erase a) else 0) =
      (∑ a : Fin n, if a ∈ S then f (S.erase a) else 0) +
        (∑ a : Fin n, if a ∈ S then g (S.erase a) else 0)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem raise_smul (c : ℝ) (f : Function n) :
    raise (c • f) = c • raise f := by
  classical
  funext S
  simp only [raise, raiseAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_add (f g : Function n) :
    lower (f + g) = lower f + lower g := by
  classical
  funext S
  change
    (∑ a : Fin n, if a ∈ S then 0 else f (insert a S) + g (insert a S)) =
      (∑ a : Fin n, if a ∈ S then 0 else f (insert a S)) +
        (∑ a : Fin n, if a ∈ S then 0 else g (insert a S))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

theorem lower_smul (c : ℝ) (f : Function n) :
    lower (c • f) = c • lower f := by
  classical
  funext S
  simp only [lower, lowerAt, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ S <;> simp [ha]

/-- The raise linear used in the binary-code argument. -/
def raiseLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := raise
  map_add' := raise_add
  map_smul' := raise_smul

/-- The lower linear used in the binary-code argument. -/
def lowerLinear (n : ℕ) : Function n →ₗ[ℝ] Function n where
  toFun := lower
  map_add' := lower_add
  map_smul' := lower_smul

@[simp] theorem raiseLinear_apply (f : Function n) :
    raiseLinear n f = raise f := rfl

theorem IsLevel.raise {k : ℕ} {f : Function n} (hf : IsLevel k f) :
    IsLevel (k + 1) (raise f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.raise
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ k := by
      intro he
      apply hS
      calc
        S.card = (S.erase a).card + 1 :=
          (Finset.card_erase_add_one ha).symm
        _ = k + 1 := by rw [he]
    simp only [raiseAt, ha, ↓reduceIte, hf (S.erase a) herase]
  · simp only [raiseAt, ha, ↓reduceIte]

theorem IsLevel.lower {k : ℕ} {f : Function n}
    (hf : IsLevel (k + 1) f) :
    IsLevel k (lower f) := by
  classical
  intro S hS
  unfold MetricCodes.Boolean.lower
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a ∈ S
  · simp only [lowerAt, ha, ↓reduceIte]
  · have hinsert : (insert a S).card ≠ k + 1 := by
      intro hi
      have hcard : S.card + 1 = k + 1 := by
        simpa only [Finset.card_insert_of_notMem ha] using hi
      exact hS (Nat.add_right_cancel hcard)
    simp only [lowerAt, ha, ↓reduceIte, hf (insert a S) hinsert]

/-- The raised used in the binary-code argument. -/
def raised {n : ℕ} (f : Function n) : ℕ → Function n
  | 0 => f
  | r + 1 => raise (raised f r)

@[simp] theorem raised_succ (f : Function n) (r : ℕ) :
    raised f (r + 1) = raise (raised f r) := rfl

theorem IsLevel.raised {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (raised f r) := by
  induction r with
  | zero =>
      change IsLevel k f
      exact hf
  | succ r ih =>
      simpa only [raised_succ, Nat.add_assoc] using ih.raise

/-- The harmonic coefficient used in the binary-code argument. -/
def harmonicCoefficient (n k r : ℕ) : ℝ :=
  (r : ℝ) * ((n : ℝ) - 2 * (k : ℝ) - (r : ℝ) + 1)

@[simp] theorem harmonicCoefficient_zero (n k : ℕ) :
    harmonicCoefficient n k 0 = 0 := by
  simp only [harmonicCoefficient, CharP.cast_eq_zero, sub_zero, zero_mul]

theorem harmonicCoefficient_succ (n k r : ℕ) :
    harmonicCoefficient n k (r + 1) =
      harmonicCoefficient n k r +
        ((n : ℝ) - 2 * ((k + r : ℕ) : ℝ)) := by
  simp only [harmonicCoefficient, Nat.cast_add, Nat.cast_one]
  ring

theorem lower_raised_succ_of_harmonic {k : ℕ}
    (f : Function n) (hf : IsHarmonic k f) (r : ℕ) :
    lower (raised f (r + 1)) =
      harmonicCoefficient n k (r + 1) • raised f r := by
  induction r with
  | zero =>
      funext S
      simpa only [raised, harmonicCoefficient, zero_add, Nat.cast_one, sub_add_cancel, one_mul,
        Pi.smul_apply, smul_eq_mul] using lower_raise_of_harmonic f hf S
  | succ r ih =>
      have hlevel : IsLevel (k + (r + 1)) (raised f (r + 1)) :=
        hf.1.raised (r + 1)
      funext S
      have hcomm :=
        lower_raise_sub_raise_lower_of_level
          (raised f (r + 1)) hlevel S
      rw [ih, raise_smul] at hcomm
      have hsum := sub_eq_iff_eq_add.mp hcomm
      calc
        lower (raised f ((r + 1) + 1)) S =
            ((n : ℝ) - 2 * ((k + (r + 1) : ℕ) : ℝ)) *
                raised f (r + 1) S +
              harmonicCoefficient n k (r + 1) * raised f (r + 1) S := by
          simpa only [raised_succ, Pi.smul_apply, smul_eq_mul] using hsum
        _ = harmonicCoefficient n k ((r + 1) + 1) *
              raised f (r + 1) S := by
          rw [harmonicCoefficient_succ n k (r + 1)]
          ring
        _ = (harmonicCoefficient n k ((r + 1) + 1) •
              raised f (r + 1)) S := by
          simp only [raised_succ, Pi.smul_apply, smul_eq_mul]

/-- Toggle membership of the coordinate `a` in a finite subset. -/
def toggle (a : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  if a ∈ S then S.erase a else insert a S

@[simp] theorem toggle_toggle (a : Fin n) (S : Finset (Fin n)) :
    toggle a (toggle a S) = S := by
  classical
  by_cases ha : a ∈ S
  · simp only [toggle, ha, ↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false, and_true,
      Finset.insert_erase ha]
  · simp only [toggle, ha, ↓reduceIte, Finset.mem_insert, or_false, Finset.erase_insert ha]

private def toggleEquiv (a : Fin n) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun := toggle a
  invFun := toggle a
  left_inv := toggle_toggle a
  right_inv := toggle_toggle a

/-- The dot used in the binary-code argument. -/
def dot (f g : Function n) : ℝ :=
  ∑ S : Finset (Fin n), f S * g S

theorem dot_raiseAt_eq_lowerAt (a : Fin n) (f g : Function n) :
    dot (raiseAt a f) g = dot f (lowerAt a g) := by
  classical
  unfold dot
  calc
    (∑ S : Finset (Fin n), raiseAt a f S * g S) =
        ∑ S : Finset (Fin n),
          raiseAt a f (toggle a S) * g (toggle a S) := by
      symm
      exact (toggleEquiv a).sum_comp
        (fun S : Finset (Fin n) => raiseAt a f S * g S)
    _ = ∑ S : Finset (Fin n), f S * lowerAt a g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases ha : a ∈ S
      · simp only [raiseAt, toggle, ha, ↓reduceIte, Finset.mem_erase, ne_eq, not_true_eq_false,
          and_true, zero_mul, lowerAt, mul_zero]
      · simp only [raiseAt, toggle, ha, ↓reduceIte, Finset.mem_insert, or_false,
          Finset.erase_insert ha, lowerAt]

theorem dot_raise_eq_lower (f g : Function n) :
    dot (raise f) g = dot f (lower g) := by
  classical
  calc
    dot (raise f) g = ∑ a : Fin n, dot (raiseAt a f) g := by
      simp only [dot, raise, Finset.sum_mul]
      exact Finset.sum_comm
    _ = ∑ a : Fin n, dot f (lowerAt a g) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f g
    _ = dot f (lower g) := by
      simp only [dot, lower, Finset.mul_sum]
      exact Finset.sum_comm

theorem dot_comm (f g : Function n) : dot f g = dot g f := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  exact mul_comm _ _

theorem dot_smul_right (f g : Function n) (c : ℝ) :
    dot f (c • g) = c * dot f g := by
  classical
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem normSq_nonneg (f : Function n) : 0 ≤ (dot f f) := by
  unfold dot
  apply Finset.sum_nonneg
  intro S _
  exact mul_self_nonneg (f S)

@[simp] theorem normSq_eq_zero_iff (f : Function n) :
    (dot f f) = 0 ↔ f = 0 := by
  classical
  change (∑ S : Finset (Fin n), f S * f S) = 0 ↔ f = 0
  constructor
  · intro h
    have hz :=
      (Finset.sum_mul_self_eq_zero_iff
        (Finset.univ : Finset (Finset (Fin n))) f).mp h
    funext S
    exact hz S (Finset.mem_univ S)
  · intro h
    subst f
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end Boolean

end

section

open scoped BigOperators Matrix InnerProductSpace

/-- Data encoding the projection family construction. -/
structure ProjectionFamily (X : Type*) (D d : ℕ) where
  /-- The projection component. -/
  projection : X → Matrix (Fin D) (Fin D) ℝ
  symmetric : ∀ x, (projection x)ᵀ = projection x
  idempotent : ∀ x, projection x * projection x = projection x
  trace_eq : ∀ x, Matrix.trace (projection x) = (d : ℝ)

namespace ProjectionFamily

variable {X : Type*} {D d : ℕ}

/-- The overlap used in the metric-code argument. -/
def overlap (P : ProjectionFamily X D d) (x y : X) : ℝ :=
  Matrix.trace (P.projection x * P.projection y)

@[simp] theorem overlap_self (P : ProjectionFamily X D d) (x : X) :
    P.overlap x x = (d : ℝ) := by
  unfold overlap
  rw [P.idempotent x, P.trace_eq x]

end ProjectionFamily

section Gram

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end Gram

section Certificate

variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}

end Certificate

end

section

open scoped BigOperators Matrix

namespace Boolean

variable {n : ℕ}

/-- The sign used in the binary-code argument. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> simp [sign]

/-- The Boolean character given by the product of the signs of `x` on `S`. -/
def character (x : BinaryWord n) (S : Finset (Fin n)) : ℝ :=
  ∏ a ∈ S, sign (x a)

@[simp] theorem character_mul_self
    (x : BinaryWord n) (S : Finset (Fin n)) :
    character x S * character x S = 1 := by
  classical
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro a _
  exact sign_mul_self (x a)

/-- Multiply a function pointwise by the Boolean character of `x`. -/
def twist (x : BinaryWord n) (f : Function n) (S : Finset (Fin n)) : ℝ :=
  character x S * f S

theorem dot_twist (x : BinaryWord n) (f g : Function n) :
    dot (twist x f) (twist x g) = dot f g := by
  classical
  unfold dot
  apply Finset.sum_congr rfl
  intro S _
  unfold twist
  calc
    (character x S * f S) * (character x S * g S) =
        (character x S * character x S) * (f S * g S) := by ring
    _ = f S * g S := by rw [character_mul_self, one_mul]

theorem IsLevel.twist {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) :
    IsLevel k (twist x f) := by
  intro S hS
  change character x S * f S = 0
  rw [hf S hS, mul_zero]

/-- The coordinate function used in the binary-code argument. -/
abbrev CoordinateFunction (n : ℕ) := Fin n → Function n

/-- The coordinate dot used in the binary-code argument. -/
def coordinateDot (f g : CoordinateFunction n) : ℝ :=
  ∑ a : Fin n, dot (f a) (g a)

/-- The delete channel used in the binary-code argument. -/
def deleteChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt (i : ℝ))⁻¹ • lowerAt a f

/-- The coordinate raising channels scaled by the inverse square root of `n - i`. -/
def addChannel (i : ℕ) (f : Function n) : CoordinateFunction n :=
  fun a => (Real.sqrt ((n : ℝ) - (i : ℝ)))⁻¹ • raiseAt a f

theorem sum_not_mem_indicator (S : Finset (Fin n)) (z : ℝ) :
    (∑ a : Fin n, if a ∈ S then 0 else z) =
      ((n : ℝ) - (S.card : ℝ)) * z := by
  classical
  have hterm (a : Fin n) :
      (if a ∈ S then (0 : ℝ) else z) =
        z - (if a ∈ S then z else 0) := by
    by_cases ha : a ∈ S <;> simp [ha]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [sum_mem_indicator]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_dot_lowerAt (f g : Function n) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
        ∑ a : Fin n, dot (raiseAt a (lowerAt a f)) g := by
      apply Finset.sum_congr rfl
      intro a _
      exact (dot_raiseAt_eq_lowerAt a (lowerAt a f) g).symm
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          (if a ∈ S then f S else 0) * g S := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [raiseAt_lowerAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          (if a ∈ S then f S else 0) * g S := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_mul, sum_mem_indicator]

theorem sum_dot_raiseAt (f g : Function n) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ∑ S : Finset (Fin n),
        ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
  classical
  calc
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
        ∑ a : Fin n, dot f (lowerAt a (raiseAt a g)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact dot_raiseAt_eq_lowerAt a f (raiseAt a g)
    _ = ∑ a : Fin n, ∑ S : Finset (Fin n),
          f S * (if a ∈ S then 0 else g S) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold dot
      apply Finset.sum_congr rfl
      intro S _
      rw [lowerAt_raiseAt_self]
    _ = ∑ S : Finset (Fin n), ∑ a : Fin n,
          f S * (if a ∈ S then 0 else g S) := by
      exact Finset.sum_comm
    _ = ∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.mul_sum, sum_not_mem_indicator]
      ring

theorem sum_dot_lowerAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) =
      (i : ℝ) * dot f g := by
  classical
  rw [sum_dot_lowerAt]
  calc
    (∑ S : Finset (Fin n), (S.card : ℝ) * f S * g S) =
        ∑ S : Finset (Fin n), (i : ℝ) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp only [hS]
      · simp only [hf S hS, mul_zero, zero_mul]
    _ = (i : ℝ) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem sum_dot_raiseAt_of_level {i : ℕ} (f g : Function n)
    (hf : IsLevel i f) :
    (∑ a : Fin n, dot (raiseAt a f) (raiseAt a g)) =
      ((n : ℝ) - (i : ℝ)) * dot f g := by
  classical
  rw [sum_dot_raiseAt]
  calc
    (∑ S : Finset (Fin n),
          ((n : ℝ) - (S.card : ℝ)) * f S * g S) =
        ∑ S : Finset (Fin n),
          ((n : ℝ) - (i : ℝ)) * f S * g S := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S.card = i
      · simp only [hS]
      · simp only [hf S hS, mul_zero, zero_mul]
    _ = ((n : ℝ) - (i : ℝ)) * dot f g := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring

theorem dot_smul_left (f g : Function n) (c : ℝ) :
    dot (c • f) g = c * dot f g := by
  rw [dot_comm, dot_smul_right, dot_comm]

theorem dot_add_right (f g h : Function n) :
    dot f (g + h) = dot f g + dot f h := by
  classical
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem normSq_raise_of_level {i : ℕ}
    (f : Function n) (hf : IsLevel i f) :
    (dot (raise f) (raise f)) = (dot (lower f) (lower f)) +
      ((n : ℝ) - 2 * (i : ℝ)) * (dot f f) := by
  have hcomm :
      lower (raise f) =
        raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f := by
    funext S
    have h :=
      sub_eq_iff_eq_add.mp
        (lower_raise_sub_raise_lower_of_level f hf S)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_comm] using h
  calc
    (dot (raise f) (raise f)) = dot (raise f) (raise f) := rfl
    _ = dot f (lower (raise f)) := dot_raise_eq_lower f (raise f)
    _ = dot f
          (raise (lower f) + ((n : ℝ) - 2 * (i : ℝ)) • f) := by
      rw [hcomm]
    _ = dot f (raise (lower f)) +
          dot f (((n : ℝ) - 2 * (i : ℝ)) • f) :=
      dot_add_right f (raise (lower f))
        (((n : ℝ) - 2 * (i : ℝ)) • f)
    _ = (dot (lower f) (lower f)) +
          ((n : ℝ) - 2 * (i : ℝ)) * (dot f f) := by
      rw [dot_smul_right, dot_comm f (raise (lower f)),
        dot_raise_eq_lower]

theorem raise_eq_zero_iff_of_level {i : ℕ}
    (hi : 2 * i < n) (f : Function n) (hf : IsLevel i f) :
    raise f = 0 ↔ f = 0 := by
  constructor
  · intro hraise
    have hzero : (dot (raise f) (raise f)) = 0 := by
      rw [hraise]
      simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    have hidentity := normSq_raise_of_level f hf
    rw [hzero] at hidentity
    have hi' : (2 : ℝ) * (i : ℝ) < (n : ℝ) := by
      exact_mod_cast hi
    have hpos : 0 < (n : ℝ) - 2 * (i : ℝ) := by linarith
    have hnonneg := normSq_nonneg (lower f)
    have hfn := normSq_nonneg f
    have hnorm : (dot f f) = 0 := by nlinarith
    exact (normSq_eq_zero_iff f).mp hnorm
  · intro hfzero
    subst f
    change raiseLinear n (0 : Function n) = 0
    exact map_zero (raiseLinear n)

/-- The layer function used in the binary-code argument. -/
abbrev LayerFunction (n k : ℕ) := Level n k → ℝ

/-- The layer extend used in the binary-code argument. -/
def layerExtend {n k : ℕ} (f : LayerFunction n k) : Function n :=
  fun S => if h : S.card = k then f ⟨S, h⟩ else 0

/-- The layer restrict used in the binary-code argument. -/
def layerRestrict (k : ℕ) (f : Function n) : LayerFunction n k :=
  fun S => f S.val

theorem isLevel_layerExtend {k : ℕ} (f : LayerFunction n k) :
    IsLevel k (layerExtend f) := by
  intro S hS
  simp only [layerExtend, hS, ↓reduceDIte]

@[simp] theorem layerRestrict_layerExtend {k : ℕ}
    (f : LayerFunction n k) :
    layerRestrict k (layerExtend f) = f := by
  funext S
  simp only [layerRestrict, layerExtend, S.property, ↓reduceDIte, Subtype.coe_eta]

theorem layerExtend_layerRestrict_of_level {k : ℕ}
    (f : Function n) (hf : IsLevel k f) :
    layerExtend (layerRestrict k f) = f := by
  funext S
  by_cases hS : S.card = k
  · simp only [layerExtend, hS, ↓reduceDIte, layerRestrict]
  · simp only [layerExtend, hS, ↓reduceDIte, hf S hS]

theorem layerExtend_injective {k : ℕ} :
    Function.Injective (layerExtend (n := n) (k := k)) := by
  intro f g h
  have := congrArg (layerRestrict k) h
  simpa only [layerRestrict_layerExtend] using this

/-- Extend a function on the `k`th layer by zero, bundled as a linear map. -/
def layerExtendLinear (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] Function n where
  toFun := layerExtend
  map_add' := by
    intro f g
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.add_apply]
  map_smul' := by
    intro c f
    funext S
    by_cases hS : S.card = k <;>
      simp [layerExtend, hS, Pi.smul_apply, smul_eq_mul]

/-- Restrict a function to the `k`th layer, bundled as a linear map. -/
def layerRestrictLinear (n k : ℕ) :
    Function n →ₗ[ℝ] LayerFunction n k where
  toFun := layerRestrict k
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- The raising map from layer `k` to layer `k + 1`, obtained by extending and restricting. -/
def layerUp (n k : ℕ) :
    LayerFunction n k →ₗ[ℝ] LayerFunction n (k + 1) :=
  (layerRestrictLinear n (k + 1)).comp
    ((raiseLinear n).comp (layerExtendLinear n k))

/-- The lowering map from layer `k + 1` to layer `k`, obtained by extending and restricting. -/
def layerDown (n k : ℕ) :
    LayerFunction n (k + 1) →ₗ[ℝ] LayerFunction n k :=
  (layerRestrictLinear n k).comp
    ((lowerLinear n).comp (layerExtendLinear n (k + 1)))

@[simp] theorem layerUp_apply {k : ℕ} (f : LayerFunction n k) :
    layerUp n k f = layerRestrict (k + 1) (raise (layerExtend f)) := rfl

@[simp] theorem layerDown_apply {k : ℕ}
    (f : LayerFunction n (k + 1)) :
    layerDown n k f = layerRestrict k (lower (layerExtend f)) := rfl

theorem layerUp_injective {k : ℕ} (hk : 2 * k < n) :
    Function.Injective (layerUp n k) := by
  intro f g hfg
  have hflevel : IsLevel (k + 1) (raise (layerExtend f)) :=
    (isLevel_layerExtend f).raise
  have hglevel : IsLevel (k + 1) (raise (layerExtend g)) :=
    (isLevel_layerExtend g).raise
  have hrestrict :
      layerRestrict (k + 1) (raise (layerExtend f)) =
        layerRestrict (k + 1) (raise (layerExtend g)) := by
    simpa only [layerUp_apply] using hfg
  have hfull : raise (layerExtend f) = raise (layerExtend g) := by
    calc
      raise (layerExtend f) =
          layerExtend (layerRestrict (k + 1) (raise (layerExtend f))) :=
        (layerExtend_layerRestrict_of_level _ hflevel).symm
      _ = layerExtend
          (layerRestrict (k + 1) (raise (layerExtend g))) := by
        rw [hrestrict]
      _ = raise (layerExtend g) :=
        layerExtend_layerRestrict_of_level _ hglevel
  have hdifflevel : IsLevel k (layerExtend f - layerExtend g) := by
    intro S hS
    simp only [Pi.sub_apply, layerExtend, hS, ↓reduceDIte, sub_self]
  have hraisezero : raise (layerExtend f - layerExtend g) = 0 := by
    change raiseLinear n (layerExtend f - layerExtend g) = 0
    rw [map_sub, raiseLinear_apply, raiseLinear_apply, hfull, sub_self]
  have hdiffzero : layerExtend f - layerExtend g = 0 :=
    (raise_eq_zero_iff_of_level hk _ hdifflevel).mp hraisezero
  apply layerExtend_injective
  exact sub_eq_zero.mp hdiffzero

/-- The layer dot used in the binary-code argument. -/
def layerDot {n k : ℕ} (f g : LayerFunction n k) : ℝ :=
  ∑ S : Level n k, f S * g S

theorem dot_layerExtend {k : ℕ} (f g : LayerFunction n k) :
    dot (layerExtend f) (layerExtend g) = layerDot f g := by
  classical
  unfold dot layerDot
  refine Finset.sum_congr_set
    {S : Finset (Fin n) | S.card = k}
    (fun S => layerExtend f S * layerExtend g S)
    (fun S : Level n k => f S * g S) ?_ ?_
  · intro S hS
    change S.card = k at hS
    simp only [layerExtend, hS, ↓reduceDIte]
  · intro S hS
    change S.card ≠ k at hS
    simp only [layerExtend, hS, ↓reduceDIte, mul_zero]

theorem layerUp_layerDown_adjoint {k : ℕ}
    (f : LayerFunction n k) (g : LayerFunction n (k + 1)) :
    layerDot (layerUp n k f) g = layerDot f (layerDown n k g) := by
  rw [← dot_layerExtend, ← dot_layerExtend]
  have hup :
      layerExtend (layerUp n k f) = raise (layerExtend f) := by
    rw [layerUp_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend f).raise
  have hdown :
      layerExtend (layerDown n k g) = lower (layerExtend g) := by
    rw [layerDown_apply]
    exact layerExtend_layerRestrict_of_level _
      (isLevel_layerExtend g).lower
  rw [hup, hdown, dot_raise_eq_lower]

theorem layerUp_toMatrix_transpose (n k : ℕ) :
    LinearMap.toMatrix' (layerUp n k) =
      (LinearMap.toMatrix' (layerDown n k))ᵀ := by
  classical
  ext T S
  change
    layerUp n k (Pi.single S 1) T =
      layerDown n k (Pi.single T 1) S
  have hadjoint := layerUp_layerDown_adjoint
    (n := n) (k := k) (Pi.single S 1) (Pi.single T 1)
  simpa only [layerUp_apply, layerDown_apply, layerDot, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ite_mul, one_mul, zero_mul] using hadjoint

theorem layerUp_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerUp n k)).rank = n.choose k := by
  classical
  have hker : LinearMap.ker (layerUp n k) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (layerUp_injective hk)
  have hrange := (layerUp n k).finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, card_level] at hrange
  have hlin :
      (LinearMap.toMatrix' (layerUp n k)).mulVecLin =
        layerUp n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerUp n k)
  change
    Module.finrank ℝ
      (LinearMap.range
        (LinearMap.toMatrix' (layerUp n k)).mulVecLin) =
      n.choose k
  rw [hlin]
  exact hrange

theorem layerDown_matrix_rank {k : ℕ} (hk : 2 * k < n) :
    (LinearMap.toMatrix' (layerDown n k)).rank = n.choose k := by
  classical
  calc
    (LinearMap.toMatrix' (layerDown n k)).rank =
        ((LinearMap.toMatrix' (layerDown n k))ᵀ).rank :=
      (Matrix.rank_transpose _).symm
    _ = (LinearMap.toMatrix' (layerUp n k)).rank := by
      rw [← layerUp_toMatrix_transpose n k]
    _ = n.choose k := layerUp_matrix_rank hk

theorem layerDown_surjective {k : ℕ} (hk : 2 * k < n) :
    Function.Surjective (layerDown n k) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hlin :
      (LinearMap.toMatrix' (layerDown n k)).mulVecLin =
        layerDown n k := by
    simpa only [Matrix.toLin'_apply'] using
      Matrix.toLin'_toMatrix' (layerDown n k)
  calc
    Module.finrank ℝ (LinearMap.range (layerDown n k)) =
        (LinearMap.toMatrix' (layerDown n k)).rank := by
      change
        Module.finrank ℝ (LinearMap.range (layerDown n k)) =
          Module.finrank ℝ
            (LinearMap.range
              (LinearMap.toMatrix' (layerDown n k)).mulVecLin)
      rw [hlin]
    _ = n.choose k := layerDown_matrix_rank hk

theorem finrank_ker_layerDown {k : ℕ} (hk : 2 * k < n) :
    Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
      n.choose (k + 1) - n.choose k := by
  have hrange : LinearMap.range (layerDown n k) = ⊤ :=
    LinearMap.range_eq_top.mpr (layerDown_surjective hk)
  have hcod : Module.finrank ℝ (LayerFunction n k) = n.choose k := by
    change Module.finrank ℝ (Level n k → ℝ) = n.choose k
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hdomain :
      Module.finrank ℝ (LayerFunction n (k + 1)) =
        n.choose (k + 1) := by
    change
      Module.finrank ℝ (Level n (k + 1) → ℝ) = n.choose (k + 1)
    rw [Module.finrank_fintype_fun_eq_card, card_level]
  have hrank := (layerDown n k).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, hcod, hdomain] at hrank
  exact Nat.eq_sub_of_add_eq' hrank

/-- The harmonic layer used in the binary-code argument. -/
def harmonicLayer (n : ℕ) :
    (k : ℕ) → Submodule ℝ (LayerFunction n k)
  | 0 => ⊤
  | k + 1 => LinearMap.ker (layerDown n k)

theorem harmonicLayer_finrank (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero =>
      change Module.finrank ℝ (⊤ : Submodule ℝ (LayerFunction n 0)) =
        MetricCodes.hammingFibreDimension n 0
      rw [finrank_top,
        Module.finrank_fintype_fun_eq_card, card_level]
      simp only [Nat.choose_zero_right, hammingFibreDimension, booleanHarmonicDimension]
  | succ k =>
      have hbelow : 2 * k < n := by omega
      change
        Module.finrank ℝ (LinearMap.ker (layerDown n k)) =
          n.choose (k + 1) - n.choose k
      exact finrank_ker_layerDown (n := n) (k := k) hbelow

theorem deleteChannel_isometry {i : ℕ} (hi : 0 < i)
    (f g : Function n) (hf : IsLevel i f) :
    coordinateDot (deleteChannel i f) (deleteChannel i g) = dot f g := by
  classical
  have hi' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hs : Real.sqrt (i : ℝ) ≠ 0 := (Real.sqrt_pos.2 hi').ne'
  have hsqr : Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ) = (i : ℝ) :=
    Real.mul_self_sqrt hi'.le
  have hscalar :
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) = 1 := by
    calc
      (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ * (i : ℝ) =
          (Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
            (Real.sqrt (i : ℝ) * Real.sqrt (i : ℝ)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    coordinateDot (deleteChannel i f) (deleteChannel i g) =
        ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          (∑ a : Fin n, dot (lowerAt a f) (lowerAt a g)) := by
      simp only [coordinateDot, deleteChannel, dot_smul_left,
        dot_smul_right, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹) *
          ((i : ℝ) * dot f g) := by rw [sum_dot_lowerAt_of_level f g hf]
    _ = ((Real.sqrt (i : ℝ))⁻¹ * (Real.sqrt (i : ℝ))⁻¹ *
          (i : ℝ)) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem dot_lowerAt_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) (raiseAt a g) = 0 := by
  classical
  unfold dot
  apply Finset.sum_eq_zero
  intro S _
  by_cases ha : a ∈ S <;> simp [lowerAt, raiseAt, ha]

/-- The harmonic norm factor used in the binary-code argument. -/
def harmonicNormFactor (n k r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, harmonicCoefficient n k (j + 1)

@[simp] theorem harmonicNormFactor_zero (n k : ℕ) :
    harmonicNormFactor n k 0 = 1 := by
  simp only [harmonicNormFactor, Finset.range_zero, Finset.prod_empty]

theorem harmonicCoefficient_pos {n k r : ℕ}
    (hr : 0 < r) (hbound : 2 * k + r ≤ n) :
    0 < harmonicCoefficient n k r := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hbound' :
      (2 : ℝ) * (k : ℝ) + (r : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hbound
  unfold harmonicCoefficient
  apply mul_pos hr'
  linarith

theorem harmonicNormFactor_pos {n k r : ℕ}
    (hbound : 2 * k + r ≤ n) :
    0 < harmonicNormFactor n k r := by
  unfold harmonicNormFactor
  apply Finset.prod_pos
  intro j hj
  have hj' : j < r := Finset.mem_range.mp hj
  apply harmonicCoefficient_pos (Nat.succ_pos j)
  exact (Nat.add_le_add_left (Nat.succ_le_of_lt hj') (2 * k)).trans hbound

theorem dot_raised_succ_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f (r + 1)) (raised g (r + 1)) =
      harmonicCoefficient n k (r + 1) *
        dot (raised f r) (raised g r) := by
  calc
    dot (raised f (r + 1)) (raised g (r + 1)) =
        dot (raise (raised f r)) (raise (raised g r)) := rfl
    _ = dot (raised f r) (lower (raise (raised g r))) :=
      dot_raise_eq_lower (raised f r) (raise (raised g r))
    _ = dot (raised f r) (lower (raised g (r + 1))) := rfl
    _ = dot (raised f r)
          (harmonicCoefficient n k (r + 1) • raised g r) := by
      rw [lower_raised_succ_of_harmonic g hg r]
    _ = harmonicCoefficient n k (r + 1) *
          dot (raised f r) (raised g r) := by
      rw [dot_smul_right]

theorem dot_raised_of_harmonic {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ) :
    dot (raised f r) (raised g r) =
      harmonicNormFactor n k r * dot f g := by
  induction r with
  | zero => simp only [raised, harmonicNormFactor, Finset.range_zero, Finset.prod_empty, one_mul]
  | succ r ih =>
      rw [dot_raised_succ_of_harmonic f g hg r, ih]
      simp only [harmonicNormFactor, Finset.prod_range_succ]
      ring

/-- The harmonic embedding used in the binary-code argument. -/
def harmonicEmbedding (k r : ℕ) (f : Function n) : Function n :=
  (Real.sqrt (harmonicNormFactor n k r))⁻¹ • raised f r

/-- The normalized harmonic embedding twisted by the Boolean character of `x`. -/
def wordHarmonicEmbedding (x : BinaryWord n) (k r : ℕ)
    (f : Function n) : Function n :=
  twist x (harmonicEmbedding k r f)

theorem harmonicEmbedding_isometry {k : ℕ}
    (f g : Function n) (hg : IsHarmonic k g) (r : ℕ)
    (hbound : 2 * k + r ≤ n) :
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
      dot f g := by
  have hpos : 0 < harmonicNormFactor n k r :=
    harmonicNormFactor_pos hbound
  have hs : Real.sqrt (harmonicNormFactor n k r) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsqr :
      Real.sqrt (harmonicNormFactor n k r) *
          Real.sqrt (harmonicNormFactor n k r) =
        harmonicNormFactor n k r :=
    Real.mul_self_sqrt hpos.le
  have hscalar :
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r = 1 := by
    calc
      (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r =
        (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            (Real.sqrt (harmonicNormFactor n k r) *
              Real.sqrt (harmonicNormFactor n k r)) := by rw [hsqr]
      _ = 1 := by field_simp [hs]
  calc
    dot (harmonicEmbedding k r f) (harmonicEmbedding k r g) =
        ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            dot (raised f r) (raised g r) := by
      simp only [harmonicEmbedding, dot_smul_left, dot_smul_right]
      ring
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹) *
            (harmonicNormFactor n k r * dot f g) := by
      rw [dot_raised_of_harmonic f g hg r]
    _ = ((Real.sqrt (harmonicNormFactor n k r))⁻¹ *
          (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
            harmonicNormFactor n k r) * dot f g := by ring
    _ = dot f g := by rw [hscalar, one_mul]

theorem wordHarmonicEmbedding_isometry {k : ℕ}
    (x : BinaryWord n) (f g : Function n)
    (hg : IsHarmonic k g) (r : ℕ) (hbound : 2 * k + r ≤ n) :
    dot (wordHarmonicEmbedding x k r f)
        (wordHarmonicEmbedding x k r g) = dot f g := by
  unfold wordHarmonicEmbedding
  rw [dot_twist]
  exact harmonicEmbedding_isometry f g hg r hbound

theorem IsLevel.harmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (r : ℕ) :
    IsLevel (k + r) (harmonicEmbedding k r f) := by
  intro S hS
  change
    (Real.sqrt (harmonicNormFactor n k r))⁻¹ *
      MetricCodes.Boolean.raised f r S = 0
  rw [(MetricCodes.Boolean.IsLevel.raised hf r) S hS, mul_zero]

theorem IsLevel.wordHarmonicEmbedding {k : ℕ} {f : Function n}
    (hf : IsLevel k f) (x : BinaryWord n) (r : ℕ) :
    IsLevel (k + r) (wordHarmonicEmbedding x k r f) := by
  exact (hf.harmonicEmbedding r).twist x

theorem mem_harmonicLayer_iff {k : ℕ} (f : LayerFunction n k) :
    f ∈ harmonicLayer n k ↔ IsHarmonic k (layerExtend f) := by
  classical
  cases k with
  | zero =>
      constructor
      · intro _
        refine ⟨isLevel_layerExtend f, ?_⟩
        intro S
        unfold lower
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : a ∈ S
        · simp only [lowerAt, ha, ↓reduceIte]
        · have hcard : (insert a S).card ≠ 0 :=
            Finset.card_ne_zero_of_mem (Finset.mem_insert_self a S)
          simp only [lowerAt, ha, ↓reduceIte, layerExtend, not_false_eq_true,
            Finset.card_insert_of_notMem, Nat.add_eq_zero_iff, Finset.card_eq_zero, one_ne_zero,
            and_false, ↓reduceDIte]
      · intro _
        exact Submodule.mem_top
  | succ k =>
      constructor
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k) at hf
        have hdown : layerDown n k f = 0 := LinearMap.mem_ker.mp hf
        refine ⟨isLevel_layerExtend f, ?_⟩
        have hrestrict :
            layerRestrict k (lower (layerExtend f)) = 0 := by
          simpa only [layerDown_apply] using hdown
        have hlower : lower (layerExtend f) = 0 := by
          calc
            lower (layerExtend f) =
                layerExtend (layerRestrict k (lower (layerExtend f))) :=
              (layerExtend_layerRestrict_of_level _
                (isLevel_layerExtend f).lower).symm
            _ = layerExtend (0 : LayerFunction n k) := by rw [hrestrict]
            _ = 0 := by
              change layerExtendLinear n k (0 : LayerFunction n k) = 0
              exact map_zero (layerExtendLinear n k)
        exact fun S => congrFun hlower S
      · intro hf
        change f ∈ LinearMap.ker (layerDown n k)
        apply LinearMap.mem_ker.mpr
        rw [layerDown_apply]
        have hlower : lower (layerExtend f) = 0 := funext hf.2
        rw [hlower]
        change layerRestrictLinear n k (0 : Function n) = 0
        exact map_zero (layerRestrictLinear n k)

/-- The euclidean layer used in the binary-code argument. -/
abbrev EuclideanLayer (n k : ℕ) := EuclideanSpace ℝ (Level n k)

/-- The harmonic euclidean layer used in the binary-code argument. -/
def harmonicEuclideanLayer (n k : ℕ) :
    Submodule ℝ (EuclideanLayer n k) :=
  (harmonicLayer n k).map
    (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap

theorem harmonicEuclideanLayer_finrank
    (n k : ℕ) (hk : 2 * k ≤ n) :
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
      MetricCodes.hammingFibreDimension n k := by
  calc
    Module.finrank ℝ (harmonicEuclideanLayer n k) =
        Module.finrank ℝ (harmonicLayer n k) := by
      change
        Module.finrank ℝ
            ((harmonicLayer n k).map
              (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap) =
          Module.finrank ℝ (harmonicLayer n k)
      exact
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.finrank_map_eq
          (harmonicLayer n k)
    _ = MetricCodes.hammingFibreDimension n k := harmonicLayer_finrank n k hk

/-- The harmonic orthonormal basis used in the binary-code argument. -/
def harmonicOrthonormalBasis
    (n k : ℕ) (hk : 2 * k ≤ n) :
    OrthonormalBasis (Fin (MetricCodes.hammingFibreDimension n k)) ℝ
      (harmonicEuclideanLayer n k) :=
  (stdOrthonormalBasis ℝ (harmonicEuclideanLayer n k)).reindex
    (finCongr (harmonicEuclideanLayer_finrank n k hk))

/-- The harmonic basis function used in the binary-code argument. -/
def harmonicBasisFunction
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) : Function n :=
  layerExtend
    (WithLp.ofLp ((harmonicOrthonormalBasis n k hk p).val))

theorem harmonicBasisFunction_isHarmonic
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p : Fin (MetricCodes.hammingFibreDimension n k)) :
    IsHarmonic k (harmonicBasisFunction n k hk p) := by
  let b := harmonicOrthonormalBasis n k hk p
  have hmem : b.val ∈ harmonicEuclideanLayer n k := b.property
  change
    b.val ∈
      (harmonicLayer n k).map
        (WithLp.linearEquiv 2 ℝ (LayerFunction n k)).symm.toLinearMap
    at hmem
  obtain ⟨g, hg, heq⟩ := (Submodule.mem_map).mp hmem
  have hcoef : WithLp.ofLp b.val = g := by
    have h := congrArg
      (fun z : EuclideanLayer n k => WithLp.ofLp z) heq.symm
    simpa only [LinearEquiv.coe_coe, WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe,
      Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply] using h
  change IsHarmonic k (layerExtend (WithLp.ofLp b.val))
  apply (mem_harmonicLayer_iff (WithLp.ofLp b.val)).mp
  rw [hcoef]
  exact hg

/-- The sum of the layer dimensions over the offsets in `Fin (L - k + 1)`. -/
def hammingWindowDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

/-- Indices consisting of a window offset and a subset in its corresponding Hamming layer. -/
abbrev HammingWindowIndex (n k L : ℕ) :=
  Σ j : Fin (L - k + 1), Level n (k + j.val)

theorem hammingWindowIndex_card (n k L : ℕ) :
    Fintype.card (HammingWindowIndex n k L) =
      hammingWindowDimension n k L := by
  classical
  rw [Fintype.card_sigma]
  simp only [card_level]
  unfold hammingWindowDimension
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr j.isLt
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    refine ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro j _
    rfl

/-- Enumerate the Hamming window indices by their total dimension. -/
def hammingWindowIndexEquiv (n k L : ℕ) :
    HammingWindowIndex n k L ≃ Fin (hammingWindowDimension n k L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_finset_len,
      Fintype.card_fin] using hammingWindowIndex_card n k L)

/-- A recurrence coordinate weighted by the square root of its Hamming layer dimension. -/
def hammingRecurrenceWeight
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt (n.choose (k + j.val) : ℝ) * v j

/-- The sum of the dimension-weighted Hamming recurrence coordinates. -/
def hammingRecurrenceNormalization
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1))) : ℝ :=
  ∑ j : Fin (L - k + 1), hammingRecurrenceWeight n k L v j

/-- The square root of a normalized Hamming recurrence weight, used as a fibre amplitude. -/
def hammingFibreAmplitude
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (j : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingRecurrenceWeight n k L v j /
      hammingRecurrenceNormalization n k L v)

theorem hammingRecurrenceWeight_nonneg
    (n k L : ℕ) (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    0 ≤ hammingRecurrenceWeight n k L v j := by
  exact mul_nonneg (Real.sqrt_nonneg _) (hv j)

theorem hammingRecurrenceNormalization_pos
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    0 < hammingRecurrenceNormalization n k L v := by
  classical
  have hvzero : v ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hunit
  obtain ⟨j, hj⟩ : ∃ j : Fin (L - k + 1), 0 < v j := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    apply hvzero
    apply PiLp.ext
    intro i
    change v i = 0
    exact le_antisymm (hnone i) (hv i)
  have hlevel : k + j.val ≤ n := by
    have hjbound := j.isLt
    omega
  have hdimension : 0 < (n.choose (k + j.val) : ℝ) := by
    exact_mod_cast Nat.choose_pos hlevel
  unfold hammingRecurrenceNormalization
  apply Finset.sum_pos'
  · intro i _
    exact hammingRecurrenceWeight_nonneg n k L v hv i
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    exact mul_pos (Real.sqrt_pos.2 hdimension) hj

theorem hammingFibreAmplitude_sq
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (j : Fin (L - k + 1)) :
    hammingFibreAmplitude n k L v j ^ 2 =
      hammingRecurrenceWeight n k L v j /
        hammingRecurrenceNormalization n k L v := by
  unfold hammingFibreAmplitude
  apply Real.sq_sqrt
  exact div_nonneg
    (hammingRecurrenceWeight_nonneg n k L v hv j)
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).le

theorem hammingFibreAmplitude_sq_sum
    {n k L : ℕ} (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    (∑ j : Fin (L - k + 1), hammingFibreAmplitude n k L v j ^ 2) =
      1 := by
  simp_rw [hammingFibreAmplitude_sq hkL hLn v hunit hv]
  rw [← Finset.sum_div]
  change
    hammingRecurrenceNormalization n k L v /
      hammingRecurrenceNormalization n k L v = 1
  exact div_self
    (hammingRecurrenceNormalization_pos hkL hLn v hunit hv).ne'

theorem harmonicBasisFunction_dot
    (n k : ℕ) (hk : 2 * k ≤ n)
    (p q : Fin (MetricCodes.hammingFibreDimension n k)) :
    dot (harmonicBasisFunction n k hk p)
        (harmonicBasisFunction n k hk q) =
      if p = q then 1 else 0 := by
  classical
  unfold harmonicBasisFunction
  rw [dot_layerExtend]
  have h := (harmonicOrthonormalBasis n k hk).inner_eq_ite p q
  simpa only [layerDot, Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply,
    Real.ringHom_apply, mul_comm] using h

theorem dot_eq_layerDot_of_level {i : ℕ}
    (f g : Function n) (hf : IsLevel i f) (hg : IsLevel i g) :
    dot f g = layerDot (layerRestrict i f) (layerRestrict i g) := by
  rw [← dot_layerExtend,
    layerExtend_layerRestrict_of_level f hf,
    layerExtend_layerRestrict_of_level g hg]

/-- The matrix of twisted harmonic basis embeddings weighted by their window fibre amplitudes. -/
def hammingWindowFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (HammingWindowIndex n k L)
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun T p =>
    hammingFibreAmplitude n k L v T.1 *
      wordHarmonicEmbedding x k T.1.val
        (harmonicBasisFunction n k hk p) T.2.val

theorem hammingWindowFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingWindowFibreMatrix n k L hk v x)ᵀ *
        hammingWindowFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      if p = q then 1 else 0
  calc
    (∑ T : HammingWindowIndex n k L,
      hammingWindowFibreMatrix n k L hk v x T p *
        hammingWindowFibreMatrix n k L hk v x T q) =
      ∑ j : Fin (L - k + 1),
        hammingFibreAmplitude n k L v j ^ 2 *
          dot
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk p))
            (wordHarmonicEmbedding x k j.val
              (harmonicBasisFunction n k hk q)) := by
        simp only [hammingWindowFibreMatrix]
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        change
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
            hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q))
        calc
          (∑ S : Level n (k + j.val),
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk p) S.val) *
            (hammingFibreAmplitude n k L v j *
              wordHarmonicEmbedding x k j.val
                (harmonicBasisFunction n k hk q) S.val)) =
              hammingFibreAmplitude n k L v j ^ 2 *
                (∑ S : Level n (k + j.val),
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk p) S.val *
                  wordHarmonicEmbedding x k j.val
                    (harmonicBasisFunction n k hk q) S.val) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                ring
          _ = hammingFibreAmplitude n k L v j ^ 2 *
              dot
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk p))
                (wordHarmonicEmbedding x k j.val
                  (harmonicBasisFunction n k hk q)) := by
                congr 1
                exact
                  (dot_eq_layerDot_of_level
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk p))
                    (wordHarmonicEmbedding x k j.val
                      (harmonicBasisFunction n k hk q))
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk p).1
                      x j.val)
                    (MetricCodes.Boolean.IsLevel.wordHarmonicEmbedding
                      (harmonicBasisFunction_isHarmonic n k hk q).1
                      x j.val)).symm
    _ = ∑ j : Fin (L - k + 1),
          hammingFibreAmplitude n k L v j ^ 2 *
            (if p = q then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        have hjbound : 2 * k + j.val ≤ n := by
          have hj := j.isLt
          omega
        rw [wordHarmonicEmbedding_isometry x
          (harmonicBasisFunction n k hk p)
          (harmonicBasisFunction n k hk q)
          (harmonicBasisFunction_isHarmonic n k hk q)
          j.val hjbound, harmonicBasisFunction_dot]
    _ = (if p = q then 1 else 0) := by
        by_cases hpq : p = q
        · simp only [hpq, ↓reduceIte, mul_one, hammingFibreAmplitude_sq_sum hkL hLn v hunit hv]
        · simp only [hpq, ↓reduceIte, mul_zero, Finset.sum_const_zero]

/-- The Hamming window fibre matrix with its rows enumerated by the window dimension. -/
def hammingFibreMatrix
    (n k L : ℕ) (hk : 2 * k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (x : BinaryWord n) :
    Matrix (Fin (hammingWindowDimension n k L))
      (Fin (MetricCodes.hammingFibreDimension n k)) ℝ :=
  fun i p =>
    hammingWindowFibreMatrix n k L hk v x
      ((hammingWindowIndexEquiv n k L).symm i) p

theorem hammingFibreMatrix_transpose_mul
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j)
    (x : BinaryWord n) :
    (hammingFibreMatrix n k L hk v x)ᵀ *
        hammingFibreMatrix n k L hk v x = 1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      if p = q then 1 else 0
  calc
    (∑ i : Fin (hammingWindowDimension n k L),
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) p *
      hammingWindowFibreMatrix n k L hk v x
        ((hammingWindowIndexEquiv n k L).symm i) q) =
      ∑ T : HammingWindowIndex n k L,
        hammingWindowFibreMatrix n k L hk v x T p *
          hammingWindowFibreMatrix n k L hk v x T q :=
        (hammingWindowIndexEquiv n k L).symm.sum_comp
          (fun T =>
            hammingWindowFibreMatrix n k L hk v x T p *
              hammingWindowFibreMatrix n k L hk v x T q)
    _ = (if p = q then 1 else 0) := by
        have h := congrArg
          (fun M : Matrix
              (Fin (MetricCodes.hammingFibreDimension n k))
              (Fin (MetricCodes.hammingFibreDimension n k)) ℝ => M p q)
          (hammingWindowFibreMatrix_transpose_mul
            hk hkL hLn v hunit hv x)
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

/-- The hamming projection family used in the binary-code argument. -/
def hammingProjectionFamily
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ j : Fin (L - k + 1), 0 ≤ v j) :
    MetricCodes.ProjectionFamily (BinaryWord n)
      (hammingWindowDimension n k L)
      (MetricCodes.hammingFibreDimension n k) where
  projection x :=
    hammingFibreMatrix n k L hk v x *
      (hammingFibreMatrix n k L hk v x)ᵀ
  symmetric x := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  idempotent x := by
    let A := hammingFibreMatrix n k L hk v x
    change (A * Aᵀ) * (A * Aᵀ) = A * Aᵀ
    calc
      (A * Aᵀ) * (A * Aᵀ) = A * ((Aᵀ * A) * Aᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = A * Aᵀ := by
        rw [hammingFibreMatrix_transpose_mul hk hkL hLn
          v hunit hv x, Matrix.one_mul]
  trace_eq x := by
    rw [Matrix.trace_mul_comm,
      hammingFibreMatrix_transpose_mul hk hkL hLn v hunit hv x]
    simp only [Matrix.trace_one, Fintype.card_fin]

/-- The Euclidean sign vector of a binary word, scaled by the inverse square root of `n`. -/
def hammingAxis (x : BinaryWord n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2
    (fun a : Fin n => (Real.sqrt (n : ℝ))⁻¹ * sign (x a))

/-- The Euclidean vector of matrix entries used to express the Hilbert–Schmidt inner product. -/
def matrixHilbertSchmidtFeature
    {ι ρ : Type*}
    (A : Matrix ι ρ ℝ) : EuclideanSpace ℝ (ι × ρ) :=
  WithLp.toLp 2 (fun p : ι × ρ => A p.1 p.2)

@[simp] theorem matrixHilbertSchmidtFeature_sub
    {ι ρ : Type*}
    (A B : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (A - B) =
      matrixHilbertSchmidtFeature A -
        matrixHilbertSchmidtFeature B := by
  apply PiLp.ext
  intro p
  rfl

@[simp] theorem matrixHilbertSchmidtFeature_smul
    {ι ρ : Type*}
    (c : ℝ) (A : Matrix ι ρ ℝ) :
    matrixHilbertSchmidtFeature (c • A) =
      c • matrixHilbertSchmidtFeature A := by
  apply PiLp.ext
  intro p
  rfl

/-- The matrix axis lift used in the binary-code argument. -/
def matrixAxisLift {κ ι ρ : Type*}
    (z : κ → ℝ) (A : Matrix ι ρ ℝ) :
    Matrix (κ × ι) ρ ℝ :=
  fun p j => z p.1 * A p.2 j

/-- The axis-lifted projection minus the scaled channel image of that projection. -/
def matrixAxisResidual
    {X κ : Type*} {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    Matrix (κ × Fin D) (Fin D) ℝ :=
  matrixAxisLift (axis x) (P.projection x) -
    c • (B * P.projection x)

/-- The matrix axis gram feature used in the binary-code argument. -/
def matrixAxisGramFeature
    {X κ : Type*} {D d : ℕ}
    (P : MetricCodes.ProjectionFamily X D d)
    (axis : X → κ → ℝ)
    (B : Matrix (κ × Fin D) (Fin D) ℝ)
    (c : ℝ) (x : X) :
    EuclideanSpace ℝ ((κ × Fin D) × Fin D) :=
  matrixHilbertSchmidtFeature (matrixAxisResidual P axis B c x)

@[simp] theorem harmonicNormFactor_succ (n k r : ℕ) :
    harmonicNormFactor n k (r + 1) =
      harmonicNormFactor n k r * harmonicCoefficient n k (r + 1) := by
  simp only [harmonicNormFactor, Finset.prod_range_succ]

/-- The Hamming Jacobi entry rescaled by the square roots of the source and target layer
dimensions. -/
def hammingSourceChannelCoefficient
    (n k L : ℕ)
    (m i : Fin (L - k + 1)) : ℝ :=
  MetricCodes.hammingJacobiMatrix n k L m i *
    Real.sqrt (n.choose (k + m.val) : ℝ) /
      Real.sqrt (n.choose (k + i.val) : ℝ)

/-- The square-root weight for an adjacent channel block, normalized by the eigenvalue and
source recurrence weight. -/
def hammingAdjacentBlockCoefficient
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ)
    (target source : Fin (L - k + 1)) : ℝ :=
  Real.sqrt
    (hammingSourceChannelCoefficient n k L source target *
      hammingRecurrenceWeight n k L v target /
        (lam * hammingRecurrenceWeight n k L v source))

theorem IsLevel.smul {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (c : ℝ) : IsLevel i (c • f) := by
  intro S hS
  change c * f S = 0
  rw [hf S hS, mul_zero]

theorem IsLevel.lowerAt {i : ℕ} {f : Function n}
    (hf : IsLevel (i + 1) f) (a : Fin n) :
    IsLevel i (MetricCodes.Boolean.lowerAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [ite_eq_left ha]
  · have hinsert : (insert a S).card ≠ i + 1 := by
      intro hcard
      apply hS
      have hinsertcard := Finset.card_insert_of_notMem ha
      omega
    change (if a ∈ S then 0 else f (insert a S)) = 0
    rw [ite_eq_right ha, hf (insert a S) hinsert]

theorem IsLevel.raiseAt {i : ℕ} {f : Function n}
    (hf : IsLevel i f) (a : Fin n) :
    IsLevel (i + 1) (MetricCodes.Boolean.raiseAt a f) := by
  classical
  intro S hS
  by_cases ha : a ∈ S
  · have herase : (S.erase a).card ≠ i := by
      intro hcard
      apply hS
      have herasecard := Finset.card_erase_add_one ha
      omega
    change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [ite_eq_left ha, hf (S.erase a) herase]
  · change (if a ∈ S then f (S.erase a) else 0) = 0
    rw [ite_eq_right ha]

/-- The indicator function of the subset specified by a Hamming window index. -/
def hammingWindowBasis (n k L : ℕ)
    (T : HammingWindowIndex n k L) : Function n :=
  fun S => if S = T.2.val then 1 else 0

/-- The deletion or insertion channel between adjacent window levels, and zero otherwise. -/
def hammingAdjacentChannel (n k L : ℕ)
    (target source : Fin (L - k + 1))
    (f : Function n) : CoordinateFunction n :=
  if target.val + 1 = source.val then
    deleteChannel (k + source.val) f
  else if source.val + 1 = target.val then
    addChannel (k + source.val) f
  else
    0

theorem coordinateDot_comm (f g : CoordinateFunction n) :
    coordinateDot f g = coordinateDot g f := by
  classical
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro a _
  exact dot_comm (f a) (g a)

/-- The weighted adjacent-channel matrix in the Hamming window basis. -/
def hammingWindowChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × HammingWindowIndex n k L)
      (HammingWindowIndex n k L) ℝ :=
  fun p Q =>
    hammingAdjacentBlockCoefficient n k L v lam p.2.1 Q.1 *
      hammingAdjacentChannel n k L p.2.1 Q.1
        (hammingWindowBasis n k L Q) p.1 p.2.2.val

/-- The Hamming window channel matrix with both window indices enumerated by their total
dimension. -/
def hammingChannelMatrix
    (n k L : ℕ)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (lam : ℝ) :
    Matrix (Fin n × Fin (hammingWindowDimension n k L))
      (Fin (hammingWindowDimension n k L)) ℝ :=
  fun p q =>
    hammingWindowChannelMatrix n k L v lam
      (p.1, (hammingWindowIndexEquiv n k L).symm p.2)
      ((hammingWindowIndexEquiv n k L).symm q)

/-- The squared deletion-channel coefficient relating levels `i` and `i + 1` in harmonic degree
`k`. -/
def hammingDeletionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((i : ℝ) + 1))

/-- The squared insertion-channel coefficient relating levels `i` and `i + 1` in harmonic degree
`k`. -/
def hammingInsertionChannelSquare (n k i : ℕ) : ℝ :=
  (((i : ℝ) - (k : ℝ) + 1) *
    ((n : ℝ) - (i : ℝ) - (k : ℝ))) /
      ((n : ℝ) * ((n : ℝ) - (i : ℝ)))

theorem dot_lowerAt_eq_raiseAt (a : Fin n) (f g : Function n) :
    dot (lowerAt a f) g = dot f (raiseAt a g) := by
  calc
    dot (lowerAt a f) g = dot g (lowerAt a f) :=
      dot_comm _ _
    _ = dot (raiseAt a g) f :=
      (dot_raiseAt_eq_lowerAt a g f).symm
    _ = dot f (raiseAt a g) := dot_comm _ _

/-- The coordinate-valued function obtained by tensoring `f` with the Hamming axis of `x`. -/
def hammingAxisTensor (x : BinaryWord n) (f : Function n) :
    CoordinateFunction n :=
  fun a => hammingAxis x a • f

/-- The hamming projection gram feature used in the binary-code argument. -/
def hammingProjectionGramFeature
    {n k L : ℕ} (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (x : BinaryWord n) :
    EuclideanSpace ℝ
      ((Fin n × Fin (hammingWindowDimension n k L)) ×
        Fin (hammingWindowDimension n k L)) :=
  matrixAxisGramFeature
    (hammingProjectionFamily hk hkL hLn
      v hunit (fun i => (hv i).le))
    (fun (y : BinaryWord n) (a : Fin n) => hammingAxis y a)
    (hammingChannelMatrix n k L v lam)
    (Real.sqrt lam) x

end Boolean

end

section

open scoped BigOperators
open Finset

/-- The word support used in the metric-code argument. -/
def wordSupport {n : ℕ} (x : BinaryWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

@[simp] theorem mem_wordSupport {n : ℕ} (x : BinaryWord n) (i : Fin n) :
    i ∈ wordSupport x ↔ x i = true := by
  simp only [wordSupport, mem_filter, mem_univ, true_and]

/-- The binary word whose true coordinates are exactly the elements of `s`. -/
def wordOfSupport {n : ℕ} (s : Finset (Fin n)) : BinaryWord n :=
  fun i => decide (i ∈ s)

@[simp] theorem wordOfSupport_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    wordOfSupport s i = true ↔ i ∈ s := by
  simp only [wordOfSupport, decide_eq_true_eq]

@[simp] theorem wordSupport_wordOfSupport {n : ℕ} (s : Finset (Fin n)) :
    wordSupport (wordOfSupport s) = s := by
  ext i
  simp only [mem_wordSupport, wordOfSupport_apply]

@[simp] theorem wordOfSupport_wordSupport {n : ℕ} (x : BinaryWord n) :
    wordOfSupport (wordSupport x) = x := by
  funext i
  cases h : x i <;> simp [wordOfSupport, wordSupport, h]

private def binaryWordEquivFinset (n : ℕ) : BinaryWord n ≃ Finset (Fin n) where
  toFun := wordSupport
  invFun := wordOfSupport
  left_inv := wordOfSupport_wordSupport
  right_inv := wordSupport_wordOfSupport

theorem binaryWeight_eq_card_wordSupport {n : ℕ} (x : BinaryWord n) :
    binaryWeight x = (wordSupport x).card := by
  rfl

theorem hammingDist_comm {n : ℕ} (x y : BinaryWord n) :
    hammingDist x y = hammingDist y x := by
  exact _root_.hammingDist_comm x y

/-- The johnson dist used in the metric-code argument. -/
def johnsonDist {n w : ℕ} (x y : JohnsonSphere n w) : ℕ :=
  (wordSupport (x : BinaryWord n) \ wordSupport (y : BinaryWord n)).card

/-- Translate a binary word by coordinatewise exclusive-or with `x`. -/
def binaryTranslate {n : ℕ} (x y : BinaryWord n) : BinaryWord n :=
  fun i => Bool.xor (x i) (y i)

@[simp] theorem binaryTranslate_involutive {n : ℕ} (x y : BinaryWord n) :
    binaryTranslate x (binaryTranslate x y) = y := by
  funext i
  change Bool.xor (x i) (Bool.xor (x i) (y i)) = y i
  rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

/-- The finite set of length-`n` binary words of weight `w`. -/
def weightShell (n w : ℕ) : Finset (BinaryWord n) :=
  Finset.univ.filter fun x => binaryWeight x = w

@[simp] theorem mem_weightShell {n w : ℕ} (x : BinaryWord n) :
    x ∈ weightShell n w ↔ binaryWeight x = w := by
  simp only [weightShell, mem_filter, mem_univ, true_and]

/-- The finite set of binary words at Hamming distance exactly `r` from `x`. -/
def hammingSphere {n : ℕ} (x : BinaryWord n) (r : ℕ) :
    Finset (BinaryWord n) :=
  Finset.univ.filter fun y => hammingDist x y = r

@[simp] theorem mem_hammingSphere {n r : ℕ} (x y : BinaryWord n) :
    y ∈ hammingSphere x r ↔ hammingDist x y = r := by
  simp only [hammingSphere, mem_filter, mem_univ, true_and]

/-- The words of `C` whose translate by `z` has weight `w`. -/
def localizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  C.filter fun x => binaryWeight (binaryTranslate z x) = w

@[simp] theorem mem_localizedCode {n w : ℕ} (C : Finset (BinaryWord n))
    (z x : BinaryWord n) :
    x ∈ localizedCode C z w ↔
      x ∈ C ∧ binaryWeight (binaryTranslate z x) = w := by
  simp only [localizedCode, mem_filter]

/-- Translate the localized code by `z` into the weight-`w` shell. -/
def translateLocalizedCode {n : ℕ} (C : Finset (BinaryWord n))
    (z : BinaryWord n) (w : ℕ) : Finset (BinaryWord n) :=
  (localizedCode C z w).image (binaryTranslate z)

/-- The preceding binomial used in the metric-code argument. -/
def precedingBinomial (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => n.choose k

theorem choose_monotone_to_half (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) :
    n.choose i ≤ n.choose j := by
  have hi : 2 * i ≤ n := by omega
  have hj' : 2 * j ≤ n := by omega
  rw [← sum_booleanHarmonicDimension n i hi,
    ← sum_booleanHarmonicDimension n j hj']
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- The johnson ambient dimension used in the metric-code argument. -/
def johnsonAmbientDimension (n a L : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc a L, booleanHarmonicDimension n j

theorem johnsonAmbientDimension_eq (n a L : ℕ)
    (haL : a ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n a L =
      n.choose L - precedingBinomial n a := by
  unfold johnsonAmbientDimension
  induction L generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp only [Icc_self, booleanHarmonicDimension, sum_singleton, Nat.choose_zero_right,
        precedingBinomial, tsub_zero]
  | succ L ih =>
      by_cases htop : a = L + 1
      · subst a
        simp only [Icc_self, booleanHarmonicDimension, sum_singleton, precedingBinomial]
      · have ha' : a ≤ L := by omega
        have hhalf : L < n / 2 := by omega
        have hchoose : n.choose L ≤ n.choose (L + 1) :=
          Nat.choose_le_succ_of_lt_half_left hhalf
        have hbase : precedingBinomial n a ≤ n.choose L := by
          cases a with
          | zero => simp only [precedingBinomial, zero_le]
          | succ a =>
              apply choose_monotone_to_half n
              · omega
              · exact hhalf.le
        have hinter :
            Finset.Icc a (L + 1) =
              insert (L + 1) (Finset.Icc a L) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hinter, Finset.sum_insert (by simp only [mem_Icc, add_le_iff_nonpos_right,
                                            nonpos_iff_eq_zero, one_ne_zero, and_false,
                                            not_false_eq_true]),
          ih a ha' hhalf.le, booleanHarmonicDimension_succ]
        exact Nat.sub_add_sub_cancel hchoose hbase

theorem johnsonAmbientDimension_eq_of_fibre (n p q L : ℕ)
    (hpq : p + q ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n (p + q) L =
      n.choose L - precedingBinomial n (p + q) :=
  johnsonAmbientDimension_eq n (p + q) L hpq hL

end

end MetricCodes

namespace SpherePacking

section

open Filter MeasureTheory Metric
open scoped ENNReal InnerProductSpace Topology

/-- The euclidean used in the spherical-code argument. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

end

section

open Filter Real
open scoped Nat Topology

/-- The error in the normalized factorial-log approximation `log (n!) / n = log n - 1`. -/
def factorialLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) / (n : ℝ) - Real.log (n : ℝ) + 1

theorem tendsto_log_natCast_div_natCast :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have h :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      (1 : ℝ) 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr ?_
  intro n
  simp only [pow_one, one_mul, add_zero, Function.comp_apply]

theorem tendsto_log_two_mul_natCast_div_natCast :
    Tendsto (fun n : ℕ =>
      Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hs := hc.add tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    rw [Real.log_mul (by norm_num) hn', add_div]
  simpa only [add_zero] using hs.congr' heq

theorem tendsto_log_stirlingSeq_div_natCast :
    Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
        atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [div_eq_mul_inv, mul_zero] using hlog.mul hinv

theorem factorialLogError_eq (n : ℕ) (hn : n ≠ 0) :
    factorialLogError n =
      Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn' he, Real.log_exp] at hst
  have hlog : Real.log ((n : ℝ) * 2) = Real.log (2 * (n : ℝ)) := by
    rw [mul_comm]
  unfold factorialLogError
  field_simp [hn']
  nlinarith [hst, hlog]

theorem tendsto_factorialLogError :
    Tendsto factorialLogError atTop (nhds 0) := by
  have hhalf :=
    tendsto_log_two_mul_natCast_div_natCast.const_mul (1 / 2 : ℝ)
  have hsum := tendsto_log_stirlingSeq_div_natCast.add hhalf
  have heq :
      (fun n : ℕ =>
        Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ))) =ᶠ[atTop]
        factorialLogError := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [factorialLogError_eq n hn]
    ring
  simpa only [one_div, mul_zero, add_zero] using hsum.congr' heq

theorem scaled_log_factorial_identity (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Real.log (m.factorial : ℝ) / (n : ℝ) -
        ((m : ℝ) / (n : ℝ)) * Real.log (n : ℝ) =
      ((m : ℝ) / (n : ℝ)) *
        (factorialLogError m + Real.log ((m : ℝ) / (n : ℝ)) - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.log_div hm' hn']
  unfold factorialLogError
  field_simp [hm', hn']
  ring_nf

theorem tendsto_scaled_log_factorial_sub
    (k : ℕ → ℕ) (u : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hu : u ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))
      atTop (nhds (u * Real.log u - u)) := by
  have herror :
      Tendsto (fun n : ℕ => factorialLogError (k n))
        atTop (nhds 0) :=
    tendsto_factorialLogError.comp hk
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((k n : ℝ) / (n : ℝ)))
        atTop (nhds (Real.log u)) :=
    (Real.continuousAt_log hu).tendsto.comp hratio
  have hproduct :=
    hratio.mul ((herror.add hlog).sub (tendsto_const_nhds (x := (1 : ℝ))))
  have heq :
      (fun n : ℕ =>
        ((k n : ℝ) / (n : ℝ)) *
          (factorialLogError (k n) +
            Real.log ((k n : ℝ) / (n : ℝ)) - 1)) =ᶠ[atTop]
      (fun n : ℕ =>
        Real.log ((k n).factorial : ℝ) / (n : ℝ) -
          ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) := by
    filter_upwards [hk.eventually (eventually_ne_atTop (0 : ℕ)),
      eventually_ne_atTop (0 : ℕ)] with n hkn hn
    exact (scaled_log_factorial_identity (k n) n hkn hn).symm
  simpa only [zero_add, mul_sub, mul_one] using hproduct.congr' heq

theorem log_add_choose_div_eq (a b n : ℕ) :
    Real.log (((a + b).choose a : ℝ)) / (n : ℝ) =
      Real.log ((a + b).factorial : ℝ) / (n : ℝ) -
        Real.log (a.factorial : ℝ) / (n : ℝ) -
        Real.log (b.factorial : ℝ) / (n : ℝ) := by
  rw [Nat.cast_add_choose ℝ]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring

theorem tendsto_log_add_choose_div
    (k l : ℕ → ℕ) (u v : ℝ)
    (hk : Tendsto k atTop atTop)
    (hl : Tendsto l atTop atTop)
    (hku : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (nhds u))
    (hlv : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ))
      atTop (nhds v))
    (hu : 0 < u) (hv : 0 < v) :
    Tendsto
      (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ))
      atTop
      (nhds ((u + v) * Real.log (u + v) -
        u * Real.log u - v * Real.log v)) := by
  have hsum : Tendsto (fun n : ℕ => k n + l n) atTop atTop := by
    apply tendsto_atTop_mono (f := k)
    · intro n
      omega
    · exact hk
  have hsumratio :
      Tendsto (fun n : ℕ => ((k n + l n : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (u + v)) := by
    simpa only [Nat.cast_add, add_div] using hku.add hlv
  have htotal :=
    tendsto_scaled_log_factorial_sub (fun n => k n + l n)
      (u + v) hsum hsumratio (ne_of_gt (add_pos hu hv))
  have hfirst := tendsto_scaled_log_factorial_sub k u hk hku hu.ne'
  have hsecond := tendsto_scaled_log_factorial_sub l v hl hlv hv.ne'
  have hcomb := (htotal.sub hfirst).sub hsecond
  have heq :
      (fun n : ℕ =>
        (Real.log ((k n + l n).factorial : ℝ) / (n : ℝ) -
          (((k n + l n : ℕ) : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((k n).factorial : ℝ) / (n : ℝ) -
            ((k n : ℝ) / (n : ℝ)) * Real.log (n : ℝ)) -
          (Real.log ((l n).factorial : ℝ) / (n : ℝ) -
            ((l n : ℝ) / (n : ℝ)) * Real.log (n : ℝ))) =ᶠ[atTop]
  (fun n : ℕ =>
        Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)) := by
    apply Eventually.of_forall
    intro n
    change _ = Real.log (((k n + l n).choose (k n) : ℝ)) / (n : ℝ)
    rw [log_add_choose_div_eq]
    push_cast
    ring
  have hlimit :
      ((u + v) * Real.log (u + v) - (u + v)) -
          (u * Real.log u - u) - (v * Real.log v - v) =
        (u + v) * Real.log (u + v) -
          u * Real.log u - v * Real.log v := by
    ring
  rw [← hlimit]
  exact hcomb.congr' heq

end

end SpherePacking

namespace MetricCodes

section

open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology

namespace Hamming

/-- The finite family of length-`n` binary codes with minimum distance at least `d`. -/
noncomputable def validCodes (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact Finset.univ.filter (MetricCodes.IsBinaryCode d)

theorem mem_validCodes {n d : ℕ} (C : Finset (BinaryWord n)) :
    C ∈ validCodes n d ↔ MetricCodes.IsBinaryCode d C := by
  classical
  simp only [validCodes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The code number used in the binary-code argument. -/
noncomputable def codeNumber (n d : ℕ) : ℕ :=
  (validCodes n d).sup fun C => C.card

theorem card_le_codeNumber {n d : ℕ} (C : Finset (BinaryWord n))
    (hC : MetricCodes.IsBinaryCode d C) :
    C.card ≤ codeNumber n d := by
  unfold codeNumber
  exact Finset.le_sup ((mem_validCodes C).2 hC)

theorem codeNumber_pos (n d : ℕ) : 0 < codeNumber n d := by
  classical
  let x : BinaryWord n := fun _ => false
  have hcode : MetricCodes.IsBinaryCode d ({x} : Finset (BinaryWord n)) := by
    intro u hu v hv huv
    have hu' : u = x := Finset.mem_singleton.mp hu
    have hv' : v = x := Finset.mem_singleton.mp hv
    exact False.elim (huv (hu'.trans hv'.symm))
  have hcard : 1 ≤ codeNumber n d := by
    simpa only [Finset.card_singleton] using card_le_codeNumber ({ x } : Finset (BinaryWord n))
      hcode
  omega

/-- The ambient dimension used in the binary-code argument. -/
def ambientDimension (n k L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j)

theorem hammingFibreDimension_pos {n k : ℕ} (hk : 2 * k ≤ n) :
    0 < MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp only [hammingFibreDimension, booleanHarmonicDimension, Order.lt_one_iff]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

/-- The threshold used in the binary-code argument. -/
def threshold (n d : ℕ) : ℝ :=
  1 - 2 * (d : ℝ) / (n : ℝ)

/-- The index used in the binary-code argument. -/
abbrev Index (k L : ℕ) := Fin (L - k + 1)

/-- The space used in the binary-code argument. -/
abbrev Space (k L : ℕ) := EuclideanSpace ℝ (Index k L)

/-- The matrix used in the binary-code argument. -/
def matrix (n k L : ℕ) : Matrix (Index k L) (Index k L) ℝ :=
  MetricCodes.hammingJacobiMatrix n k L

/-- The operator used in the binary-code argument. -/
def operator (n k L : ℕ) : Space k L →ₗ[ℝ] Space k L :=
  Matrix.toEuclideanLin (matrix n k L)

/-- The continuous operator used in the binary-code argument. -/
def continuousOperator (n k L : ℕ) : Space k L →L[ℝ] Space k L :=
  LinearMap.toContinuousLinearMap (operator n k L)

/-- The rayleigh used in the binary-code argument. -/
def rayleigh (n k L : ℕ) (x : Space k L) : ℝ :=
  (continuousOperator n k L).rayleighQuotient x

/-- The top eigenvalue used in the binary-code argument. -/
def topEigenvalue (n k L : ℕ) : ℝ :=
  ⨆ x : {x : Space k L // x ≠ 0}, rayleigh n k L x

/-- The coordinate abs used in the binary-code argument. -/
abbrev coordinateAbs (k L : ℕ) (x : Space k L) : Space k L :=
  MetricCodes.Spherical.HigherHierarchyFinitePerron.coordinateAbs x

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy, Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).2
  simpa only [one_mul] using (Real.binEntropy_le_log_two (p := u))

theorem binaryEntropy_continuous : Continuous MetricCodes.binaryEntropy := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact Real.binEntropy_continuous.div_const (Real.log 2)

/-- The feasible used in the binary-code argument. -/
def Feasible (δ a b : ℝ) : Prop :=
  0 ≤ b ∧ b < a ∧ a ≤ (1 : ℝ) / 2 ∧
    1 - 2 * δ < MetricCodes.hammingGamma a b

/-- The rate set used in the binary-code argument. -/
def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible δ a b ∧
    r = MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b}

/-- The variational rate used in the binary-code argument. -/
def variationalRate (δ : ℝ) : ℝ := sInf (rateSet δ)

theorem rateSet_bddBelow (δ : ℝ) : BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨a, b, hfeasible, rfl⟩
  obtain ⟨hb, hba, ha, hgamma⟩ := hfeasible
  have ha0 : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have ha1 : a ≤ 1 := by linarith
  have hapos := MetricCodes.binaryEntropy_nonneg ha0 ha1
  have hble := binaryEntropy_le_one b
  linarith

theorem variationalRate_le_of_feasible {δ a b : ℝ}
    (h : Feasible δ a b) :
    variationalRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact csInf_le (rateSet_bddBelow δ) ⟨a, b, h, rfl⟩

/-- The classical parameter used in the binary-code argument. -/
def classicalParameter (δ : ℝ) : ℝ :=
  (1 : ℝ) / 2 - Real.sqrt (δ * (1 - δ))

/-- The classical rate used in the binary-code argument. -/
def classicalRate (δ : ℝ) : ℝ :=
  MetricCodes.binaryEntropy (classicalParameter δ)

theorem classicalParameter_lt_half {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ < (1 : ℝ) / 2 := by
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  unfold classicalParameter
  have hsqrt := Real.sqrt_pos.2 hrad
  linarith

theorem classicalParameter_pos {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    0 < classicalParameter δ := by
  have hsquare : 0 < (δ - (1 : ℝ) / 2) ^ 2 :=
    sq_pos_of_ne_zero (by linarith)
  have hrad : 0 < δ * (1 - δ) := mul_pos hδ (by linarith)
  have hrad_lt : δ * (1 - δ) < ((1 : ℝ) / 2) ^ 2 := by
    nlinarith
  have hroot : Real.sqrt (δ * (1 - δ)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num)).2 hrad_lt
  unfold classicalParameter
  linarith

theorem classicalParameter_mul_one_sub {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    classicalParameter δ * (1 - classicalParameter δ) =
      ((1 : ℝ) / 2 - δ) ^ 2 := by
  have hrad : 0 ≤ δ * (1 - δ) :=
    (mul_pos hδ (by linarith)).le
  have hsqrt := Real.sq_sqrt hrad
  unfold classicalParameter
  nlinarith

theorem hammingGamma_zero {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    MetricCodes.hammingGamma a 0 = 2 * Real.sqrt (a * (1 - a)) := by
  have hrad : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha')
  have hsqrt : Real.sqrt (a * (1 - a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hsquare := Real.sq_sqrt hrad.le
  unfold MetricCodes.hammingGamma
  simp only [sub_zero]
  field_simp [hsqrt]
  nlinarith

theorem hammingGamma_classicalParameter {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    MetricCodes.hammingGamma (classicalParameter δ) 0 = 1 - 2 * δ := by
  have ha := classicalParameter_pos hδ hδ'
  have ha' : classicalParameter δ < 1 :=
    (classicalParameter_lt_half hδ hδ').trans (by norm_num)
  rw [hammingGamma_zero ha ha',
    classicalParameter_mul_one_sub hδ hδ',
    Real.sqrt_sq (by linarith : 0 ≤ (1 : ℝ) / 2 - δ)]
  ring

/-- The slope `2 / (1 - 2 * a) + 1` used to perturb the Hamming bound parameters. -/
def improvementSlope (a : ℝ) : ℝ :=
  2 / (1 - 2 * a) + 1

/-- The affine perturbation of `a` with slope `improvementSlope a` and parameter `b`. -/
def improvementPath (a b : ℝ) : ℝ :=
  a + improvementSlope a * b

theorem improvementSlope_gt_one {a : ℝ} (ha : a < (1 : ℝ) / 2) :
    1 < improvementSlope a := by
  have hden : 0 < 1 - 2 * a := by linarith
  have hfrac : 0 < 2 / (1 - 2 * a) := by positivity
  unfold improvementSlope
  linarith

theorem tendsto_improvementPath_zero (a : ℝ) :
    Tendsto (improvementPath a) (𝓝[>] (0 : ℝ)) (nhds a) := by
  have hcontinuous : Continuous (improvementPath a) := by
    unfold improvementPath
    fun_prop
  simpa only [improvementPath, mul_zero, add_zero] using
    (hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds

/-- The cubic factor remaining after extracting `b` from the difference of the squared spectral-
bound expressions. -/
def spectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let r := a * (1 - a)
  let p := c * (1 - 2 * a) - 1
  let q := c ^ 2 - 1
  r * (c * (1 - 2 * a) - 2) +
    b * (p ^ 2 + r * (2 - c ^ 2)) -
      2 * b ^ 2 * p * q + b ^ 3 * q ^ 2

theorem spectralMarginPolynomial_factor (a c b : ℝ) :
    ((a + c * b - b) * (1 - (a + c * b) - b)) ^ 2 -
      (a * (1 - a)) * ((a + c * b) * (1 - (a + c * b))) =
        b * spectralMarginPolynomial a c b := by
  unfold spectralMarginPolynomial
  ring

theorem spectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (spectralMarginPolynomial a c) := by
  unfold spectralMarginPolynomial
  fun_prop

theorem spectralMarginPolynomial_improvement_zero {a : ℝ}
    (ha : a < (1 : ℝ) / 2) :
    spectralMarginPolynomial a (improvementSlope a) 0 =
      a * (1 - a) * (1 - 2 * a) := by
  have hden : 1 - 2 * a ≠ 0 := by linarith
  have hden' : 1 - a * 2 ≠ 0 := by
    simpa only [ne_eq, mul_comm] using hden
  unfold spectralMarginPolynomial improvementSlope
  field_simp [hden, hden']; ring

theorem eventually_hammingGamma_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.hammingGamma a 0 <
        MetricCodes.hammingGamma (improvementPath a b) b := by
  have hzero : 0 < spectralMarginPolynomial a (improvementSlope a) 0 := by
    rw [spectralMarginPolynomial_improvement_zero ha']
    have ha1 : 0 < 1 - a := by linarith
    have hhalf : 0 < 1 - 2 * a := by linarith
    exact mul_pos (mul_pos ha ha1) hhalf
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < spectralMarginPolynomial a (improvementSlope a) b := by
    have hcontinuous :
        ContinuousAt
          (spectralMarginPolynomial a (improvementSlope a)) 0 :=
      (spectralMarginPolynomial_continuous a (improvementSlope a)).continuousAt
    have hlim := hcontinuous.tendsto
    exact nhdsWithin_le_nhds (hlim.eventually (lt_mem_nhds hzero))
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a).eventually (gt_mem_nhds ha')
  have hc : 1 < improvementSlope a := improvementSlope_gt_one ha'
  filter_upwards [hpoly, hhalf, self_mem_nhdsWithin]
    with b hbpoly hbhalf (hb : 0 < b)
  have hbpath : b < improvementPath a b := by
    unfold improvementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < improvementPath a b := lt_trans hb hbpath
  have hpath1 : improvementPath a b < 1 :=
    hbhalf.trans (by norm_num)
  have htail : 0 < 1 - improvementPath a b - b := by
    linarith
  have hbase : 0 < a * (1 - a) := mul_pos ha (by linarith)
  have hrad : 0 < improvementPath a b * (1 - improvementPath a b) :=
    mul_pos hpath (sub_pos.mpr hpath1)
  have hfactor :
      ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) =
        b * spectralMarginPolynomial a (improvementSlope a) b := by
    simpa only [improvementPath] using spectralMarginPolynomial_factor a (improvementSlope a) b
  have hmargin :
      0 < ((improvementPath a b - b) *
        (1 - improvementPath a b - b)) ^ 2 -
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [hfactor]
    exact mul_pos hb hbpoly
  have htarget :
      0 < (improvementPath a b - b) *
        (1 - improvementPath a b - b) :=
    mul_pos (sub_pos.mpr hbpath) htail
  have hsquare :
      (Real.sqrt (a * (1 - a)) *
        Real.sqrt (improvementPath a b *
          (1 - improvementPath a b))) ^ 2 =
        (a * (1 - a)) *
          (improvementPath a b * (1 - improvementPath a b)) := by
    rw [mul_pow, Real.sq_sqrt hbase.le, Real.sq_sqrt hrad.le]
  have hroot :
      Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) <
        (improvementPath a b - b) *
          (1 - improvementPath a b - b) := by
    have hnonneg :
        0 ≤ Real.sqrt (a * (1 - a)) *
          Real.sqrt (improvementPath a b *
            (1 - improvementPath a b)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hquot :
      Real.sqrt (a * (1 - a)) <
        ((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b)) :=
    (lt_div_iff₀ (Real.sqrt_pos.2 hrad)).2 hroot
  rw [hammingGamma_zero ha (by linarith)]
  unfold MetricCodes.hammingGamma
  calc
    2 * Real.sqrt (a * (1 - a)) <
        2 * (((improvementPath a b - b) *
          (1 - improvementPath a b - b)) /
            Real.sqrt
              (improvementPath a b * (1 - improvementPath a b))) :=
      mul_lt_mul_of_pos_left hquot (by norm_num)
    _ = 2 * (improvementPath a b - b) *
        (1 - improvementPath a b - b) /
          Real.sqrt
            (improvementPath a b * (1 - improvementPath a b)) := by ring

theorem differentiableAt_binaryEntropy {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    DifferentiableAt ℝ MetricCodes.binaryEntropy a := by
  have hfun : MetricCodes.binaryEntropy =
      (fun u : ℝ => Real.binEntropy u / Real.log 2) :=
    funext binaryEntropy_eq_binEntropy_div_log
  rw [hfun]
  exact
    (Real.differentiableAt_binEntropy ha.ne' (ne_of_lt ha')).div_const
      (Real.log 2)

theorem neg_mul_logb_le_binaryEntropy {b : ℝ}
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    b * (-Real.logb 2 b) ≤ MetricCodes.binaryEntropy b := by
  have hlog : Real.logb 2 (1 - b) ≤ 0 :=
    Real.logb_nonpos (by norm_num) (by linarith) (by linarith)
  have hterm : (1 - b) * Real.logb 2 (1 - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  unfold MetricCodes.binaryEntropy
  nlinarith

theorem eventually_binaryEntropy_improvement {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy b < MetricCodes.binaryEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.binaryEntropy (improvementPath a b)
  have hinner : DifferentiableAt ℝ (improvementPath a) 0 := by
    unfold improvementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (improvementPath a 0) := by
    simpa only [improvementPath, mul_zero, add_zero] using
      differentiableAt_binaryEntropy ha (ha'.trans (by norm_num))
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, improvementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with b hbound hlogb hb1 (hb : 0 < b)
  have houter_bound :
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy a < b * M := by
    calc
      MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a =
        b * (b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a)) := by
            field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_binaryEntropy hb.le hb1.le
  linarith

theorem exists_strict_improving_feasible {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    ∃ a b : ℝ, Feasible δ a b ∧
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b < classicalRate δ := by
  let a₀ : ℝ := classicalParameter δ
  have ha₀ : 0 < a₀ := classicalParameter_pos hδ hδ'
  have ha₀half : a₀ < (1 : ℝ) / 2 :=
    classicalParameter_lt_half hδ hδ'
  have hgamma := eventually_hammingGamma_improvement ha₀ ha₀half
  have hentropy := eventually_binaryEntropy_improvement ha₀ ha₀half
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a₀ b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a₀).eventually
      (gt_mem_nhds ha₀half)
  have hc : 1 < improvementSlope a₀ :=
    improvementSlope_gt_one ha₀half
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible δ (improvementPath a₀ b) b ∧
          MetricCodes.binaryEntropy (improvementPath a₀ b) -
            MetricCodes.binaryEntropy b < classicalRate δ := by
    filter_upwards [hgamma, hentropy, hhalf, self_mem_nhdsWithin]
      with b hgamma' hentropy' hhalf' (hb : 0 < b)
    have hbpath : b < improvementPath a₀ b := by
      unfold improvementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb.le, hbpath, hhalf'.le, ?_⟩
      have hboundary : MetricCodes.hammingGamma a₀ 0 = 1 - 2 * δ := by
        dsimp [a₀]
        exact hammingGamma_classicalParameter hδ hδ'
      rwa [hboundary] at hgamma'
    · simpa only [classicalRate] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨improvementPath a₀ b, b, hb⟩

theorem variationalRate_lt_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    variationalRate δ < classicalRate δ := by
  obtain ⟨a, b, hfeasible, himprove⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact (variationalRate_le_of_feasible hfeasible).trans_lt himprove

/-- The longitudinal degree used in the binary-code argument. -/
def longitudinalDegree (a : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (a * (n : ℝ))

/-- The transverse degree used in the binary-code argument. -/
def transverseDegree (b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (b * (n : ℝ))

theorem tendsto_longitudinal_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa only [longitudinalDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The normalized coefficient used in the binary-code argument. -/
def normalizedCoefficient (x y z : ℝ) : ℝ :=
  ((x - y + z) * (1 - x - y)) /
    Real.sqrt ((x + z) * (1 - x))

/-- The terminal indicator used in the binary-code argument. -/
def terminalIndicator (d m p : ℕ) : ℝ :=
  if d - m ≤ p then 1 else 0

/-- The terminal vector used in the binary-code argument. -/
def terminalVector (k L m : ℕ) : Space k L :=
  WithLp.toLp 2
    (fun p : Fin (L - k + 1) => terminalIndicator (L - k) m p.val)

/-- The terminal edge rayleigh used in the binary-code argument. -/
def terminalEdgeRayleigh (a b : ℝ) (m n : ℕ) : ℝ :=
  (2 * ∑ r ∈ Finset.range m,
    MetricCodes.hammingJacobiEntry n (transverseDegree b n)
      (longitudinalDegree a n - (m - r))) /
        ((m : ℝ) + 1)

theorem longitudinalDegree_le_dimension {a : ℝ}
    (ha : a ≤ 1) (n : ℕ) :
    longitudinalDegree a n ≤ n := by
  unfold longitudinalDegree
  apply Nat.floor_le_of_le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)

theorem complement_longitudinalDegree_floor_le {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (n : ℕ) :
    longitudinalDegree (1 - a) n ≤ n - longitudinalDegree a n := by
  have hk := longitudinalDegree_le_dimension ha' n
  have hfloor : (longitudinalDegree a n : ℝ) ≤ a * (n : ℝ) := by
    unfold longitudinalDegree
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  change Nat.floor ((1 - a) * (n : ℝ)) ≤
    n - longitudinalDegree a n
  apply Nat.floor_le_of_le
  change (1 - a) * (n : ℝ) ≤
    ((n - longitudinalDegree a n : ℕ) : ℝ)
  rw [Nat.cast_sub hk]
  nlinarith

theorem tendsto_complement_longitudinalDegree {a : ℝ}
    (ha : 0 ≤ a) (ha' : a < 1) :
    Tendsto (fun n : ℕ => n - longitudinalDegree a n) atTop atTop := by
  have hcomp : Tendsto (longitudinalDegree (1 - a)) atTop atTop := by
    change Tendsto
      (fun n : ℕ => Nat.floor ((1 - a) * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop (1 - a) (sub_pos.mpr ha')
  exact tendsto_atTop_mono
    (fun n => complement_longitudinalDegree_floor_le ha ha'.le n)
    hcomp

theorem tendsto_complement_longitudinal_ratio {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ => ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  have hone : Tendsto
      (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp only [ne_eq, Nat.cast_eq_zero, hn, not_false_eq_true, div_self]
  have hmain := hone.sub (tendsto_longitudinal_ratio ha)
  refine hmain.congr' (Filter.Eventually.of_forall fun n => ?_)
  change
    (n : ℝ) / (n : ℝ) -
      (longitudinalDegree a n : ℝ) / (n : ℝ) =
        ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ)
  rw [Nat.cast_sub (longitudinalDegree_le_dimension ha' n)]
  ring

theorem tendsto_log_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
      atTop (nhds (Real.binEntropy a)) := by
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  have hcomplement := tendsto_complement_longitudinalDegree ha.le ha'
  have hratio := tendsto_longitudinal_ratio ha.le
  have hcomplementratio :=
    tendsto_complement_longitudinal_ratio ha.le ha'.le
  have hchoose := SpherePacking.tendsto_log_add_choose_div
    (longitudinalDegree a)
    (fun n : ℕ => n - longitudinalDegree a n)
    a (1 - a)
    hgrowth hcomplement hratio hcomplementratio ha (sub_pos.mpr ha')
  have hlimit :
      (a + (1 - a)) * Real.log (a + (1 - a)) -
        a * Real.log a - (1 - a) * Real.log (1 - a) =
        Real.binEntropy a := by
    simp only [add_sub_cancel, Real.log_one, mul_zero, zero_sub, Real.binEntropy, Real.log_inv,
      mul_neg]
    ring
  rw [hlimit] at hchoose
  refine hchoose.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hk := longitudinalDegree_le_dimension ha'.le n
  have hsum :
      longitudinalDegree a n + (n - longitudinalDegree a n) = n := by
    omega
  rw [hsum]

theorem tendsto_logb_choose_longitudinal {a : ℝ}
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (n.choose (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have h := (tendsto_log_choose_longitudinal ha ha').div_const (Real.log 2)
  rw [← binaryEntropy_eq_binEntropy_div_log a] at h
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem longitudinalDegree_le_half {a : ℝ}
    (ha : a ≤ (1 : ℝ) / 2) (n : ℕ) :
    longitudinalDegree a n ≤ n / 2 := by
  unfold longitudinalDegree
  calc
    Nat.floor (a * (n : ℝ)) ≤ Nat.floor ((n : ℝ) / 2) := by
      apply Nat.floor_mono
      have h := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
      linarith
    _ = n / 2 := by
      simpa only [Nat.cast_ofNat] using (Nat.floor_div_eq_div (K := ℝ) n 2)

theorem choose_le_mul_hammingFibreDimension
    {n k : ℕ} (hk : 2 * k ≤ n) :
    n.choose k ≤ (n + 1) * MetricCodes.hammingFibreDimension n k := by
  cases k with
  | zero => simp only [Nat.choose_zero_right, hammingFibreDimension, booleanHarmonicDimension,
              mul_one, le_add_iff_nonneg_left, zero_le]
  | succ j =>
      change n.choose (j + 1) ≤
        (n + 1) * (n.choose (j + 1) - n.choose j)
      have hpositive :=
        hammingFibreDimension_pos (n := n) (k := j + 1) hk
      change 0 < n.choose (j + 1) - n.choose j at hpositive
      have hmono : n.choose j ≤ n.choose (j + 1) :=
        (Nat.sub_pos_iff_lt.mp hpositive).le
      have hrec :
          (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
            (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq n j
      have hidentity :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hmono]
        calc
          ((n.choose (j + 1) : ℝ) - (n.choose j : ℝ)) *
              ((n - j : ℕ) : ℝ) =
            (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by ring
          _ = (n.choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) -
              (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
                rw [← hrec]
          _ = (n.choose (j + 1) : ℝ) *
              (((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ)) := by ring
      have hfactorNat : j + 2 ≤ n - j := by omega
      have hfactorReal :
          (1 : ℝ) ≤
            ((n - j : ℕ) : ℝ) - ((j + 1 : ℕ) : ℝ) := by
        have hcast : ((j + 2 : ℕ) : ℝ) ≤ ((n - j : ℕ) : ℝ) := by
          exact_mod_cast hfactorNat
        have hcastj : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
          norm_num
        rw [hcastj]
        push_cast at hcast
        linarith
      have hlower :
          (n.choose (j + 1) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) := by
        rw [hidentity]
        nlinarith [Nat.cast_nonneg (α := ℝ) (n.choose (j + 1))]
      have hrange :
          ((n - j : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n - j ≤ n + 1 by omega)
      have hupper :
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by
        calc
          ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n - j : ℕ) : ℝ) ≤
            ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) *
              ((n + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hrange (Nat.cast_nonneg _)
          _ = ((n + 1 : ℕ) : ℝ) *
              ((n.choose (j + 1) - n.choose j : ℕ) : ℝ) := by ring
      exact_mod_cast hlower.trans hupper

theorem hammingFibreDimension_le_choose (n k : ℕ) :
    MetricCodes.hammingFibreDimension n k ≤ n.choose k := by
  cases k with
  | zero => simp only [hammingFibreDimension, booleanHarmonicDimension, Nat.choose_zero_right,
              Std.le_refl]
  | succ j =>
      change n.choose (j + 1) - n.choose j ≤ n.choose (j + 1)
      exact Nat.sub_le _ _

theorem tendsto_logb_succ_div :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := SpherePacking.tendsto_log_two_mul_natCast_div_natCast
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hle :
      ∀ᶠ n : ℕ in atTop,
        Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.log_le_log
    · positivity
    · have hnat : n + 1 ≤ 2 * n := by omega
      exact_mod_cast hnat
  have hnatural :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hzero hupper hnonneg hle
  have hbase := hnatural.div_const (Real.log 2)
  have hbase' :
      Tendsto
        (fun n : ℕ =>
          (Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log 2)
        atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, zero_div] using hbase
  refine hbase'.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring

theorem tendsto_logb_hammingFibreDimension {b : ℝ}
    (hb : 0 < b) (hb' : b ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy b)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hb' (by norm_num)
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa only [transverseDegree, longitudinalDegree] using tendsto_logb_choose_longitudinal hb hb1
  have hpoly := tendsto_logb_succ_div
  have hlowerlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa only [transverseDegree, longitudinalDegree] using longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    have hchoosepos : 0 < (n.choose (transverseDegree b n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : transverseDegree b n ≤ n)
    have hlog :
        Real.logb 2 (n.choose (transverseDegree b n) : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.hammingFibreDimension n
                (transverseDegree b n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        hchoosepos
      exact_mod_cast choose_le_mul_hammingFibreDimension hkhalf
    calc
      Real.logb 2 (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 (n.choose (transverseDegree b n) : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
          (MetricCodes.hammingFibreDimension n
            (transverseDegree b n) : ℝ) / (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).2
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa only [transverseDegree, longitudinalDegree] using longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hfibre
    exact_mod_cast hammingFibreDimension_le_choose n
      (transverseDegree b n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlim hchoose hlower hupper

/-- The binary rate used in the binary-code argument. -/
def binaryRate (δ : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ))
    Filter.atTop

theorem tendsto_ceil_distance_ratio {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ))
      atTop (nhds δ) := by
  simpa only [Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The window fibre quotient used in the binary-code argument. -/
def windowFibreQuotient (a b : ℝ) (n : ℕ) : ℝ :=
  (ambientDimension n (transverseDegree b n)
      (longitudinalDegree a n) : ℝ) /
    (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ)

theorem codeLogRate_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) := by
  apply div_nonneg
  · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  · exact Nat.cast_nonneg n

theorem binaryRate_le_of_eventually {δ r : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds r))
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ u n) :
    binaryRate δ ≤ r := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (codeLogRate_nonneg δ))
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) w :=
    hlower.isCoboundedUnder_le
  have hcomparison : Filter.limsup w atTop ≤ Filter.limsup u atTop :=
    Filter.limsup_le_limsup hbound hcob hu.isBoundedUnder_le
  change Filter.limsup w atTop ≤ r
  exact hcomparison.trans_eq hu.limsup_eq

/-- The spectral gap used in the binary-code argument. -/
def spectralGap (δ a b : ℝ) : ℝ :=
  (MetricCodes.hammingGamma a b - (1 - 2 * δ)) / 4

/-- The spectral prefactor used in the binary-code argument. -/
def spectralPrefactor (δ a b : ℝ) : ℝ :=
  2 / spectralGap δ a b

end Hamming

end

namespace Johnson

section

open scoped BigOperators InnerProductSpace Matrix

/-- The finite family of binary codes of length `n` and minimum distance at least `d`. -/
def binaryCodeFamily (n d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (Finset.univ : Finset (BinaryWord n)).powerset.filter
    (fun C => IsBinaryCode d C)

@[simp] theorem mem_binaryCodeFamily {n d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ binaryCodeFamily n d ↔ IsBinaryCode d C := by
  classical
  simp only [binaryCodeFamily, Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The binary code number used in the Johnson-code argument. -/
def binaryCodeNumber (n d : ℕ) : ℕ :=
  (binaryCodeFamily n d).sup (fun C => C.card)

/-- The finite family of minimum-distance-`d` codes contained in the weight-`w` shell. -/
def shellCodeFamily (n w d : ℕ) : Finset (Finset (BinaryWord n)) := by
  classical
  exact (weightShell n w).powerset.filter (fun C => IsBinaryCode d C)

@[simp] theorem mem_shellCodeFamily {n w d : ℕ}
    (C : Finset (BinaryWord n)) :
    C ∈ shellCodeFamily n w d ↔
      C ⊆ weightShell n w ∧ IsBinaryCode d C := by
  classical
  simp only [shellCodeFamily, Finset.mem_filter, Finset.mem_powerset]

/-- The largest cardinality of a minimum-distance-`d` code in the weight-`w` shell. -/
def shellCodeNumber (n w d : ℕ) : ℕ :=
  (shellCodeFamily n w d).sup (fun C => C.card)

/-- Forget the weight proof on each point of a finite Johnson-sphere code. -/
def words {n w : ℕ} (C : Finset (JohnsonSphere n w)) :
    Finset (BinaryWord n) :=
  C.image Subtype.val

/-- The minimum-distance condition on the underlying binary words of a Johnson-sphere code. -/
def IsCode {n w : ℕ} (d : ℕ)
    (C : Finset (JohnsonSphere n w)) : Prop :=
  IsBinaryCode d (words C)

/-- Regard a code contained in the weight-`w` shell as a finite set of Johnson-sphere points. -/
def asSubtype {n w : ℕ} (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) :
    Finset (JohnsonSphere n w) := by
  classical
  exact C.attach.image (fun x =>
    (⟨x.val, (MetricCodes.mem_weightShell x.val).mp
      (hweight x.property)⟩ : JohnsonSphere n w))

/-- The correlation used in the Johnson-code argument. -/
def correlation {n w : ℕ} (x y : JohnsonSphere n w) : ℝ :=
  1 - (n : ℝ) * (MetricCodes.johnsonDist x y : ℝ) /
    ((w : ℝ) * ((n - w : ℕ) : ℝ))

@[simp] theorem correlation_self {n w : ℕ}
    (x : JohnsonSphere n w) :
    correlation x x = 1 := by
  simp only [correlation, johnsonDist, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
    CharP.cast_eq_zero, mul_zero, zero_div, sub_zero]

/-- The threshold used in the Johnson-code argument. -/
def threshold (n w d : ℕ) : ℝ :=
  1 - (n : ℝ) * (d : ℝ) /
    (2 * (w : ℝ) * ((n - w : ℕ) : ℝ))

/-- The coordinate indicator used in the Johnson-code argument. -/
def coordinateIndicator {n : ℕ} (x : BinaryWord n)
    (i : Fin n) : ℝ :=
  if i ∈ MetricCodes.wordSupport x then 1 else 0

theorem sum_coordinateIndicator {n : ℕ} (x : BinaryWord n) :
    (∑ i : Fin n, coordinateIndicator x i) =
      (MetricCodes.binaryWeight x : ℝ) := by
  simpa only [coordinateIndicator, mem_wordSupport, Finset.sum_boole,
    binaryWeight_eq_card_wordSupport, Nat.cast_inj,
    mul_one] using (MetricCodes.Boolean.sum_mem_indicator (MetricCodes.wordSupport x) (1 : ℝ))

/-- The geometric axis used in the Johnson-code argument. -/
def geometricAxis {n w : ℕ} (x : JohnsonSphere n w) : MetricCodes.Ambient n :=
  WithLp.toLp 2 (fun i : Fin n =>
    Real.sqrt ((n : ℝ) /
      ((w : ℝ) * ((n - w : ℕ) : ℝ))) *
        (coordinateIndicator (x : BinaryWord n) i -
          (w : ℝ) / (n : ℝ)))

/-- The support coordinates used in the Johnson-code argument. -/
abbrev SupportCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈ MetricCodes.wordSupport (x : BinaryWord n)}

/-- The complement coordinates used in the Johnson-code argument. -/
abbrev ComplementCoordinates {n w : ℕ} (x : JohnsonSphere n w) :=
  {i : Fin n // i ∈
    (Finset.univ : Finset (Fin n)) \
      MetricCodes.wordSupport (x : BinaryWord n)}

/-- The support coordinate equiv used in the Johnson-code argument. -/
def supportCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    SupportCoordinates x ≃ Fin w :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe, Fintype.card_fin]
    simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property)

/-- The complement coordinate equiv used in the Johnson-code argument. -/
def complementCoordinateEquiv {n w : ℕ} (x : JohnsonSphere n w) :
    ComplementCoordinates x ≃ Fin (n - w) :=
  Fintype.equivOfCardEq (by
    have hx : (MetricCodes.wordSupport (x : BinaryWord n)).card = w := by
      simpa only [MetricCodes.binaryWeight_eq_card_wordSupport] using x.property
    rw [Fintype.card_coe, Fintype.card_fin,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin, hx])

/-- The harmonic fibre index used in the Johnson-code argument. -/
abbrev HarmonicFibreIndex (n w p q : ℕ) :=
  Fin (MetricCodes.hammingFibreDimension w p) ×
    Fin (MetricCodes.hammingFibreDimension (n - w) q)

/-- The harmonic fibre index equiv used in the Johnson-code argument. -/
def harmonicFibreIndexEquiv (n w p q : ℕ) :
    HarmonicFibreIndex n w p q ≃
      Fin (MetricCodes.johnsonFibreDimension n w p q) :=
  Fintype.equivOfCardEq (by
    change
      Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p) ×
            Fin (MetricCodes.booleanHarmonicDimension (n - w) q)) =
        Fintype.card
          (Fin (MetricCodes.booleanHarmonicDimension w p *
            MetricCodes.booleanHarmonicDimension (n - w) q))
    rw [Fintype.card_prod]
    simp only [Fintype.card_fin])

/-- The shell window index used in the Johnson-code argument. -/
abbrev ShellWindowIndex (n p q L : ℕ) :=
  Σ i : Fin (L - (p + q) + 1),
    Fin (MetricCodes.booleanHarmonicDimension n (p + q + i.val))

theorem shellWindowIndex_card (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    Fintype.card (ShellWindowIndex n p q L) =
      MetricCodes.johnsonAmbientDimension n (p + q) L := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  unfold MetricCodes.johnsonAmbientDimension
  refine Finset.sum_bij (fun i _ => p + q + i.val) ?_ ?_ ?_ ?_
  · intro i _
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hi := i.isLt
      omega
  · intro i _ j _ heq
    apply Fin.ext
    omega
  · intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    refine ⟨⟨j - (p + q), by omega⟩,
      Finset.mem_univ _, ?_⟩
    change p + q + (j - (p + q)) = j
    exact Nat.add_sub_of_le hlo
  · intro i _
    rfl

/-- The shell window index equiv used in the Johnson-code argument. -/
def shellWindowIndexEquiv (n p q L : ℕ)
    (hfirst : p + q ≤ L) :
    ShellWindowIndex n p q L ≃
      Fin (MetricCodes.johnsonAmbientDimension n (p + q) L) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using
      shellWindowIndex_card n p q L hfirst)

/-- The index used in the Johnson-code argument. -/
abbrev Index (p q L : ℕ) := Fin (L - (p + q) + 1)

/-- The space used in the Johnson-code argument. -/
abbrev Space (p q L : ℕ) := EuclideanSpace ℝ (Index p q L)

/-- The matrix used in the Johnson-code argument. -/
def matrix (n w p q L : ℕ) :
    Matrix (Index p q L) (Index p q L) ℝ :=
  MetricCodes.johnsonJacobiMatrix n w p q L

/-- The operator used in the Johnson-code argument. -/
def operator (n w p q L : ℕ) : Space p q L →ₗ[ℝ] Space p q L :=
  Matrix.toEuclideanLin (matrix n w p q L)

/-- The continuous operator used in the Johnson-code argument. -/
def continuousOperator (n w p q L : ℕ) :
    Space p q L →L[ℝ] Space p q L :=
  LinearMap.toContinuousLinearMap (operator n w p q L)

/-- The rayleigh used in the Johnson-code argument. -/
def rayleigh (n w p q L : ℕ) (x : Space p q L) : ℝ :=
  (continuousOperator n w p q L).rayleighQuotient x

/-- The top eigenvalue used in the Johnson-code argument. -/
def topEigenvalue (n w p q L : ℕ) : ℝ :=
  ⨆ x : {x : Space p q L // x ≠ 0}, rayleigh n w p q L x

/-- Data encoding the admissible degrees construction. -/
structure AdmissibleDegrees (n w p q L : ℕ) : Prop where
  weight_pos : 0 < w
  weight_lt : w < n
  weight_half : 2 * w ≤ n
  support_half : 2 * p ≤ w
  complement_half : 2 * q ≤ n - w
  first_le : p + q ≤ L
  last_le : L ≤ MetricCodes.johnsonLastDegree n w p q

theorem AdmissibleDegrees.terminal_le_weight
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ w := by
  exact h.last_le.trans (by
    unfold MetricCodes.johnsonLastDegree
    exact min_le_left _ _)

theorem AdmissibleDegrees.terminal_le_half
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    L ≤ n / 2 := by
  have hL := h.terminal_le_weight
  have hw := h.weight_half
  omega

theorem booleanHarmonicDimension_pos {n k : ℕ}
    (hk : 2 * k ≤ n) :
    0 < MetricCodes.booleanHarmonicDimension n k := by
  cases k with
  | zero => simp only [booleanHarmonicDimension, Order.lt_one_iff]
  | succ j =>
      change 0 < n.choose (j + 1) - n.choose j
      apply Nat.sub_pos_of_lt
      have hchoose : 0 < n.choose j := Nat.choose_pos (by omega)
      have hfactor : j + 1 < n - j := by omega
      have hmul :
          n.choose j * (j + 1) < n.choose j * (n - j) :=
        Nat.mul_lt_mul_of_pos_left hfactor hchoose
      have hmul' :
          n.choose j * (j + 1) < n.choose (j + 1) * (j + 1) := by
        calc
          n.choose j * (j + 1) < n.choose j * (n - j) := hmul
          _ = n.choose (j + 1) * (j + 1) :=
            (Nat.choose_succ_right_eq n j).symm
      exact (Nat.mul_lt_mul_right (by omega : 0 < j + 1)).mp hmul'

theorem AdmissibleDegrees.fibreDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L) :
    0 < MetricCodes.johnsonFibreDimension n w p q := by
  unfold MetricCodes.johnsonFibreDimension
  exact Nat.mul_pos
    (booleanHarmonicDimension_pos h.support_half)
    (booleanHarmonicDimension_pos h.complement_half)

theorem ambientDimension_eq {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L) :
    MetricCodes.johnsonAmbientDimension n (p + q) L =
      n.choose L - MetricCodes.precedingBinomial n (p + q) := by
  exact MetricCodes.johnsonAmbientDimension_eq_of_fibre n p q L
    h.first_le h.terminal_le_half

theorem zonalDiagonal_eq {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    MetricCodes.johnsonZonalDiagonal n w j =
      MetricCodes.johnsonM n w ^ 2 * (j : ℝ) *
        ((n : ℝ) - (j : ℝ) + 1) /
        ((w : ℝ) * ((n - w : ℕ) : ℝ) *
          MetricCodes.johnsonJ n j * (MetricCodes.johnsonJ n j + 1)) := by
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hj' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hj
  have hsmall : (2 : ℝ) * (j : ℝ) < (n : ℝ) := by
    nlinarith
  have hw' : (w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hw
  have hN' : (n : ℝ) - (w : ℝ) ≠ 0 := by
    have hwn' : (w : ℝ) < (n : ℝ) := by exact_mod_cast hwn
    linarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hJone : MetricCodes.johnsonJ n j + 1 ≠ 0 := by
    linarith
  have hD :
      (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
          (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 ≠ 0 := by
    have hfactor :
        (n : ℝ) * 2 - (n : ℝ) * (j : ℝ) * 4 +
            (n : ℝ) ^ 2 - (j : ℝ) * 4 + (j : ℝ) ^ 2 * 4 =
          ((n : ℝ) - 2 * (j : ℝ)) *
            ((n : ℝ) - 2 * (j : ℝ) + 2) := by
      ring
    rw [hfactor]
    exact (mul_pos (by linarith) (by linarith)).ne'
  unfold MetricCodes.johnsonZonalDiagonal MetricCodes.johnsonDiagonal
    MetricCodes.johnsonMu MetricCodes.johnsonM
    MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
  rw [Nat.cast_sub (Nat.le_of_lt hwn)]
  field_simp [hw', hN', hJ.ne', hJone]
  unfold MetricCodes.johnsonJ
  ring

theorem zonalDiagonal_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hj : 0 < j) (hjw : j ≤ w) :
    0 < MetricCodes.johnsonZonalDiagonal n w j := by
  rw [zonalDiagonal_eq hw hhalf hjw]
  have hwn : w < n := by omega
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hjw
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hlast : 0 < (n : ℝ) - (j : ℝ) + 1 := by
    nlinarith
  positivity

theorem associatedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonEdge n w p q j := by
  have hwn : w < n := by omega
  have hN : 0 < n - w := Nat.sub_pos_of_lt hwn
  have hjw : j < w := by
    exact lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  have hjleft : j < w - p + q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hjright : j < n - w + p - q := by
    apply lt_of_lt_of_le hlast
    unfold MetricCodes.johnsonLastDegree
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hhalf' : (2 : ℝ) * (w : ℝ) < (n : ℝ) := by
    exact_mod_cast hhalf
  have hjw' : (j : ℝ) < (w : ℝ) := by
    exact_mod_cast hjw
  have hfirst' : (p : ℝ) + (q : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hfirst
  have hjleft' :
      (j : ℝ) < (w : ℝ) - (p : ℝ) + (q : ℝ) := by
    have hcast : (j : ℝ) < ((w - p + q : ℕ) : ℝ) := by
      exact_mod_cast hjleft
    simpa only [Nat.cast_add, Nat.cast_sub (by omega : p ≤ w)]
      using hcast
  have hjright' :
      (j : ℝ) < (n : ℝ) - (w : ℝ) + (p : ℝ) - (q : ℝ) := by
    have hcast : (j : ℝ) < ((n - w + p - q : ℕ) : ℝ) := by
      exact_mod_cast hjright
    simpa only [Nat.cast_sub (by omega : q ≤ n - w + p),
      Nat.cast_add, Nat.cast_sub (by omega : w ≤ n)] using hcast
  have hJ : 0 < MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hM : 0 < MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonM
    nlinarith
  have hJminusM : 0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonM n w := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonM
    linarith
  have hJplusM : 0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonM n w := by
    linarith
  have hJminusDelta :
      0 < MetricCodes.johnsonJ n j - MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hJplusDelta :
      0 < MetricCodes.johnsonJ n j + MetricCodes.johnsonDelta n w p q := by
    unfold MetricCodes.johnsonJ MetricCodes.johnsonDelta
      MetricCodes.johnsonJ2 MetricCodes.johnsonJ1
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaMinus :
      0 < MetricCodes.johnsonSigma n w p q + 1 -
        MetricCodes.johnsonJ n j := by
    unfold MetricCodes.johnsonSigma MetricCodes.johnsonJ1 MetricCodes.johnsonJ2
      MetricCodes.johnsonJ
    rw [Nat.cast_sub (by omega : w ≤ n)]
    linarith
  have hSigmaPlus :
      0 < MetricCodes.johnsonSigma n w p q + 1 +
        MetricCodes.johnsonJ n j := by
    linarith
  have hJM :
      0 < MetricCodes.johnsonJ n j ^ 2 - MetricCodes.johnsonM n w ^ 2 := by
    nlinarith [mul_pos hJminusM hJplusM]
  have hJDelta :
      0 < MetricCodes.johnsonJ n j ^ 2 -
        MetricCodes.johnsonDelta n w p q ^ 2 := by
    nlinarith [mul_pos hJminusDelta hJplusDelta]
  have hSigma :
      0 < (MetricCodes.johnsonSigma n w p q + 1) ^ 2 -
        MetricCodes.johnsonJ n j ^ 2 := by
    nlinarith [mul_pos hSigmaMinus hSigmaPlus]
  have hjstep : (j : ℝ) + 1 ≤ (w : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hjw
  have hhalfstep :
      (2 : ℝ) * (w : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 2 * w + 1 ≤ n by omega)
  have hdenleft : 0 < 2 * MetricCodes.johnsonJ n j - 1 := by
    unfold MetricCodes.johnsonJ
    nlinarith
  have hdenright : 0 < 2 * MetricCodes.johnsonJ n j + 1 := by
    linarith
  have hnu : 0 < MetricCodes.johnsonNu n w p q j := by
    unfold MetricCodes.johnsonNu
    apply div_pos
    · exact Real.sqrt_pos.mpr
        (mul_pos (mul_pos hJM hJDelta) hSigma)
    · exact mul_pos (mul_pos (by norm_num) hJ)
        (Real.sqrt_pos.mpr (mul_pos hdenleft hdenright))
  unfold MetricCodes.johnsonEdge
  exact div_pos
    (mul_pos (by exact_mod_cast (show 0 < n by omega)) hnu)
    (mul_pos (by exact_mod_cast hw)
      (by exact_mod_cast hN))

theorem zonalEdge_pos {n w j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j < w) :
    0 < MetricCodes.johnsonZonalEdge n w j := by
  have hlast : MetricCodes.johnsonLastDegree n w 0 0 = w := by
    simp only [johnsonLastDegree, tsub_zero, add_zero, min_eq_left (by omega : w ≤ n - w), min_self]
  unfold MetricCodes.johnsonZonalEdge
  apply associatedEdge_pos hw hhalf (by omega) (by omega)
    (Nat.zero_le j)
  simpa only [hlast] using hj

theorem hattedDiagonal_nonneg {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n) (hj : j ≤ w) :
    0 ≤ MetricCodes.johnsonHattedDiagonal n w p q j := by
  by_cases hz : j = 0
  · subst j
    simp only [johnsonHattedDiagonal, ↓reduceIte, Std.le_refl]
  · exact MetricCodes.johnsonHattedDiagonal_nonneg
      (zonalDiagonal_pos hw hhalf (Nat.pos_of_ne_zero hz) hj)

theorem hattedEdge_pos {n w p q j : ℕ}
    (hw : 0 < w) (hhalf : 2 * w < n)
    (hp : 2 * p ≤ w) (hq : 2 * q ≤ n - w)
    (hfirst : p + q ≤ j)
    (hlast : j < MetricCodes.johnsonLastDegree n w p q) :
    0 < MetricCodes.johnsonHattedEdge n w p q j := by
  have hedge := associatedEdge_pos hw hhalf hp hq hfirst hlast
  have hjw : j < w :=
    lt_of_lt_of_le hlast (by
      unfold MetricCodes.johnsonLastDegree
      exact min_le_left _ _)
  unfold MetricCodes.johnsonHattedEdge
  exact div_pos (sq_pos_of_pos hedge)
    (zonalEdge_pos hw hhalf hjw)

theorem matrix_entry_nonneg {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (i j : Index p q L) :
    0 ≤ matrix n w p q L i j := by
  have hfirst := h.first_le
  have hiL : p + q + i.val ≤ L := by
    have hi := i.isLt
    omega
  have hjL : p + q + j.val ≤ L := by
    have hj := j.isLt
    omega
  unfold matrix MetricCodes.johnsonJacobiMatrix
  split_ifs with hdiag hforward hbackward
  · exact hattedDiagonal_nonneg h.weight_pos hstrict
      (hiL.trans h.terminal_le_weight)
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + i.val < L)
    exact h.last_le
  · apply (hattedEdge_pos h.weight_pos hstrict
      h.support_half h.complement_half (by omega) ?_).le
    apply lt_of_lt_of_le (by omega : p + q + j.val < L)
    exact h.last_le
  · exact le_rfl

/-- The coordinate abs used in the Johnson-code argument. -/
abbrev coordinateAbs (p q L : ℕ)
    (x : Space p q L) : Space p q L :=
  MetricCodes.Spherical.HigherHierarchyFinitePerron.coordinateAbs x

theorem johnsonWindowHarmonicDimension_pos
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (i : Index p q L) :
    0 < MetricCodes.booleanHarmonicDimension n (p + q + i.val) := by
  apply booleanHarmonicDimension_pos
  have hi := i.isLt
  have hfirst := h.first_le
  have hterminal := h.terminal_le_weight
  have hhalf := h.weight_half
  omega

/-- The johnson recurrence weight used in the Johnson-code argument. -/
def johnsonRecurrenceWeight
    (n _ p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ) *
    v i

/-- The johnson source channel coefficient used in the Johnson-code argument. -/
def johnsonSourceChannelCoefficient
    (n w p q L : ℕ) (m i : Index p q L) : ℝ :=
  matrix n w p q L m i *
    Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + m.val) : ℝ) /
      Real.sqrt (MetricCodes.booleanHarmonicDimension n (p + q + i.val) : ℝ)

theorem johnsonSourceChannelCoefficient_nonneg
    {n w p q L : ℕ} (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n) (m i : Index p q L) :
    0 ≤ johnsonSourceChannelCoefficient n w p q L m i := by
  unfold johnsonSourceChannelCoefficient
  exact div_nonneg
    (mul_nonneg (matrix_entry_nonneg h hstrict m i)
      (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- The johnson adjacent block coefficient used in the Johnson-code argument. -/
def johnsonAdjacentBlockCoefficient
    (n w p q L : ℕ) (v : Space p q L) (lam : ℝ)
    (target source : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonSourceChannelCoefficient n w p q L source target *
      johnsonRecurrenceWeight n w p q L v target /
        (lam * johnsonRecurrenceWeight n w p q L v source))

/-- The sum of the Johnson recurrence weights over the admissible index range. -/
def johnsonRecurrenceNormalization
    (n w p q L : ℕ) (v : Space p q L) : ℝ :=
  ∑ i : Index p q L, johnsonRecurrenceWeight n w p q L v i

/-- The johnson fibre amplitude used in the Johnson-code argument. -/
def johnsonFibreAmplitude
    (n w p q L : ℕ) (v : Space p q L) (i : Index p q L) : ℝ :=
  Real.sqrt
    (johnsonRecurrenceWeight n w p q L v i /
      johnsonRecurrenceNormalization n w p q L v)

/-- Data encoding the projection gram construction. -/
structure ProjectionGram (n w p q L : ℕ) where
  /-- The projections component. -/
  projections :
    MetricCodes.ProjectionFamily (JohnsonSphere n w)
      (MetricCodes.johnsonAmbientDimension n (p + q) L)
      (MetricCodes.johnsonFibreDimension n w p q)
  /-- The feature component. -/
  feature : JohnsonSphere n w →
    EuclideanSpace ℝ
      (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
        MetricCodes.johnsonAmbientDimension n (p + q) L))
  gram : ∀ x y : JohnsonSphere n w,
    ⟪feature x, feature y⟫_ℝ =
      (correlation x y - topEigenvalue n w p q L) *
        projections.overlap x y

/-- The centered eta used in the Johnson-code argument. -/
def centeredEta (α β γ : ℝ) : ℝ :=
  1 - 2 * α + 2 * β - 2 * γ

/-- The spectral limit used in the Johnson-code argument. -/
def spectralLimit (α β γ u : ℝ) : ℝ :=
  let z := (1 - 2 * u)
  let m := (1 - 2 * α)
  let σ := (1 - 2 * β - 2 * γ)
  let η := centeredEta α β γ
  (σ * η - m * z ^ 2) ^ 2 /
      (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
    ((z ^ 2 - η ^ 2) * (σ ^ 2 - z ^ 2)) /
      (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2))

theorem sqrt_one_sub_centeredDegree_sq {u : ℝ}
    (hu : 0 < u) (hhalf : u < (1 : ℝ) / 2) :
    Real.sqrt (1 - (1 - 2 * u) ^ 2) =
      2 * Real.sqrt (u * (1 - u)) := by
  have hvariance : 0 < u * (1 - u) :=
    mul_pos hu (by linarith)
  have hrad : 0 ≤ 1 - (1 - 2 * u) ^ 2 := by
    nlinarith
  have hsquare := Real.sq_sqrt hvariance.le
  apply (Real.sqrt_eq_iff_eq_sq hrad (by positivity)).mpr
  nlinarith

theorem zero_fibre_spectral_algebra
    (z m s : ℝ)
    (hz : z ≠ 0) (hm : 1 - m ^ 2 ≠ 0)
    (hs : s ≠ 0) (hplus : 1 + 2 * s ≠ 0)
    (hsquare : 4 * s ^ 2 = 1 - z ^ 2) :
    1 -
        ((m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s))) =
      (z ^ 2 - m ^ 2) /
        ((1 - m ^ 2) * (1 + 2 * s)) := by
  have hzsq : z ^ 2 = 1 - 4 * s ^ 2 := by
    nlinarith [hsquare]
  have hzsqne : 1 - 4 * s ^ 2 ≠ 0 := by
    rw [← hzsq]
    exact pow_ne_zero 2 hz
  have hplus' : 2 * s + 1 ≠ 0 := by
    simpa only [add_comm, ne_eq] using hplus
  have hplus'' : 1 + s * 2 ≠ 0 := by
    simpa only [ne_eq, mul_comm] using hplus
  have hfour : 4 * s ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hs)
  rw [hzsq]
  field_simp [hm, hs, hplus, hplus', hplus'', hfour, hzsqne]; ring

theorem spectralLimit_zero_fibre_boundary {α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2) :
    1 - spectralLimit α 0 0 u =
      (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  let z : ℝ := (1 - 2 * u)
  let m : ℝ := (1 - 2 * α)
  let s : ℝ := Real.sqrt (u * (1 - u))
  have ha0 : 0 < α := lt_trans hu hua
  have haone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvariance : 0 < u * (1 - u) := mul_pos hu huone
  have hz : z ≠ 0 := by
    dsimp [z]
    nlinarith
  have hm : 1 - m ^ 2 ≠ 0 := by
    have hprod : 0 < α * (1 - α) := mul_pos ha0 haone
    dsimp [m]
    nlinarith
  have hs : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_pos.mpr hvariance).ne'
  have hplus : 1 + 2 * s ≠ 0 := by
    have hsnonneg : 0 ≤ s := by
      dsimp [s]
      exact Real.sqrt_nonneg _
    nlinarith
  have hsquare : 4 * s ^ 2 = 1 - z ^ 2 := by
    have hsqrt := Real.sq_sqrt hvariance.le
    dsimp [s, z]
    nlinarith
  have hradical : Real.sqrt (1 - z ^ 2) = 2 * s := by
    simpa only using sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hsig : (1 - 2 * 0 - 2 * 0 : ℝ) = 1 := by
    norm_num
  have heta : centeredEta α 0 0 = (1 - 2 * α) := by
    simp only [centeredEta, mul_zero, add_zero, sub_zero]
  have hlimit :
      spectralLimit α 0 0 u =
        (m - m * z ^ 2) ^ 2 /
            (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
          ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
            (z ^ 2 * (1 - m ^ 2) * (2 * s)) := by
    change
      (((1 - 2 * 0 - 2 * 0) * centeredEta α 0 0 -
          (1 - 2 * α) * (1 - 2 * u) ^ 2) ^ 2 /
        ((1 - 2 * u) ^ 2 *
          (1 - (1 - 2 * α) ^ 2) *
          (1 - (1 - 2 * u) ^ 2)) +
        (((1 - 2 * u) ^ 2 - centeredEta α 0 0 ^ 2) *
          ((1 - 2 * 0 - 2 * 0) ^ 2 - (1 - 2 * u) ^ 2)) /
          ((1 - 2 * u) ^ 2 *
            (1 - (1 - 2 * α) ^ 2) *
            Real.sqrt (1 - (1 - 2 * u) ^ 2))) = _
    rw [hsig, heta]
    simp only [one_mul, one_pow]
    change
      (m - m * z ^ 2) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - m ^ 2) * (1 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) = _
    rw [hradical]
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos ha0 haone).ne'
  have hfourA : α * 4 - α ^ 2 * 4 ≠ 0 := by
    have hp : 0 < α * (1 - α) := mul_pos ha0 haone
    nlinarith
  have hmraw : 1 - (1 - 2 * α) ^ 2 ≠ 0 := by
    simpa [m] using hm
  have hplusraw :
      1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    simpa only [ne_eq] using hplus
  calc
    1 - spectralLimit α 0 0 u =
        (z ^ 2 - m ^ 2) /
          ((1 - m ^ 2) * (1 + 2 * s)) := by
      rw [hlimit]
      exact zero_fibre_spectral_algebra z m s hz hm hs hplus hsquare
    _ = (α * (1 - α) - u * (1 - u)) /
        (α * (1 - α) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
      dsimp [z, m, s]
      field_simp [hmraw, hA, hfourA, hplusraw]; ring

/-- The asymptotic threshold used in the Johnson-code argument. -/
def asymptoticThreshold (δ α : ℝ) : ℝ :=
  1 - δ / (2 * α * (1 - α))

/-- The rank penalty used in the Johnson-code argument. -/
def rankPenalty (α β γ : ℝ) : ℝ :=
  α * MetricCodes.binaryEntropy (β / α) +
    (1 - α) * MetricCodes.binaryEntropy (γ / (1 - α))

/-- The shell rate used in the Johnson-code argument. -/
def shellRate (α β γ u : ℝ) : ℝ :=
  1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u -
    rankPenalty α β γ

theorem binaryEntropy_eq_binEntropy_div_log (u : ℝ) :
    MetricCodes.binaryEntropy u = Real.binEntropy u / Real.log 2 := by
  simp only [MetricCodes.binaryEntropy, Real.logb, Real.binEntropy,
    Real.log_inv]
  ring

theorem binaryEntropy_le_one (u : ℝ) :
    MetricCodes.binaryEntropy u ≤ 1 := by
  rw [binaryEntropy_eq_binEntropy_div_log]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  simpa only [one_mul] using (Real.binEntropy_le_log_two (p := u))

/-- Data encoding the asymptotic parameters construction. -/
structure AsymptoticParameters (δ α β γ u : ℝ) : Prop where
  distance_pos : 0 < δ
  distance_lt_half : δ < (1 : ℝ) / 2
  weight_gt_distance : δ / 2 < α
  weight_lt_half : α < (1 : ℝ) / 2
  support_nonneg : 0 ≤ β
  support_lt_half : β < α / 2
  complement_nonneg : 0 ≤ γ
  complement_lt_half : γ < (1 - α) / 2
  first_lt_degree : β + γ < u
  degree_lt_weight : u < α
  degree_lt_left : u < α - β + γ
  degree_lt_right : u < 1 - α + β - γ

namespace AsymptoticParameters

variable {δ α β γ u : ℝ}

theorem weight_pos (h : AsymptoticParameters δ α β γ u) :
    0 < α := by
  nlinarith [h.distance_pos, h.weight_gt_distance]

theorem weight_complement_pos
    (h : AsymptoticParameters δ α β γ u) :
    0 < 1 - α := by
  nlinarith [h.weight_lt_half]

theorem degree_pos (h : AsymptoticParameters δ α β γ u) :
    0 < u := by
  nlinarith [h.support_nonneg, h.complement_nonneg,
    h.first_lt_degree]

theorem rankPenalty_le_one
    (h : AsymptoticParameters δ α β γ u) :
    rankPenalty α β γ ≤ 1 := by
  have hsupport := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (β / α)) h.weight_pos.le
  have hcomplement := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one (γ / (1 - α)))
    h.weight_complement_pos.le
  unfold rankPenalty
  nlinarith

theorem shellRate_lower
    (h : AsymptoticParameters δ α β γ u) :
    -1 ≤ shellRate α β γ u := by
  have hαentropy := binaryEntropy_le_one α
  have huone : u ≤ 1 := by
    nlinarith [h.degree_lt_weight, h.weight_lt_half]
  have huentropy := MetricCodes.binaryEntropy_nonneg h.degree_pos.le huone
  unfold shellRate
  nlinarith [h.rankPenalty_le_one]

end AsymptoticParameters

@[simp] theorem shellRate_zero_fibre (α u : ℝ) :
    shellRate α 0 0 u =
      1 - MetricCodes.binaryEntropy α + MetricCodes.binaryEntropy u := by
  simp only [shellRate, rankPenalty, zero_div, binaryEntropy_zero, mul_zero, add_zero, sub_zero]

/-- The predicate asserting spectrally feasible. -/
def IsSpectrallyFeasible (δ α β γ u : ℝ) : Prop :=
  asymptoticThreshold δ α < spectralLimit α β γ u

/-- The feasible used in the Johnson-code argument. -/
def Feasible (δ α β γ u : ℝ) : Prop :=
  AsymptoticParameters δ α β γ u ∧
    IsSpectrallyFeasible δ α β γ u

/-- The rate set used in the Johnson-code argument. -/
def rateSet (δ : ℝ) : Set ℝ :=
  {r | ∃ α β γ u : ℝ,
    Feasible δ α β γ u ∧ r = shellRate α β γ u}

theorem rateSet_bddBelow (δ : ℝ) :
    BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨α, β, γ, u, ⟨hparameter, _hspectral⟩, rfl⟩
  exact hparameter.shellRate_lower

/-- The variational rate used in the Johnson-code argument. -/
def variationalRate (δ : ℝ) : ℝ :=
  sInf (rateSet δ)

theorem variationalRate_le_of_feasible {δ α β γ u : ℝ}
    (h : Feasible δ α β γ u) :
    variationalRate δ ≤ shellRate α β γ u := by
  exact csInf_le (rateSet_bddBelow δ) ⟨α, β, γ, u, h, rfl⟩

/-- The mrrw g used in the Johnson-code argument. -/
def mrrwG (v : ℝ) : ℝ :=
  MetricCodes.binaryEntropy ((1 - Real.sqrt (1 - v)) / 2)

@[simp] theorem mrrwG_one : mrrwG 1 = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp only [mrrwG, sub_self, Real.sqrt_zero, sub_zero, one_div,
    binaryEntropy_eq_binEntropy_div_log, Real.binEntropy_two_inv, ne_eq, hlog, not_false_eq_true,
    div_self]

theorem mrrwG_continuous : Continuous mrrwG := by
  unfold mrrwG
  exact MetricCodes.Hamming.binaryEntropy_continuous.comp
    ((continuous_const.sub
      ((continuous_const.sub continuous_id).sqrt)).div_const 2)

theorem mrrwG_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ mrrwG v := by
  have hroot : Real.sqrt (1 - v) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith)
  have hroot' : 0 ≤ Real.sqrt (1 - v) :=
    Real.sqrt_nonneg _
  unfold mrrwG
  apply MetricCodes.binaryEntropy_nonneg
  · linarith
  · linarith

/-- The mrrw objective used in the Johnson-code argument. -/
def mrrwObjective (δ r : ℝ) : ℝ :=
  1 + mrrwG (r ^ 2) -
    mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)

theorem mrrwObjective_continuous (δ : ℝ) :
    Continuous (mrrwObjective δ) := by
  have hsquare : Continuous (fun r : ℝ => r ^ 2) :=
    continuous_id.pow 2
  have hargument :
      Continuous (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ) :=
    (hsquare.add (continuous_const.mul continuous_id)).add
      continuous_const
  unfold mrrwObjective
  exact (continuous_const.add (mrrwG_continuous.comp hsquare)).sub
    (mrrwG_continuous.comp hargument)

theorem mrrwObjective_endpoint {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwObjective δ (1 - 2 * δ) =
      MetricCodes.Hamming.classicalRate δ := by
  have hlast :
      (1 - 2 * δ) ^ 2 + 2 * δ * (1 - 2 * δ) + 2 * δ =
        (1 : ℝ) := by
    ring
  have hroot :
      Real.sqrt (1 - (1 - 2 * δ) ^ 2) =
        2 * Real.sqrt (δ * (1 - δ)) := by
    exact sqrt_one_sub_centeredDegree_sq hδ hhalf
  calc
    mrrwObjective δ (1 - 2 * δ) =
        mrrwG ((1 - 2 * δ) ^ 2) := by
      unfold mrrwObjective
      rw [hlast, mrrwG_one]
      ring
    _ = MetricCodes.Hamming.classicalRate δ := by
      unfold mrrwG MetricCodes.Hamming.classicalRate
        MetricCodes.Hamming.classicalParameter
      rw [hroot]
      congr 1; ring

theorem mrrwG_variance {u : ℝ}
    (hu : u ≤ (1 : ℝ) / 2) :
    mrrwG (4 * u * (1 - u)) = MetricCodes.binaryEntropy u := by
  have hrad :
      1 - 4 * u * (1 - u) = (1 - 2 * u) ^ 2 := by
    ring
  have hroot :
      Real.sqrt (1 - 4 * u * (1 - u)) = 1 - 2 * u := by
    rw [hrad, Real.sqrt_sq (by linarith)]
  unfold mrrwG
  rw [hroot]
  congr 1
  ring

theorem zero_fibre_boundary_variance {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    4 * α * (1 - α) =
      (2 * Real.sqrt (u * (1 - u))) ^ 2 +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ := by
  have hα : 0 < α := lt_trans hu hua
  have hαone : 0 < 1 - α := by linarith
  have huone : 0 < 1 - u := by linarith
  have hA : α * (1 - α) ≠ 0 :=
    (mul_pos hα hαone).ne'
  have hs : 0 ≤ Real.sqrt (u * (1 - u)) :=
    Real.sqrt_nonneg _
  have hplus : 1 + 2 * Real.sqrt (u * (1 - u)) ≠ 0 := by
    nlinarith
  have hrel :
      δ / (2 * α * (1 - α)) =
        (α * (1 - α) - u * (1 - u)) /
          (α * (1 - α) *
            (1 + 2 * Real.sqrt (u * (1 - u)))) := by
    calc
      δ / (2 * α * (1 - α)) =
          1 - spectralLimit α 0 0 u := by
        rw [hboundary]
        unfold asymptoticThreshold
        ring
      _ = _ := spectralLimit_zero_fibre_boundary hu hua ha
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  field_simp [hA, hα.ne', hαone.ne', hplus] at hrel
  nlinarith [hsquare]

theorem mrrwObjective_zero_fibre_boundary {δ α u : ℝ}
    (hu : 0 < u) (hua : u < α)
    (ha : α < (1 : ℝ) / 2)
    (hboundary :
      spectralLimit α 0 0 u = asymptoticThreshold δ α) :
    mrrwObjective δ (2 * Real.sqrt (u * (1 - u))) =
      shellRate α 0 0 u := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 =
        4 * u * (1 - u) := by
    nlinarith [hsquare]
  have hboundary' :=
    zero_fibre_boundary_variance hu hua ha hboundary
  have hargument :
      4 * u * (1 - u) +
        2 * δ * (2 * Real.sqrt (u * (1 - u))) + 2 * δ =
        4 * α * (1 - α) := by
    nlinarith [hboundary', hvariance]
  unfold mrrwObjective
  rw [hvariance, hargument,
    mrrwG_variance (by linarith : u ≤ (1 : ℝ) / 2),
    mrrwG_variance ha.le, shellRate_zero_fibre]
  ring

/-- The values of the MRRW objective as `r` ranges from zero to `1 - 2 * δ`. -/
def mrrwRateSet (δ : ℝ) : Set ℝ :=
  {t | ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
    t = mrrwObjective δ r}

theorem mrrwRateSet_bddBelow (δ : ℝ) :
    BddBelow (mrrwRateSet δ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, _hr, _hupper, rfl⟩
  have hfirst := mrrwG_nonneg (sq_nonneg r)
  have hsecond :
      mrrwG (r ^ 2 + 2 * δ * r + 2 * δ) ≤ 1 := by
    unfold mrrwG
    exact binaryEntropy_le_one _
  unfold mrrwObjective
  linarith

/-- The mrrw rate used in the Johnson-code argument. -/
def mrrwRate (δ : ℝ) : ℝ :=
  sInf (mrrwRateSet δ)

theorem mrrwRate_le_objective {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ) :
    mrrwRate δ ≤ mrrwObjective δ r := by
  exact csInf_le (mrrwRateSet_bddBelow δ)
    ⟨r, hr, hupper, rfl⟩

theorem exists_mrrw_minimizer {δ : ℝ}
    (hhalf : δ ≤ (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        mrrwObjective δ r ≤ mrrwObjective δ s := by
  have hnonempty : (Set.Icc 0 (1 - 2 * δ)).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · linarith
  obtain ⟨r, hr, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty
      (mrrwObjective_continuous δ).continuousOn
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro s hs hupper
  exact hmin ⟨hs, hupper⟩

theorem mrrwRate_eq_objective_of_minimizer {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      mrrwObjective δ r ≤ mrrwObjective δ s) :
    mrrwRate δ = mrrwObjective δ r := by
  apply le_antisymm
  · exact mrrwRate_le_objective hr hupper
  · unfold mrrwRate
    apply le_csInf
    · exact ⟨mrrwObjective δ r, r, hr, hupper, rfl⟩
    · rintro _ ⟨s, hs, hsupper, rfl⟩
      exact hmin s hs hsupper

theorem mrrwRate_le_classicalRate {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ ≤ MetricCodes.Hamming.classicalRate δ := by
  calc
    mrrwRate δ ≤ mrrwObjective δ (1 - 2 * δ) :=
      mrrwRate_le_objective (by linarith) (le_refl _)
    _ = MetricCodes.Hamming.classicalRate δ :=
      mrrwObjective_endpoint hδ hhalf

theorem mrrw_endpoint_dichotomy {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ < MetricCodes.Hamming.classicalRate δ ∨
      mrrwRate δ = MetricCodes.Hamming.classicalRate δ := by
  exact lt_or_eq_of_le (mrrwRate_le_classicalRate hδ hhalf)

/-- The combined variational rate used in the Johnson-code argument. -/
def combinedVariationalRate (δ : ℝ) : ℝ :=
  min (MetricCodes.Hamming.variationalRate δ) (variationalRate δ)

theorem combinedVariationalRate_le_hamming (δ : ℝ) :
    combinedVariationalRate δ ≤ MetricCodes.Hamming.variationalRate δ := by
  exact min_le_left _ _

theorem combinedVariationalRate_le_shell (δ : ℝ) :
    combinedVariationalRate δ ≤ variationalRate δ := by
  exact min_le_right _ _

theorem combinedVariationalRate_lt_mrrw_of_endpoint
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hendpoint : mrrwRate δ = MetricCodes.Hamming.classicalRate δ) :
    combinedVariationalRate δ < mrrwRate δ := by
  calc
    combinedVariationalRate δ ≤
        MetricCodes.Hamming.variationalRate δ :=
      combinedVariationalRate_le_hamming δ
    _ < MetricCodes.Hamming.classicalRate δ :=
      MetricCodes.Hamming.variationalRate_lt_classicalRate hδ hhalf
    _ = mrrwRate δ := hendpoint.symm

end

end Johnson

end MetricCodes

end MetricCodesNoncomputable
