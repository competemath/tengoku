import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.QBinomial
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Theta
import Tengoku.Seed.Algebra.BigOperators.Intervals
import Tengoku.Seed.Analysis.Normed.Group.Tannery

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian sharpness

This file proves the exact Gaussian product formula, counts the subspaces in
the elementary-abelian examples, and certifies the even-rank asymptotic with
the sharp Euler--theta constant.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators Topology
open Filter Finset Real

/-! ## Finite Euler products and the Gaussian product formula -/

@[simp] theorem gammaR_zero (p : ℝ) : gammaR p 0 = 1 := by
  simp [gammaR]

theorem gammaR_succ (p : ℝ) (r : ℕ) :
    gammaR p (r + 1) = gammaR p r * (1 - p⁻¹ ^ (r + 1)) := by
  simp [gammaR, Finset.prod_range_succ]

theorem gammaR_pos {p : ℝ} (hp : 1 < p) (r : ℕ) : 0 < gammaR p r := by
  rw [gammaR]
  apply Finset.prod_pos
  intro j hj
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  have hinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  exact sub_pos.mpr (pow_lt_one₀ (inv_pos.mpr hp0).le hinv (by omega))

theorem gammaR_le_one {p : ℝ} (hp : 1 < p) (r : ℕ) : gammaR p r ≤ 1 := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  rw [gammaR]
  apply Finset.prod_le_one
  · intro j hj
    exact (sub_pos.mpr <| pow_lt_one₀ (inv_pos.mpr hp0).le
      (inv_lt_one_of_one_lt₀ hp) (by omega)).le
  · intro j hj
    have : 0 ≤ p⁻¹ ^ (j + 1) := pow_nonneg (inv_pos.mpr hp0).le _
    linarith

/-- Finite Euler products decrease as more factors are included.-/
theorem gammaR_antitone {p : ℝ} (hp : 1 < p) : Antitone (gammaR p) := by
  apply antitone_nat_of_succ_le
  intro r
  rw [gammaR_succ]
  apply mul_le_of_le_one_right (gammaR_pos hp r).le
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  exact sub_le_self 1 (pow_nonneg (inv_pos.mpr hp0).le _)

/-- The exponent obtained by pulling the powers of `q` out of the first `r`
Euler factors.  Keeping it as a finite sum avoids parity bookkeeping.-/
def qWeight (r : ℕ) : ℕ := ∑ j ∈ Finset.range r, (j + 1)

@[simp] theorem qWeight_zero : qWeight 0 = 0 := by simp [qWeight]

theorem qWeight_succ (r : ℕ) : qWeight (r + 1) = qWeight r + (r + 1) := by
  simp [qWeight, Finset.sum_range_succ]

theorem qWeight_split : ∀ {n k : ℕ}, k ≤ n →
    qWeight n = qWeight k + qWeight (n - k) + k * (n - k) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          rw [qWeight_succ, qWeight_succ, Nat.succ_sub_succ_eq_sub, ih hkn]
          have hn : n + 1 = (k + 1) + (n - k) := by omega
          rw [hn]
          ring

private theorem cast_qpow_sub_one_factor {q m : ℕ} (hq : 1 ≤ q) :
    ((q ^ (m + 1) - 1 : ℕ) : ℝ) =
      (q : ℝ) ^ (m + 1) * (1 - (q : ℝ)⁻¹ ^ (m + 1)) := by
  have hpow : 1 ≤ q ^ (m + 1) := one_le_pow₀ hq
  rw [Nat.cast_sub hpow, Nat.cast_one, Nat.cast_pow]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [inv_pow]
  field_simp

/-- The finite Euler product is the normalized `q`-factorial.-/
theorem qFactorial_cast_real_eq_pow_mul_gammaR {q r : ℕ} (hq : 1 ≤ q) :
    (qFactorial q r : ℝ) = (q : ℝ) ^ qWeight r * gammaR (q : ℝ) r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [qFactorial_succ, Nat.cast_mul, ih, qWeight_succ, gammaR_succ,
        cast_qpow_sub_one_factor hq, pow_add]
      ring

/-- Gaussian product formula in terms of finite Euler products.-/
theorem qBinom_cast_real_eq_gammaR {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℝ) =
      (q : ℝ) ^ (k * (n - k)) * gammaR (q : ℝ) n /
        (gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k)) := by
  have hnat := qBinom_mul_qFactorials hq hk
  have hreal : (qBinom q n k : ℝ) * (qFactorial q k : ℝ) *
      (qFactorial q (n - k) : ℝ) = (qFactorial q n : ℝ) := by
    exact_mod_cast hnat
  rw [qFactorial_cast_real_eq_pow_mul_gammaR (by omega),
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega),
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega)] at hreal
  have hsplit := qWeight_split hk
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hpow : (q : ℝ) ^ qWeight n =
      ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
        (q : ℝ) ^ (k * (n - k)) := by
    rw [hsplit, pow_add, pow_add]
  have hden : gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k) ≠ 0 :=
    mul_ne_zero (ne_of_gt (gammaR_pos (by exact_mod_cast (by omega : 1 < q)) k))
      (ne_of_gt (gammaR_pos (by exact_mod_cast (by omega : 1 < q)) (n - k)))
  apply (eq_div_iff hden).2
  have hpowers : (q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)
  apply mul_left_cancel₀ hpowers
  calc
    ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
          ((qBinom q n k : ℝ) *
            (gammaR (q : ℝ) k * gammaR (q : ℝ) (n - k))) =
        (qBinom q n k : ℝ) *
          ((q : ℝ) ^ qWeight k * gammaR (q : ℝ) k) *
          ((q : ℝ) ^ qWeight (n - k) * gammaR (q : ℝ) (n - k)) := by ring
    _ = (q : ℝ) ^ qWeight n * gammaR (q : ℝ) n := hreal
    _ = ((q : ℝ) ^ qWeight k * (q : ℝ) ^ qWeight (n - k)) *
          ((q : ℝ) ^ (k * (n - k)) * gammaR (q : ℝ) n) := by
      rw [hpow]
      ring

/-! ### Ordered bases and relative generating tuples -/

private def frameWeight (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, j

@[simp] private theorem frameWeight_zero : frameWeight 0 = 0 := by
  simp [frameWeight]

private theorem frameWeight_succ (r : ℕ) :
    frameWeight (r + 1) = frameWeight r + r := by
  simp [frameWeight, Finset.sum_range_succ]

private theorem frameWeight_add_qWeight (r : ℕ) :
    frameWeight r + qWeight r = r * r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [frameWeight_succ, qWeight_succ]
      calc
        frameWeight r + r + (qWeight r + (r + 1)) =
            (frameWeight r + qWeight r) + (2 * r + 1) := by ring
        _ = r * r + (2 * r + 1) := by rw [ih]
        _ = (r + 1) * (r + 1) := by ring

private theorem framePower_cast_real {p r : ℕ} :
    (framePower p r : ℝ) = (p : ℝ) ^ frameWeight r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [framePower_succ, Nat.cast_mul, Nat.cast_pow, ih, frameWeight_succ, pow_add]

/-- The exact Euler-product form of the ordered-basis count.-/
theorem frameProd_diagonal_cast_real_eq_gammaR {p r : ℕ} (hp : 2 ≤ p) :
    (frameProd p r r : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  have hdiag := frameProd_mul_qFactorial (q := p) (n := r) (k := r) (le_refl r)
  simp only [Nat.sub_self, qFactorial_zero, mul_one] at hdiag
  have hreal : (frameProd p r r : ℝ) =
      (framePower p r : ℝ) * (qFactorial p r : ℝ) := by exact_mod_cast hdiag
  rw [hreal, framePower_cast_real,
    qFactorial_cast_real_eq_pow_mul_gammaR (by omega), ← mul_assoc,
    ← pow_add, frameWeight_add_qWeight]

/-- In `𝔽_p^r`, relative generating `r`-tuples are ordered bases; their
certified cardinal is `γ_{p,r} |𝔽_p^r|^r`.  The first equality is the
finite-vector-space realization used in the escape argument.-/
theorem card_orderedBases_fin_zmod_cast_eq_gammaR (p r : ℕ) [Fact p.Prime] :
    (Nat.card (LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  rw [card_orderedBases_fin_zmod]
  exact frameProd_diagonal_cast_real_eq_gammaR (Nat.Prime.two_le (Fact.out : p.Prime))

/-- An `r`-tuple in the standard `r`-dimensional elementary-abelian space
generates the whole space if and only if it is linearly independent.  This is
the literal ordered-basis bridge used by the escape example.-/
theorem span_eq_top_iff_linearIndependent_fin_zmod (p r : ℕ) [Fact p.Prime]
    (s : Fin r → (Fin r → ZMod p)) :
    Submodule.span (ZMod p) (Set.range s) = ⊤ ↔
      LinearIndependent (ZMod p) s := by
  constructor
  · intro hspan
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · rw [hspan]
    · simp
  · intro hs
    exact hs.span_eq_top_of_card_eq_finrank' (by simp)

/-- An additive subgroup of a `ZMod p`-module is automatically stable under
`ZMod p`-scalars.  This packages that elementary observation as a submodule.-/
private def addSubgroupAsZModSubmodule {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (A : AddSubgroup V) :
    Submodule (ZMod p) V where
  carrier := A
  zero_mem' := A.zero_mem
  add_mem' := A.add_mem
  smul_mem' c x hx := by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact A.nsmul_mem hx _

/-- For an elementary-abelian group, additive generation and vector-space
generation agree literally.-/
theorem span_toAddSubgroup_eq_addClosure_zmod {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (s : Set V) :
    (Submodule.span (ZMod p) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · have hspan : Submodule.span (ZMod p) s ≤
        addSubgroupAsZModSubmodule (AddSubgroup.closure s) :=
      Submodule.span_le.mpr AddSubgroup.subset_closure
    intro x hx
    exact hspan hx
  · rw [AddSubgroup.closure_le]
    intro x hx
    exact Submodule.subset_span hx

theorem addClosure_eq_top_iff_span_eq_top_zmod {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (s : Set V) :
    AddSubgroup.closure s = ⊤ ↔ Submodule.span (ZMod p) s = ⊤ := by
  rw [← span_toAddSubgroup_eq_addClosure_zmod (p := p) s]
  constructor
  · intro h
    apply Submodule.toAddSubgroup_injective
    simpa using h
  · intro h
    rw [h]
    rfl

/-- Literal group-generation form: an ordered `r`-tuple generates the
additive elementary-abelian group if and only if it is an ordered basis.-/
theorem addClosure_eq_top_iff_linearIndependent_fin_zmod
    (p r : ℕ) [Fact p.Prime] (s : Fin r → (Fin r → ZMod p)) :
    AddSubgroup.closure (Set.range s) = ⊤ ↔ LinearIndependent (ZMod p) s := by
  rw [addClosure_eq_top_iff_span_eq_top_zmod (p := p) (Set.range s),
    span_eq_top_iff_linearIndependent_fin_zmod p r s]

/-- Ordered generating `r`-tuples in the standard elementary-abelian
`r`-space.-/
abbrev GeneratingFramesFinZMod (p r : ℕ) :=
  {s : Fin r → (Fin r → ZMod p) //
    AddSubgroup.closure (Set.range s) = ⊤}

/-- A generating tuple is canonically the same datum as an ordered basis.-/
def generatingFramesEquivOrderedBasesFinZMod (p r : ℕ) [Fact p.Prime] :
    GeneratingFramesFinZMod p r ≃
      LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r :=
  Equiv.subtypeEquiv (Equiv.refl _) fun s ↦
    addClosure_eq_top_iff_linearIndependent_fin_zmod p r s

/-- Exact cardinality of the generating tuples in the elementary-abelian
escape family.-/
theorem card_generatingFrames_fin_zmod_cast_eq_gammaR (p r : ℕ) [Fact p.Prime] :
    (Nat.card (GeneratingFramesFinZMod p r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  rw [Nat.card_congr (generatingFramesEquivOrderedBasesFinZMod p r)]
  exact card_orderedBases_fin_zmod_cast_eq_gammaR p r

/-- The inverse finite Euler products converge to the Euler constant.-/
theorem gammaR_inv_tendsto {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun r : ℕ ↦ (gammaR p r)⁻¹) atTop (nhds (eulerC p)) := by
  simpa [gammaR, Finset.prod_inv_distrib] using eulerC_partial_tendsto hp

/-- The finite Euler products themselves converge to `C_p⁻¹`.-/
theorem gammaR_tendsto {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (gammaR p) atTop (nhds (eulerC p)⁻¹) := by
  have h := (gammaR_inv_tendsto hp).inv₀ (ne_of_gt (eulerC_pos hp))
  simpa using h

/-! ## Centered Gaussian summands -/

/-- The right-hand term at distance `j` from the middle Gaussian layer,
normalized by the central power.  It is set to zero outside the rank.-/
noncomputable def normalizedGaussianRight (p a j : ℕ) : ℝ :=
  if j ≤ a then (p : ℝ)⁻¹ ^ (a * a) * (qBinom p (2 * a) (a + j) : ℝ) else 0

theorem normalizedGaussianRight_eq {p a j : ℕ} (hp : 2 ≤ p) (hj : j ≤ a) :
    normalizedGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ * (gammaR (p : ℝ) (a - j))⁻¹ := by
  rw [normalizedGaussianRight, ite_eq_left hj,
    qBinom_cast_real_eq_gammaR hp (by omega : a + j ≤ 2 * a)]
  have hsub : 2 * a - (a + j) = a - j := by omega
  rw [hsub]
  have hexp : a * a = j * j + (a + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hscale : (p : ℝ)⁻¹ ^ (a * a) *
      (p : ℝ) ^ ((a + j) * (a - j)) = (p : ℝ)⁻¹ ^ (j * j) := by
    rw [hexp, pow_add]
    simp [inv_pow, hp0]
  rw [div_eq_mul_inv, mul_inv]
  calc
    (p : ℝ)⁻¹ ^ (a * a) *
          ((p : ℝ) ^ ((a + j) * (a - j)) * gammaR (p : ℝ) (2 * a) *
            ((gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹)) =
        ((p : ℝ)⁻¹ ^ (a * a) *
          (p : ℝ) ^ ((a + j) * (a - j))) * gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by ring
    _ = (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by rw [hscale]

private theorem tendsto_double_nat_atTop :
    Tendsto (fun a : ℕ ↦ 2 * a) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  omega

theorem normalizedGaussianRight_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ normalizedGaussianRight p a j) atTop
      (nhds (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have htwo := (gammaR_tendsto hpR).comp tendsto_double_nat_atTop
  have hplus := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat j)
  have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
  have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * j))) := tendsto_const_nhds
  have hprod := ((hc.mul htwo).mul hplus).mul hminus
  have hC0 : eulerC (p : ℝ) ≠ 0 := ne_of_gt (eulerC_pos hpR)
  convert hprod.congr' ?_ using 1
  · field_simp
  · filter_upwards [eventually_ge_atTop j] with a ha
    rw [normalizedGaussianRight_eq hp ha]
    simp only [Function.comp_apply, Nat.add_comm, Nat.mul_comm]

theorem normalizedGaussianRight_nonneg {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ normalizedGaussianRight p a j := by
  unfold normalizedGaussianRight
  split_ifs
  · positivity
  · exact le_rfl

theorem normalizedGaussianRight_le {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedGaussianRight p a j ≤
      eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by
  by_cases hj : j ≤ a
  · rw [normalizedGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := pow_nonneg (inv_nonneg.mpr (by linarith)) _
    have hgam : 0 ≤ gammaR (p : ℝ) (2 * a) := (gammaR_pos hp1 _).le
    have hplus : 0 ≤ (gammaR (p : ℝ) (a + j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹ * (gammaR (p : ℝ) (a - j))⁻¹ ≤
          (p : ℝ)⁻¹ ^ (j * j) * 1 *
            (gammaR (p : ℝ) (a + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (gammaR_le_one hp1 _) hpow) hplus)
          hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) *
            (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
            (mul_nonneg hpow zero_le_one)) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) *
            eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg (mul_nonneg hpow zero_le_one) (eulerC_pos hpR).le)
      _ = eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by ring
  · rw [normalizedGaussianRight, ite_eq_right hj]
    positivity

/-- The sharp one-sided Gaussian majorant used in the manuscript.  One
inverse Euler factor cancels against the longer numerator product, leaving
only a single factor `C_p`.-/
theorem normalizedGaussianRight_le_eulerC {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedGaussianRight p a j ≤
      eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by
  by_cases hj : j ≤ a
  · rw [normalizedGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := by positivity
    have hpluspos : 0 < gammaR (p : ℝ) (a + j) := gammaR_pos hp1 _
    have hratio_nonneg : 0 ≤ gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ :=
      mul_nonneg (gammaR_pos hp1 _).le (inv_pos.mpr hpluspos).le
    have hratio : gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact (div_le_one hpluspos).2 (gammaR_antitone hp1 (by omega))
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * j) * gammaR (p : ℝ) (2 * a) *
          (gammaR (p : ℝ) (a + j))⁻¹ *
            (gammaR (p : ℝ) (a - j))⁻¹ =
        (p : ℝ)⁻¹ ^ (j * j) *
          (gammaR (p : ℝ) (2 * a) *
            (gammaR (p : ℝ) (a + j))⁻¹) *
              (gammaR (p : ℝ) (a - j))⁻¹ := by ring
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 *
            (gammaR (p : ℝ) (a - j))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio hpow) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * j) * 1 * eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg hpow zero_le_one)
      _ = eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by ring
  · rw [normalizedGaussianRight, ite_eq_right hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    exact mul_nonneg (eulerC_pos hpR).le (by positivity)

/-- Symmetric integer indexing of the centered Gaussian layers.-/
noncomputable def normalizedGaussianCentered (p a : ℕ) (j : ℤ) : ℝ :=
  normalizedGaussianRight p a j.natAbs

theorem normalizedGaussianCentered_eq {p a : ℕ} {j : ℤ} (hp : 2 ≤ p)
    (hj : j.natAbs ≤ a) :
    normalizedGaussianCentered p a j =
      (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs) * gammaR (p : ℝ) (2 * a) *
        (gammaR (p : ℝ) (a + j.natAbs))⁻¹ *
          (gammaR (p : ℝ) (a - j.natAbs))⁻¹ := by
  exact normalizedGaussianRight_eq hp hj

theorem normalizedGaussianCentered_tendsto {p : ℕ} {j : ℤ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ normalizedGaussianCentered p a j) atTop
      (nhds (eulerC (p : ℝ) *
        (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs))) := by
  exact normalizedGaussianRight_tendsto hp

theorem normalizedGaussianCentered_le_eulerC {p a : ℕ} {j : ℤ}
    (hp : 2 ≤ p) :
    normalizedGaussianCentered p a j ≤
      eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j.natAbs * j.natAbs) := by
  exact normalizedGaussianRight_le_eulerC hp

/-- Multiplicity of the central layer (`1`) and of a noncentral symmetric
pair (`2`).-/
def centerMultiplicity (j : ℕ) : ℕ := if j = 0 then 1 else 2

noncomputable def evenGaussianSummand (p a j : ℕ) : ℝ :=
  (centerMultiplicity j : ℝ) * normalizedGaussianRight p a j

noncomputable def evenGaussianLimitSummand (p j : ℕ) : ℝ :=
  (centerMultiplicity j : ℝ) *
    (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))

theorem evenGaussianSummand_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ evenGaussianSummand p a j) atTop
      (nhds (evenGaussianLimitSummand p j)) := by
  exact tendsto_const_nhds.mul (normalizedGaussianRight_tendsto hp)

theorem summable_nat_gaussian_inv_pow {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) := by
  have hpR0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpR1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  have hgeom : Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ j) :=
    summable_geometric_of_lt_one hpR0 hpR1
  exact hgeom.of_nonneg_of_le (fun j ↦ pow_nonneg hpR0 _)
    (fun j ↦ pow_le_pow_of_le_one hpR0 hpR1.le (Nat.le_mul_self j))

private theorem exp_neg_log_sq_nat_eq_inv_pow {p j : ℕ} (hp : 1 ≤ p) :
    Real.exp (-Real.log (p : ℝ) * (j : ℝ) ^ 2) =
      (p : ℝ)⁻¹ ^ (j * j) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -Real.log (p : ℝ) * (j : ℝ) ^ 2 =
      (j * j : ℕ) * (-Real.log (p : ℝ)) by norm_num; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpR]

theorem tsum_evenGaussianSummand_eq_normalized_total {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenGaussianSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · rw [Finset.sum_range_succ']
    have htail : (∑ j ∈ Finset.range a, evenGaussianSummand p a (j + 1)) =
        2 * ((p : ℝ)⁻¹ ^ (a * a) *
          ∑ j ∈ Finset.range a, (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
      calc
        (∑ j ∈ Finset.range a, evenGaussianSummand p a (j + 1)) =
            ∑ j ∈ Finset.range a, 2 *
              ((p : ℝ)⁻¹ ^ (a * a) *
                (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < a := Finset.mem_range.mp hj
          have hja : j + 1 ≤ a := by omega
          simp [evenGaussianSummand, centerMultiplicity, normalizedGaussianRight, hja]
        _ = 2 * ((p : ℝ)⁻¹ ^ (a * a) *
              ∑ j ∈ Finset.range a, (qBinom p (2 * a) (a + (j + 1)) : ℝ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
    rw [htail]
    simp [evenGaussianSummand, centerMultiplicity, normalizedGaussianRight]
    rw [totalQBinom_even_split hp]
    push_cast
    ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [evenGaussianSummand, normalizedGaussianRight, show ¬j ≤ a by omega]

theorem tsum_evenGaussianLimitSummand_eq_sharpConstant {p : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenGaussianLimitSummand p j = sharpConstant (p : ℝ) := by
  have hsum : Summable (fun j : ℕ ↦ evenGaussianLimitSummand p j) := by
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    refine ((summable_nat_gaussian_inv_pow hp).mul_left
      (2 * eulerC (p : ℝ))).of_nonneg_of_le ?_ ?_
    · intro j
      unfold evenGaussianLimitSummand centerMultiplicity
      split_ifs <;> positivity [eulerC_pos hpR]
    · intro j
      have hx : 0 ≤ eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) :=
        mul_nonneg (eulerC_pos hpR).le (by positivity)
      unfold evenGaussianLimitSummand centerMultiplicity
      by_cases hj : j = 0
      · simp only [ite_eq_left hj, Nat.cast_one, one_mul]
        linarith
      · rw [ite_eq_right hj]
        change (2 : ℝ) * (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)) ≤
            2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)
        ring_nf
        exact le_rfl
  rw [hsum.tsum_eq_zero_add]
  have htheta : gaussianTheta (p : ℝ) =
      1 + 2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) := by
    rw [gaussianTheta_eq_one_add_two_mul_tsum_pnat
      (by exact_mod_cast (by omega : 1 < p)),
      tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ ↦ Real.exp (-Real.log (p : ℝ) * (n : ℝ) ^ 2))]
    congr 2
    apply tsum_congr
    intro j
    simpa using exp_neg_log_sq_nat_eq_inv_pow (p := p) (j := j + 1) (by omega)
  rw [sharpConstant, htheta]
  simp only [evenGaussianLimitSummand, centerMultiplicity, ite_eq_left, Nat.cast_one,
    one_mul, ite_eq_right (Nat.succ_ne_zero _), Nat.cast_ofNat]
  rw [tsum_mul_left, tsum_mul_left]
  simp
  ring

/-- Full-constant asymptotic for the number of subspaces in even rank.-/
theorem gaussian_even_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  rw [← tsum_evenGaussianLimitSummand_eq_sharpConstant hp]
  have hbound : Summable (fun j : ℕ ↦
      2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j)) :=
    (summable_nat_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, evenGaussianSummand p a j) atTop
      (nhds (∑' j : ℕ, evenGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence
      (f := fun a j ↦ evenGaussianSummand p a j)
      (g := fun j ↦ evenGaussianLimitSummand p j)
      (bound := fun j ↦ 2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j))
      hbound (fun j ↦ evenGaussianSummand_tendsto hp)
      (Filter.Eventually.of_forall fun a j ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · calc
            evenGaussianSummand p a j ≤
                2 * normalizedGaussianRight p a j := by
              have hn := normalizedGaussianRight_nonneg (p := p) (a := a) (j := j) hp
              unfold evenGaussianSummand centerMultiplicity
              by_cases hj : j = 0
              · simp only [ite_eq_left hj, Nat.cast_one, one_mul]
                linarith
              · rw [ite_eq_right hj]
                change (2 : ℝ) * normalizedGaussianRight p a j ≤
                    2 * normalizedGaussianRight p a j
                exact le_rfl
            _ ≤ 2 * (eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j)) := by
              gcongr
              exact normalizedGaussianRight_le hp
            _ = 2 * eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * j) := by ring
        · exact mul_nonneg (by positivity) (normalizedGaussianRight_nonneg hp))
  exact ht.congr' (Filter.Eventually.of_forall fun a ↦
    tsum_evenGaussianSummand_eq_normalized_total hp)

/-! ## Odd-rank Gaussian asymptotics -/

/-- The extra quarter-power which changes the integral normalization
`p^(-a(a+1))` in rank `2a+1` into the canonical normalization
`p^(-(2a+1)^2/4)`.-/
noncomputable def quarterShiftScale (p : ℝ) : ℝ :=
  Real.exp (-Real.log p / 4)

/-- The half-shifted sharp constant governing odd ranks.-/
noncomputable def oddGaussianConstant (p : ℝ) : ℝ :=
  eulerC p * shiftedTheta p (1 / 2)

/-- The right-hand odd-rank layer at distance `j` from the middle pair,
normalized by `p^(a(a+1))`.-/
noncomputable def normalizedOddGaussianRight (p a j : ℕ) : ℝ :=
  if j ≤ a then
    (p : ℝ)⁻¹ ^ (a * (a + 1)) *
      (qBinom p (2 * a + 1) (a + 1 + j) : ℝ)
  else 0

theorem normalizedOddGaussianRight_eq {p a j : ℕ} (hp : 2 ≤ p) (hj : j ≤ a) :
    normalizedOddGaussianRight p a j =
      (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
        (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by
  rw [normalizedOddGaussianRight, ite_eq_left hj,
    qBinom_cast_real_eq_gammaR hp (by omega : a + 1 + j ≤ 2 * a + 1)]
  have hsub : 2 * a + 1 - (a + 1 + j) = a - j := by omega
  rw [hsub]
  have hexp : a * (a + 1) = j * (j + 1) + (a + 1 + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hscale : (p : ℝ)⁻¹ ^ (a * (a + 1)) *
      (p : ℝ) ^ ((a + 1 + j) * (a - j)) =
        (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    rw [hexp, pow_add]
    simp [inv_pow, hp0]
  rw [div_eq_mul_inv, mul_inv]
  calc
    (p : ℝ)⁻¹ ^ (a * (a + 1)) *
          ((p : ℝ) ^ ((a + 1 + j) * (a - j)) *
            gammaR (p : ℝ) (2 * a + 1) *
              ((gammaR (p : ℝ) (a + 1 + j))⁻¹ *
                (gammaR (p : ℝ) (a - j))⁻¹)) =
        ((p : ℝ)⁻¹ ^ (a * (a + 1)) *
          (p : ℝ) ^ ((a + 1 + j) * (a - j))) *
            gammaR (p : ℝ) (2 * a + 1) *
              (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
                (gammaR (p : ℝ) (a - j))⁻¹ := by ring
    _ = (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
        (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
          (gammaR (p : ℝ) (a - j))⁻¹ := by rw [hscale]

private theorem tendsto_double_add_one_nat_atTop :
    Tendsto (fun a : ℕ ↦ 2 * a + 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  omega

theorem normalizedOddGaussianRight_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ normalizedOddGaussianRight p a j) atTop
      (nhds (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have htwo := (gammaR_tendsto hpR).comp tendsto_double_add_one_nat_atTop
  have hplus₀ := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat (1 + j))
  have hplus : Tendsto (fun a : ℕ ↦ (gammaR (p : ℝ) (a + 1 + j))⁻¹)
      atTop (nhds (eulerC (p : ℝ))) := by
    change Tendsto (fun a : ℕ ↦ (gammaR (p : ℝ) (a + (1 + j)))⁻¹)
      atTop (nhds (eulerC (p : ℝ))) at hplus₀
    simpa only [Nat.add_assoc] using hplus₀
  have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
  have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * (j + 1))) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * (j + 1)))) := tendsto_const_nhds
  have hprod := ((hc.mul htwo).mul hplus).mul hminus
  have htend : Tendsto (fun a : ℕ ↦ normalizedOddGaussianRight p a j) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * (j + 1)) * (eulerC (p : ℝ))⁻¹ *
        eulerC (p : ℝ) * eulerC (p : ℝ))) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop j] with a ha
    rw [normalizedOddGaussianRight_eq hp ha]
    simp only [Function.comp_apply]
  have hC0 : eulerC (p : ℝ) ≠ 0 := ne_of_gt (eulerC_pos hpR)
  convert htend using 1
  field_simp

theorem normalizedOddGaussianRight_nonneg {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ normalizedOddGaussianRight p a j := by
  unfold normalizedOddGaussianRight
  split_ifs
  · positivity
  · exact le_rfl

theorem normalizedOddGaussianRight_le {p a j : ℕ} (hp : 2 ≤ p) :
    normalizedOddGaussianRight p a j ≤
      eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
  by_cases hj : j ≤ a
  · rw [normalizedOddGaussianRight_eq hp hj]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
    have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) :=
      pow_nonneg (inv_nonneg.mpr (by linarith)) _
    have hgam : 0 ≤ gammaR (p : ℝ) (2 * a + 1) := (gammaR_pos hp1 _).le
    have hplus : 0 ≤ (gammaR (p : ℝ) (a + 1 + j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    have hminus : 0 ≤ (gammaR (p : ℝ) (a - j))⁻¹ :=
      (inv_pos.mpr (gammaR_pos hp1 _)).le
    calc
      (p : ℝ)⁻¹ ^ (j * (j + 1)) * gammaR (p : ℝ) (2 * a + 1) *
            (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ ≤
          (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 *
            (gammaR (p : ℝ) (a + 1 + j))⁻¹ *
              (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (gammaR_le_one hp1 _) hpow) hplus) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 * eulerC (p : ℝ) *
            (gammaR (p : ℝ) (a - j))⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
            (mul_nonneg hpow zero_le_one)) hminus
      _ ≤ (p : ℝ)⁻¹ ^ (j * (j + 1)) * 1 * eulerC (p : ℝ) *
            eulerC (p : ℝ) := by
        exact mul_le_mul_of_nonneg_left (gammaR_inv_lt_eulerC hpR _).le
          (mul_nonneg (mul_nonneg hpow zero_le_one) (eulerC_pos hpR).le)
      _ = eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by ring
  · rw [normalizedOddGaussianRight, ite_eq_right hj]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (inv_nonneg.mpr (by positivity)) _)

/-- The two members of the middle pair and all subsequent symmetric pairs.-/
noncomputable def oddGaussianSummand (p a j : ℕ) : ℝ :=
  2 * quarterShiftScale (p : ℝ) * normalizedOddGaussianRight p a j

noncomputable def oddGaussianLimitSummand (p j : ℕ) : ℝ :=
  2 * quarterShiftScale (p : ℝ) *
    (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))

theorem oddGaussianSummand_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ oddGaussianSummand p a j) atTop
      (nhds (oddGaussianLimitSummand p j)) := by
  exact tendsto_const_nhds.mul (normalizedOddGaussianRight_tendsto hp)

theorem summable_nat_odd_gaussian_inv_pow {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ (j * (j + 1))) := by
  have hpR0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpR1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  have hgeom : Summable (fun j : ℕ ↦ (p : ℝ)⁻¹ ^ j) :=
    summable_geometric_of_lt_one hpR0 hpR1
  exact hgeom.of_nonneg_of_le (fun j ↦ pow_nonneg hpR0 _)
    (fun j ↦ pow_le_pow_of_le_one hpR0 hpR1.le (by
      calc
        j = j * 1 := by simp
        _ ≤ j * (j + 1) :=
          Nat.mul_le_mul_left j (Nat.succ_le_succ (Nat.zero_le j))))

/-- Odd rank has no single central layer: the lower and upper halves pair
exactly.-/
theorem totalQBinom_odd_split {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    totalQBinom q (2 * a + 1) =
      2 * ∑ j ∈ Finset.range (a + 1), qBinom q (2 * a + 1) (a + 1 + j) := by
  let f : ℕ → ℕ := fun k ↦ qBinom q (2 * a + 1) k
  have hlow : (∑ j ∈ Finset.range (a + 1), f j) =
      ∑ j ∈ Finset.range (a + 1), f (a + 1 + j) := by
    calc
      (∑ j ∈ Finset.range (a + 1), f j) =
          ∑ j ∈ Finset.range (a + 1), f (a + 1 - 1 - j) :=
        (Finset.sum_range_reflect f (a + 1)).symm
      _ = ∑ j ∈ Finset.range (a + 1), f (a + 1 + j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hja : j < a + 1 := Finset.mem_range.mp hj
        dsimp [f]
        rw [qBinom_symm hq (by omega : a - j ≤ 2 * a + 1)]
        congr 1
        omega
  rw [totalQBinom, Fin.sum_univ_eq_sum_range]
  have hsize : 2 * a + 1 + 1 = (a + 1) + (a + 1) := by omega
  rw [hsize, Finset.sum_range_add, hlow]
  dsimp [f]
  ring

theorem tsum_oddGaussianSummand_eq_normalized_total {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, oddGaussianSummand p a j =
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · calc
      (∑ j ∈ Finset.range (a + 1), oddGaussianSummand p a j) =
          ∑ j ∈ Finset.range (a + 1),
            2 * quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
              (qBinom p (2 * a + 1) (a + 1 + j) : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < a + 1 := Finset.mem_range.mp hj
        have hja : j ≤ a := by omega
        simp [oddGaussianSummand, normalizedOddGaussianRight, hja]
        ring
      _ = 2 * quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
            ∑ j ∈ Finset.range (a + 1),
              (qBinom p (2 * a + 1) (a + 1 + j) : ℝ) := by
        rw [Finset.mul_sum]
      _ = quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
            (totalQBinom p (2 * a + 1) : ℝ) := by
        rw [totalQBinom_odd_split hp]
        push_cast
        ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [oddGaussianSummand, normalizedOddGaussianRight, show ¬j ≤ a by omega]

private theorem exp_neg_log_nat_eq_inv_pow {p m : ℕ} (hp : 1 ≤ p) :
    Real.exp (-Real.log (p : ℝ) * (m : ℝ)) = (p : ℝ)⁻¹ ^ m := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show -Real.log (p : ℝ) * (m : ℝ) =
      (m : ℕ) * (-Real.log (p : ℝ)) by norm_num; ring]
  rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpR]

/-- The half-shifted theta series is exactly the paired odd Gaussian series,
including the quarter-power normalization.-/
theorem shiftedTheta_half_eq_quarterShiftScale_mul_tsum {p : ℕ} (hp : 2 ≤ p) :
    shiftedTheta (p : ℝ) (1 / 2) = quarterShiftScale (p : ℝ) *
      (2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1))) := by
  let F : ℤ → ℝ := fun z ↦
    Real.exp (-Real.log (p : ℝ) * ((z : ℝ) - (1 / 2 : ℝ)) ^ 2)
  let e : ℤ ≃ ℕ ⊕ ℕ := (Equiv.neg ℤ).trans Equiv.intEquivNatSumNat
  have hF : Summable F := by
    simpa only [F] using shiftedTheta_summable
      (p := (p : ℝ)) (x := (1 / 2 : ℝ)) (by exact_mod_cast (by omega : 1 < p))
  have hleft : Summable (fun j : ℕ ↦ F (e.symm (Sum.inl j))) := by
    change Summable (F ∘ (fun j : ℕ ↦ e.symm (Sum.inl j)))
    exact hF.comp_injective (e.symm.injective.comp Sum.inl_injective)
  have hright : Summable (fun j : ℕ ↦ F (e.symm (Sum.inr j))) := by
    change Summable (F ∘ (fun j : ℕ ↦ e.symm (Sum.inr j)))
    exact hF.comp_injective (e.symm.injective.comp Sum.inr_injective)
  have hsplit :
      (∑' s : ℕ ⊕ ℕ, F (e.symm s)) =
        (∑' j : ℕ, F (e.symm (Sum.inl j))) +
          ∑' j : ℕ, F (e.symm (Sum.inr j)) :=
    (hleft.hasSum.sum hright.hasSum).tsum_eq
  have hleftterm (j : ℕ) :
      F (e.symm (Sum.inl j)) =
        quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    have he : e.symm (Sum.inl j) = -(j : ℤ) := rfl
    rw [he]
    dsimp only [F]
    rw [Int.cast_neg, Int.cast_natCast]
    rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := j * (j + 1)) (by omega)]
    rw [quarterShiftScale, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have hrightterm (j : ℕ) :
      F (e.symm (Sum.inr j)) =
        quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
    have he : e.symm (Sum.inr j) = ((j + 1 : ℕ) : ℤ) := rfl
    rw [he]
    dsimp only [F]
    rw [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := j * (j + 1)) (by omega)]
    rw [quarterShiftScale, ← Real.exp_add]
    congr 1
    norm_num
    ring
  unfold shiftedTheta
  change (∑' z : ℤ, F z) = _
  rw [← e.symm.tsum_eq F, hsplit]
  simp_rw [hleftterm, hrightterm]
  rw [tsum_mul_left]
  ring

theorem tsum_oddGaussianLimitSummand_eq_oddGaussianConstant {p : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, oddGaussianLimitSummand p j = oddGaussianConstant (p : ℝ) := by
  have htheta := shiftedTheta_half_eq_quarterShiftScale_mul_tsum hp
  unfold oddGaussianLimitSummand oddGaussianConstant
  calc
    (∑' j : ℕ, 2 * quarterShiftScale (p : ℝ) *
        (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))) =
        (2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ)) *
          ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      ring
    _ = eulerC (p : ℝ) *
        (quarterShiftScale (p : ℝ) *
          (2 * ∑' j : ℕ, (p : ℝ)⁻¹ ^ (j * (j + 1)))) := by ring
    _ = eulerC (p : ℝ) * shiftedTheta (p : ℝ) (1 / 2) := by rw [htheta]

theorem oddGaussianSummand_nonneg {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ oddGaussianSummand p a j := by
  have hscale : 0 ≤ quarterShiftScale (p : ℝ) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg (by norm_num) hscale)
    (normalizedOddGaussianRight_nonneg hp)

theorem oddGaussianSummand_le {p a j : ℕ} (hp : 2 ≤ p) :
    oddGaussianSummand p a j ≤
      2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
        (p : ℝ)⁻¹ ^ (j * (j + 1)) := by
  unfold oddGaussianSummand
  have hs : 0 ≤ 2 * quarterShiftScale (p : ℝ) :=
    mul_nonneg (by norm_num) (Real.exp_pos _).le
  calc
    2 * quarterShiftScale (p : ℝ) * normalizedOddGaussianRight p a j ≤
        2 * quarterShiftScale (p : ℝ) *
          (eulerC (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ (j * (j + 1))) :=
      mul_le_mul_of_nonneg_left (normalizedOddGaussianRight_le hp) hs
    _ = 2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
          (p : ℝ)⁻¹ ^ (j * (j + 1)) := by ring

/-- Full half-shifted-theta asymptotic in odd rank.-/
theorem gaussian_odd_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by
  rw [← tsum_oddGaussianLimitSummand_eq_oddGaussianConstant hp]
  have hbound : Summable (fun j : ℕ ↦
      2 * quarterShiftScale (p : ℝ) * eulerC (p : ℝ) ^ 2 *
        (p : ℝ)⁻¹ ^ (j * (j + 1))) :=
    (summable_nat_odd_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, oddGaussianSummand p a j)
      atTop (nhds (∑' j : ℕ, oddGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence hbound
      (fun j : ℕ ↦ oddGaussianSummand_tendsto hp)
      (Filter.Eventually.of_forall fun (a j : ℕ) ↦ ?_)
  · convert ht using 1
    funext a
    exact (tsum_oddGaussianSummand_eq_normalized_total (a := a) hp).symm
  · rw [Real.norm_eq_abs, abs_of_nonneg (oddGaussianSummand_nonneg hp)]
    exact oddGaussianSummand_le hp

theorem quarterShiftScale_mul_centered_power {p a : ℕ} (hp : 2 ≤ p) :
    quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) =
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  change quarterShiftScale (p : ℝ) * (p : ℝ)⁻¹ ^ (a * (a + 1)) =
    (p : ℝ) ^ (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4))
  rw [Real.rpow_def_of_pos hpR]
  rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := a * (a + 1)) (by omega),
    quarterShiftScale, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Equivalent quarter-square form of the odd-rank asymptotic.-/
theorem gaussian_odd_rank_rpow_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      Real.rpow (p : ℝ) (-(((2 * a + 1 : ℕ) : ℝ) ^ 2 / 4)) *
        (totalQBinom p (2 * a + 1) : ℝ)) atTop
      (nhds (oddGaussianConstant (p : ℝ))) := by
  apply (gaussian_odd_rank_asymptotic hp).congr'
  filter_upwards with a
  rw [quarterShiftScale_mul_centered_power hp]

/-- The half-integral translate is strictly below the integral theta maximum,
so the odd-rank constant is strictly smaller than the even-rank sharp
constant under the canonical quarter-square normalization.-/
theorem oddGaussianConstant_lt_sharpConstant {p : ℝ} (hp : 2 ≤ p) :
    oddGaussianConstant p < sharpConstant p := by
  have hhalf : ¬ ∃ z : ℤ, (z : ℝ) = (1 / 2 : ℝ) := by
    rintro ⟨z, hz⟩
    have hz' : (2 : ℝ) * (z : ℝ) = 1 := by rw [hz]; norm_num
    have hzInt : (2 : ℤ) * z = 1 := by exact_mod_cast hz'
    omega
  have htheta := shiftedTheta_lt_of_not_integer (p := p) (x := (1 / 2 : ℝ))
    (by linarith) hhalf
  simpa [oddGaussianConstant, sharpConstant] using
    mul_lt_mul_of_pos_left htheta (eulerC_pos hp)

/-! ## The finite prime-power envelope -/

/-- The manuscript's finite sum `U_p(p^n)`, in an exact real form.-/
noncomputable def primePowerU (p n : ℕ) : ℝ :=
  ∑ r : Fin (n + 1),
    (p : ℝ) ^ (r.val * (n - r.val)) * (gammaR (p : ℝ) r.val)⁻¹

private theorem centered_power_normalization {p a j : ℕ} (hp : 1 ≤ p) (hj : j ≤ a) :
    (p : ℝ)⁻¹ ^ (a * a) * (p : ℝ) ^ ((a + j) * (a - j)) =
      (p : ℝ)⁻¹ ^ (j * j) := by
  have hexp : a * a = j * j + (a + j) * (a - j) := by
    have := Nat.sub_add_cancel hj
    nlinarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [hexp, pow_add]
  simp [inv_pow, hp0]

/-- The paired centered summands in the even-rank `U` sum.-/
noncomputable def evenUSummand (p a j : ℕ) : ℝ :=
  if j = 0 then (gammaR (p : ℝ) a)⁻¹
  else if j ≤ a then
    (p : ℝ)⁻¹ ^ (j * j) *
      ((gammaR (p : ℝ) (a + j))⁻¹ + (gammaR (p : ℝ) (a - j))⁻¹)
  else 0

theorem tsum_evenUSummand_eq_normalized_U {p a : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, evenUSummand p a j =
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a) := by
  let f : ℕ → ℝ := fun r ↦
    (p : ℝ)⁻¹ ^ (a * a) *
      ((p : ℝ) ^ (r * (2 * a - r)) * (gammaR (p : ℝ) r)⁻¹)
  have hhigh (j : ℕ) (hj : j < a) :
      f (a + (j + 1)) = (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) *
        (gammaR (p : ℝ) (a + (j + 1)))⁻¹ := by
    have hja : j + 1 ≤ a := by omega
    dsimp [f]
    have hsub : 2 * a - (a + (j + 1)) = a - (j + 1) := by omega
    rw [hsub, ← mul_assoc, centered_power_normalization (by omega) hja]
  have hlow (j : ℕ) (hj : j < a) :
      f (a - 1 - j) = (p : ℝ)⁻¹ ^ ((j + 1) * (j + 1)) *
        (gammaR (p : ℝ) (a - (j + 1)))⁻¹ := by
    have hja : j + 1 ≤ a := by omega
    have hindex : a - 1 - j = a - (j + 1) := by omega
    have hsub : 2 * a - (a - (j + 1)) = a + (j + 1) := by omega
    dsimp [f]
    rw [hindex, hsub]
    have hcenter := centered_power_normalization (p := p) (a := a) (j := j + 1)
      (by omega) hja
    rw [mul_comm (a - (j + 1)) (a + (j + 1)), ← mul_assoc, hcenter]
  rw [tsum_eq_sum (s := Finset.range (a + 1))]
  · rw [Finset.sum_range_succ']
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hcenter : f a = (gammaR (p : ℝ) a)⁻¹ := by
      dsimp [f]
      have hsub : 2 * a - a = a := by omega
      rw [hsub]
      simp [inv_pow, hp0]
    have hpairs : (∑ j ∈ Finset.range a, evenUSummand p a (j + 1)) =
        (∑ r ∈ Finset.range a, f r) +
          ∑ j ∈ Finset.range a, f (a + 1 + j) := by
      rw [← Finset.sum_range_reflect f a, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j < a := Finset.mem_range.mp hj
      have hind : a + 1 + j = a + (j + 1) := by omega
      rw [hind, hhigh j hja, hlow j hja]
      simp [evenUSummand, show j + 1 ≤ a by omega]
      ring
    rw [hpairs]
    simp only [evenUSummand, ite_eq_left]
    rw [← hcenter]
    have hU : (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a) =
        ∑ r ∈ Finset.range (2 * a + 1), f r := by
      rw [primePowerU]
      have hfin := Fin.sum_univ_eq_sum_range
        (fun r : ℕ ↦ (p : ℝ) ^ (r * (2 * a - r)) *
          (gammaR (p : ℝ) r)⁻¹) (2 * a + 1)
      rw [hfin, Finset.mul_sum]
    rw [hU]
    have hsize : 2 * a + 1 = (a + 1) + a := by omega
    rw [hsize, Finset.sum_range_add, Finset.sum_range_succ]
    ring
  · intro j hj
    have hja : a < j := by
      rw [Finset.mem_range, not_lt] at hj
      omega
    simp [evenUSummand, show j ≠ 0 by omega, show ¬j ≤ a by omega]

theorem evenUSummand_tendsto {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ evenUSummand p a j) atTop
      (nhds (evenGaussianLimitSummand p j)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  by_cases hj0 : j = 0
  · subst j
    simpa [evenUSummand, evenGaussianLimitSummand, centerMultiplicity] using
      gammaR_inv_tendsto hpR
  · have hplus := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat j)
    have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
    have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) atTop
        (nhds ((p : ℝ)⁻¹ ^ (j * j))) := tendsto_const_nhds
    have ht := hc.mul (hplus.add hminus)
    have hlim : (p : ℝ)⁻¹ ^ (j * j) *
        (eulerC (p : ℝ) + eulerC (p : ℝ)) =
          evenGaussianLimitSummand p j := by
      simp only [evenGaussianLimitSummand, centerMultiplicity, ite_eq_right hj0,
        Nat.cast_ofNat]
      ring
    rw [← hlim]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop j] with a ha
    simp [evenUSummand, hj0, ha]

theorem evenUSummand_nonneg {p a j : ℕ} (hp : 2 ≤ p) :
    0 ≤ evenUSummand p a j := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  unfold evenUSummand
  by_cases hj0 : j = 0
  · rw [ite_eq_left hj0]
    exact (inv_pos.mpr (gammaR_pos hp1 a)).le
  · rw [ite_eq_right hj0]
    by_cases hja : j ≤ a
    · rw [ite_eq_left hja]
      exact mul_nonneg (by positivity)
        (add_nonneg (inv_pos.mpr (gammaR_pos hp1 (a + j))).le
          (inv_pos.mpr (gammaR_pos hp1 (a - j))).le)
    · rw [ite_eq_right hja]

theorem evenUSummand_le {p a j : ℕ} (hp : 2 ≤ p) :
    evenUSummand p a j ≤
      2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  unfold evenUSummand
  by_cases hj0 : j = 0
  · subst j
    simp only [ite_eq_left, Nat.zero_mul, pow_zero, mul_one]
    linarith [gammaR_inv_lt_eulerC hpR a, eulerC_pos hpR]
  · rw [ite_eq_right hj0]
    by_cases hja : j ≤ a
    · rw [ite_eq_left hja]
      have hpow : 0 ≤ (p : ℝ)⁻¹ ^ (j * j) := by positivity
      have hsum : (gammaR (p : ℝ) (a + j))⁻¹ +
          (gammaR (p : ℝ) (a - j))⁻¹ ≤ 2 * eulerC (p : ℝ) := by
        linarith [gammaR_inv_lt_eulerC hpR (a + j),
          gammaR_inv_lt_eulerC hpR (a - j)]
      nlinarith
    · rw [ite_eq_right hja]
      exact mul_nonneg (mul_nonneg (by norm_num) (eulerC_pos hpR).le) (by positivity)

/-- The finite envelope has the same sharp even-rank asymptotic.-/
theorem primePowerU_even_rank_asymptotic {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) * primePowerU p (2 * a)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  rw [← tsum_evenGaussianLimitSummand_eq_sharpConstant hp]
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbound : Summable (fun j : ℕ ↦
      2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j)) :=
    (summable_nat_gaussian_inv_pow hp).mul_left _
  have ht : Tendsto (fun a : ℕ ↦ ∑' j : ℕ, evenUSummand p a j) atTop
      (nhds (∑' j : ℕ, evenGaussianLimitSummand p j)) :=
    tendsto_tsum_of_dominated_convergence
      (f := fun a j ↦ evenUSummand p a j)
      (g := fun j ↦ evenGaussianLimitSummand p j)
      (bound := fun j ↦ 2 * eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))
      hbound (fun j ↦ evenUSummand_tendsto hp)
      (Filter.Eventually.of_forall fun a j ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (evenUSummand_nonneg hp)]
        exact evenUSummand_le hp)
  exact ht.congr' (Filter.Eventually.of_forall fun a ↦
    tsum_evenUSummand_eq_normalized_U hp)

/-- The elementary-abelian count asymptotically exhausts the finite envelope.-/
theorem gaussian_total_div_primePowerU_tendsto_one {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦
      (totalQBinom p (2 * a) : ℝ) / primePowerU p (2 * a)) atTop (nhds 1) := by
  have hdiv := (gaussian_even_rank_asymptotic hp).div
    (primePowerU_even_rank_asymptotic hp)
    (ne_of_gt (sharpConstant_pos (by exact_mod_cast hp)))
  have hCne : sharpConstant (p : ℝ) ≠ 0 :=
    ne_of_gt (sharpConstant_pos (by exact_mod_cast hp))
  rw [div_self hCne] at hdiv
  apply hdiv.congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    have hp0 : (p : ℝ)⁻¹ ^ (a * a) ≠ 0 := by
      exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast (by omega : p ≠ 0)))
    dsimp
    field_simp [hp0]

/-- Exact elementary-abelian realization of every even-rank Gaussian sum.-/
theorem elementaryAbelian_subspace_escape_equality (p a : ℕ) [Fact p.Prime] :
    Nat.card (Submodule (ZMod p) (Fin (2 * a) → ZMod p)) = totalQBinom p (2 * a) :=
  card_all_subspaces_fin_zmod p (2 * a)

/-- No uniformly smaller constant can dominate all normalized even-rank
elementary-abelian examples.-/
theorem sharpConstant_le_of_even_rank_bound {p : ℕ} (hp : 2 ≤ p) {C : ℝ}
    (hC : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C :=
  le_of_tendsto (gaussian_even_rank_asymptotic hp) (Filter.Eventually.of_forall hC)

/-- Any proposed improvement whose normalized right side tends to zero is
incompatible with the elementary-abelian family; this is the quantified
optimal-exponent assertion used in the manuscript.-/
theorem no_vanishing_normalized_bound {p : ℕ} (hp : 2 ≤ p) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (nhds 0))
    (hbound : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤ b a) : False := by
  have hle : sharpConstant (p : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto (gaussian_even_rank_asymptotic hp) hb
      (Filter.Eventually.of_forall hbound)
  exact (not_le_of_gt (sharpConstant_pos (by exact_mod_cast hp))) hle

/-- Explicit optimality of the exponent `1/4`, in normalized exponential
form.  For every `α < 1/4` and every fixed constant `C`, the proposed
normalized right side tends to zero and therefore cannot dominate all
elementary-abelian examples.-/
theorem no_subquarter_normalized_exponential_bound {p : ℕ} (hp : 2 ≤ p)
    {α C : ℝ} (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
  intro hbound
  apply no_vanishing_normalized_bound hp
    (fun a : ℕ ↦ C * Real.exp
      (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2))
  · have hcast : Tendsto (fun a : ℕ ↦ (a : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hsq : Tendsto (fun a : ℕ ↦ (a : ℝ) ^ 2) atTop atTop := by
      simpa [pow_two] using hcast.atTop_mul_atTop₀ hcast
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    have hcoef : Real.log (p : ℝ) * (4 * α - 1) < 0 := by
      exact mul_neg_of_pos_of_neg hlog (by linarith)
    have hexponent : Tendsto (fun a : ℕ ↦
        Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) atTop atBot := by
      simpa [mul_assoc] using hsq.const_mul_atTop_of_neg hcoef
    have hconst : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C) := tendsto_const_nhds
    simpa only [Function.comp_apply, mul_zero] using
      hconst.mul (Real.tendsto_exp_atBot.comp hexponent)
  · exact hbound

/-- Unnormalized `Real.rpow` form of exponent optimality.  The order of the
elementary-abelian group is `p^(2a)`, so an exponent `α` on the square of
the base-`p` logarithm gives the power `p^(4αa²)`.-/
theorem no_subquarter_rpow_bound {p : ℕ} (hp : 2 ≤ p) {α C : ℝ}
    (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * α * (a : ℝ) ^ 2) := by
  intro hbound
  apply no_subquarter_normalized_exponential_bound hp hα
  intro a
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  calc
    (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤
        (p : ℝ)⁻¹ ^ (a * a) *
          (C * Real.rpow (p : ℝ) (4 * α * (a : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound a) (by positivity)
    _ = C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
      change (p : ℝ)⁻¹ ^ (a * a) *
          (C * (p : ℝ) ^ (4 * α * (a : ℝ) ^ 2)) =
        C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2)
      rw [Real.rpow_def_of_pos hpR]
      rw [← exp_neg_log_nat_eq_inv_pow (p := p) (m := a * a) (by omega)]
      calc
        Real.exp (-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) *
              (C * Real.exp (Real.log (p : ℝ) *
                (4 * α * (a : ℝ) ^ 2))) =
            C * (Real.exp (-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) *
              Real.exp (Real.log (p : ℝ) * (4 * α * (a : ℝ) ^ 2))) := by ring
        _ = C * Real.exp
            ((-Real.log (p : ℝ) * ((a * a : ℕ) : ℝ)) +
              Real.log (p : ℝ) * (4 * α * (a : ℝ) ^ 2)) := by
          rw [Real.exp_add]
        _ = C * Real.exp
            (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
          congr 2
          push_cast
          ring

end SharpIntermediateSubgroupBounds
