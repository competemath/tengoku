/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SubgaussianConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite multiscale chaining

This file formalizes the finite, completely elementary core of a chaining
argument.  A process is evaluated along successive projections onto finite
nets.  Its value is decomposed into a base value, a finite telescoping sum of
increments, and a final approximation remainder.  Consequently a large
uniform deviation forces either a large base value or a large increment at
one of the finitely many levels.

The resulting probability estimate is a genuine finite union bound.  It is
stated first with arbitrary scalar tail bounds and then with sub-Gaussian MGF
hypotheses.  This module deliberately does not claim an infinite Dudley
entropy integral: passing to infinitely many levels requires separate
measurability, separability, and limit arguments.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The event that the process is large at one of the points of the coarsest
finite net.-/
def finiteChainingBaseEvent (Z : Omega → T → ℝ) (N0 : Finset T)
    (b : ℝ) : Set Omega :=
  ⋃ u ∈ N0, {omega | b < |Z omega u|}

/-- The event that some adjacent-level increment is larger than its assigned
threshold.  The union includes every pair of points in the two adjacent
nets; this avoids any measurability requirement on the chosen projections.-/
def finiteChainingIncrementEvent (Z : Omega → T → ℝ)
    (N : ℕ → Finset T) (a : ℕ → ℝ) (m : ℕ) : Set Omega :=
  ⋃ k ∈ Finset.range m, ⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
    {omega | a k < |Z omega u - Z omega v|}

/-- Choice of projections onto a finite family of nets.  This isolates the
only use of choice in finite chaining: once each `N k` covers the index
space at radius `eps k`, one can simultaneously choose a nearest-enough net
point at every level up to `m`.-/
theorem exists_finiteNetProjections [PseudoMetricSpace T] [Nonempty T]
    (N : ℕ → Finset T) (eps : ℕ → ℝ) (m : ℕ)
    (hnet : ∀ k, k ≤ m → ∀ t, ∃ u ∈ N k, dist t u ≤ eps k) :
    ∃ proj : ℕ → T → T,
      (∀ k, k ≤ m → ∀ t, proj k t ∈ N k) ∧
      ∀ k, k ≤ m → ∀ t, dist t (proj k t) ≤ eps k := by
  classical
  let fallback : T := Classical.choice (inferInstance : Nonempty T)
  let proj : ℕ → T → T := fun k t ↦
    if hk : k ≤ m then Classical.choose (hnet k hk t) else fallback
  refine ⟨proj, ?_, ?_⟩
  · intro k hk t
    rw [show proj k t = Classical.choose (hnet k hk t) by simp [proj, hk]]
    exact (Classical.choose_spec (hnet k hk t)).1
  · intro k hk t
    rw [show proj k t = Classical.choose (hnet k hk t) by simp [proj, hk]]
    exact (Classical.choose_spec (hnet k hk t)).2

omit [MeasurableSpace Omega] in
/-- A finite telescoping decomposition bounds a process value by its base
value, the absolute adjacent-level increments, and the last approximation
remainder.-/
theorem abs_process_le_finiteChainingSum
    (Z : Omega → T → ℝ) (proj : ℕ → T → T)
    (m : ℕ) (omega : Omega) (t : T) :
    |Z omega t| ≤
      |Z omega (proj 0 t)| +
        ∑ k ∈ Finset.range m,
          |Z omega (proj (k + 1) t) - Z omega (proj k t)|
        + |Z omega t - Z omega (proj m t)| := by
  have htel := Finset.sum_range_sub
    (fun k ↦ Z omega (proj k t)) m
  have hid :
      Z omega t = Z omega (proj 0 t) +
          (∑ k ∈ Finset.range m,
            (Z omega (proj (k + 1) t) - Z omega (proj k t))) +
          (Z omega t - Z omega (proj m t)) := by
    rw [htel]
    ring
  calc
    |Z omega t| =
        |Z omega (proj 0 t) +
          (∑ k ∈ Finset.range m,
            (Z omega (proj (k + 1) t) - Z omega (proj k t))) +
          (Z omega t - Z omega (proj m t))| := congrArg abs hid
    _ ≤
        |Z omega (proj 0 t) +
          (∑ k ∈ Finset.range m,
            (Z omega (proj (k + 1) t) - Z omega (proj k t)))| +
          |Z omega t - Z omega (proj m t)| := abs_add_le _ _
    _ ≤
        |Z omega (proj 0 t)| +
          |∑ k ∈ Finset.range m,
            (Z omega (proj (k + 1) t) - Z omega (proj k t))| +
          |Z omega t - Z omega (proj m t)| := by
      have hadd :
          |Z omega (proj 0 t) +
              (∑ k ∈ Finset.range m,
                (Z omega (proj (k + 1) t) - Z omega (proj k t)))| ≤
            |Z omega (proj 0 t)| +
              |∑ k ∈ Finset.range m,
                (Z omega (proj (k + 1) t) - Z omega (proj k t))| :=
        abs_add_le _ _
      exact add_le_add_left hadd _
    _ ≤ |Z omega (proj 0 t)| +
          ∑ k ∈ Finset.range m,
            |Z omega (proj (k + 1) t) - Z omega (proj k t)| +
          |Z omega t - Z omega (proj m t)| := by
      have hsum :
          |∑ k ∈ Finset.range m,
              (Z omega (proj (k + 1) t) - Z omega (proj k t))| ≤
            ∑ k ∈ Finset.range m,
              |Z omega (proj (k + 1) t) - Z omega (proj k t)| :=
        Finset.abs_sum_le_sum_abs _ _
      exact add_le_add_left
        (add_le_add_right hsum |Z omega (proj 0 t)|)
        |Z omega t - Z omega (proj m t)|

omit [MeasurableSpace Omega] in
/-- Deterministic event inclusion behind finite chaining.  If every point is
projected into its prescribed finite net through level `m`, and the last
projection has error at most `r`, then a deviation larger than the sum of all
thresholds forces a bad base value or a bad adjacent-level increment.

The existential event is the set-theoretically robust formulation of an
upper tail for the supremum; it does not presuppose measurability of that
supremum.-/
theorem finiteChaining_largeDeviation_subset
    (Z : Omega → T → ℝ) (N : ℕ → Finset T)
    (proj : ℕ → T → T) (a : ℕ → ℝ) (b r : ℝ) (m : ℕ)
    (hproj : ∀ k, k ≤ m → ∀ t, proj k t ∈ N k)
    (hrem : ∀ omega t, |Z omega t - Z omega (proj m t)| ≤ r) :
    {omega | ∃ t, b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ⊆
      finiteChainingBaseEvent Z (N 0) b ∪
        finiteChainingIncrementEvent Z N a m := by
  classical
  intro omega homega
  obtain ⟨t, ht⟩ := homega
  by_cases hbase : omega ∈ finiteChainingBaseEvent Z (N 0) b
  · exact Or.inl hbase
  right
  by_contra hincr
  have hbase_le : |Z omega (proj 0 t)| ≤ b := by
    by_contra hbad
    apply hbase
    refine Set.mem_iUnion.2 ⟨proj 0 t, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact hproj 0 (Nat.zero_le m) t
    · exact lt_of_not_ge hbad
  have hincr_le : ∀ k ∈ Finset.range m,
      |Z omega (proj (k + 1) t) - Z omega (proj k t)| ≤ a k := by
    intro k hk
    have hkm : k < m := Finset.mem_range.1 hk
    by_contra hbad
    apply hincr
    refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk,
      Set.mem_iUnion.2 ⟨proj (k + 1) t, Set.mem_iUnion.2 ⟨?_,
        Set.mem_iUnion.2 ⟨proj k t, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩⟩⟩⟩
    · exact hproj (k + 1) (Nat.succ_le_iff.2 hkm) t
    · exact hproj k (Nat.le_of_lt hkm) t
    · exact lt_of_not_ge hbad
  have hchain := abs_process_le_finiteChainingSum Z proj m omega t
  have hsum :
      (∑ k ∈ Finset.range m,
        |Z omega (proj (k + 1) t) - Z omega (proj k t)|) ≤
      ∑ k ∈ Finset.range m, a k :=
    Finset.sum_le_sum hincr_le
  have htotal : |Z omega t| ≤
      b + (∑ k ∈ Finset.range m, a k) + r :=
    hchain.trans (add_le_add (add_le_add hbase_le hsum) (hrem omega t))
  exact (not_lt_of_ge htotal) ht

/-- Finite chaining with arbitrary pointwise tail estimates.  The first term
is the cost of the coarsest net.  At level `k`, the union bound pays for all
`card (N (k+1)) * card (N k)` possible adjacent-net pairs.

This is the reusable probabilistic core: any scalar concentration inequality
can be supplied through `hbaseTail` and `hincrTail`.-/
theorem measureReal_finiteChaining_largeDeviation_le [IsFiniteMeasure mu]
    (Z : Omega → T → ℝ) (N : ℕ → Finset T)
    (proj : ℕ → T → T) (a delta : ℕ → ℝ)
    (b r delta0 : ℝ) (m : ℕ)
    (hproj : ∀ k, k ≤ m → ∀ t, proj k t ∈ N k)
    (hrem : ∀ omega t, |Z omega t - Z omega (proj m t)| ≤ r)
    (hbaseTail : ∀ u ∈ N 0,
      mu.real {omega | b < |Z omega u|} ≤ delta0)
    (hincrTail : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k,
        mu.real {omega | a k < |Z omega u - Z omega v|} ≤ delta k) :
    mu.real {omega | ∃ t,
        b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ≤
      (N 0).card * delta0 +
        ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) * delta k := by
  classical
  let B : Set Omega := finiteChainingBaseEvent Z (N 0) b
  let I : Set Omega := finiteChainingIncrementEvent Z N a m
  have hsubset :
      {omega | ∃ t,
          b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ⊆
        B ∪ I := by
    simpa only [B, I] using
      finiteChaining_largeDeviation_subset Z N proj a b r m hproj hrem
  have hB : mu.real B ≤ (N 0).card * delta0 := by
    calc
      mu.real B ≤
          ∑ u ∈ N 0, mu.real {omega | b < |Z omega u|} := by
        simpa only [B, finiteChainingBaseEvent] using
          (measureReal_biUnion_finset_le (μ := mu) (N 0)
            (fun u ↦ {omega | b < |Z omega u|}))
      _ ≤ ∑ _u ∈ N 0, delta0 :=
        Finset.sum_le_sum hbaseTail
      _ = (N 0).card * delta0 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hlevel : ∀ k ∈ Finset.range m,
      mu.real (⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
          {omega | a k < |Z omega u - Z omega v|}) ≤
        ((N (k + 1)).card * (N k).card : ℕ) * delta k := by
    intro k hk
    calc
      mu.real (⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
          {omega | a k < |Z omega u - Z omega v|}) ≤
          ∑ u ∈ N (k + 1),
            mu.real (⋃ v ∈ N k,
              {omega | a k < |Z omega u - Z omega v|}) :=
        measureReal_biUnion_finset_le (N (k + 1)) _
      _ ≤ ∑ u ∈ N (k + 1),
          ∑ v ∈ N k,
            mu.real {omega | a k < |Z omega u - Z omega v|} := by
        exact Finset.sum_le_sum fun u hu ↦
          measureReal_biUnion_finset_le (N k)
            (fun v ↦ {omega | a k < |Z omega u - Z omega v|})
      _ ≤ ∑ _u ∈ N (k + 1), ∑ _v ∈ N k, delta k := by
        exact Finset.sum_le_sum fun u hu ↦
          Finset.sum_le_sum fun v hv ↦ hincrTail k hk u hu v hv
      _ = ((N (k + 1)).card * (N k).card : ℕ) * delta k := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  have hI : mu.real I ≤
      ∑ k ∈ Finset.range m,
        ((N (k + 1)).card * (N k).card : ℕ) * delta k := by
    calc
      mu.real I ≤
          ∑ k ∈ Finset.range m,
            mu.real (⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
              {omega | a k < |Z omega u - Z omega v|}) := by
        simpa only [I, finiteChainingIncrementEvent] using
          (measureReal_biUnion_finset_le (μ := mu) (Finset.range m)
            (fun k ↦ ⋃ u ∈ N (k + 1), ⋃ v ∈ N k,
              {omega | a k < |Z omega u - Z omega v|}))
      _ ≤ ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) * delta k :=
        Finset.sum_le_sum hlevel
  calc
    mu.real {omega | ∃ t,
        b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ≤
        mu.real (B ∪ I) := measureReal_mono hsubset
    _ ≤ mu.real B + mu.real I := measureReal_union_le B I
    _ ≤ (N 0).card * delta0 +
        ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) * delta k :=
      add_le_add hB hI

/-- Bilateral tail estimate for one variable with a sub-Gaussian MGF.-/
theorem HasSubgaussianMGF.measureReal_abs_ge_le
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c mu) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤ |X omega|} ≤
      2 * exp (-t ^ 2 / (2 * (c : ℝ))) := by
  have hpos := hX.measure_ge_le ht
  have hneg := hX.neg.measure_ge_le ht
  have hset : {omega | t ≤ |X omega|} =
      {omega | t ≤ X omega} ∪ {omega | t ≤ -X omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    mu.real ({omega | t ≤ X omega} ∪ {omega | t ≤ -X omega}) ≤
        mu.real {omega | t ≤ X omega} +
          mu.real {omega | t ≤ -X omega} :=
      measureReal_union_le _ _
    _ ≤ exp (-t ^ 2 / (2 * (c : ℝ))) +
        exp (-t ^ 2 / (2 * (c : ℝ))) :=
      add_le_add hpos hneg
    _ = 2 * exp (-t ^ 2 / (2 * (c : ℝ))) := by ring

/-- Strict version of the bilateral sub-Gaussian tail, convenient for the
open upper-tail events used by finite chaining.-/
theorem HasSubgaussianMGF.measureReal_abs_gt_le
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c mu) {t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t < |X omega|} ≤
      2 * exp (-t ^ 2 / (2 * (c : ℝ))) := by
  exact (measureReal_mono (by
    intro omega homega
    change t < |X omega| at homega
    change t ≤ |X omega|
    exact homega.le)).trans (hX.measureReal_abs_ge_le ht)

/-- Variance proxy furnished by Hoeffding's lemma for a centred variable in
the interval `[lower, upper]`.-/
def hoeffdingMGFProxy (lower upper : ℝ) : ℝ≥0 :=
  (‖upper - lower‖₊ / (2 : ℝ≥0)) ^ (2 : ℕ)

/-- Finite multiscale chaining under sub-Gaussian MGF assumptions.  No
independence between the values at different net points is needed: only the
individual base and increment tails enter the union bound.-/
theorem measureReal_finiteChaining_largeDeviation_le_of_subgaussian
    [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N : ℕ → Finset T)
    (proj : ℕ → T → T) (a : ℕ → ℝ)
    (c : ℕ → ℝ≥0) (b r : ℝ) (c0 : ℝ≥0) (m : ℕ)
    (hproj : ∀ k, k ≤ m → ∀ t, proj k t ∈ N k)
    (hrem : ∀ omega t, |Z omega t - Z omega (proj m t)| ≤ r)
    (hb : 0 ≤ b) (ha : ∀ k ∈ Finset.range m, 0 ≤ a k)
    (hbaseSubG : ∀ u ∈ N 0,
      HasSubgaussianMGF (fun omega ↦ Z omega u) c0 mu)
    (hincrSubG : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k,
        HasSubgaussianMGF (fun omega ↦ Z omega u - Z omega v) (c k) mu) :
    mu.real {omega | ∃ t,
        b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ≤
      (N 0).card *
          (2 * exp (-b ^ 2 / (2 * (c0 : ℝ)))) +
        ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) *
            (2 * exp (-(a k) ^ 2 / (2 * (c k : ℝ)))) := by
  apply measureReal_finiteChaining_largeDeviation_le
    Z N proj a
      (fun k ↦ 2 * exp (-(a k) ^ 2 / (2 * (c k : ℝ))))
      b r (2 * exp (-b ^ 2 / (2 * (c0 : ℝ)))) m hproj hrem
  · intro u hu
    exact (hbaseSubG u hu).measureReal_abs_gt_le hb
  · intro k hk u hu v hv
    exact (hincrSubG k hk u hu v hv).measureReal_abs_gt_le (ha k hk)

/-- Hoeffding specialization of finite chaining.  Boundedness and centring
are required only for the finitely many base values and adjacent-level
increments that appear in the chain.-/
theorem measureReal_finiteChaining_largeDeviation_le_of_hoeffding
    [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N : ℕ → Finset T)
    (proj : ℕ → T → T) (a : ℕ → ℝ)
    (lower upper : ℕ → ℝ)
    (b r lower0 upper0 : ℝ) (m : ℕ)
    (hproj : ∀ k, k ≤ m → ∀ t, proj k t ∈ N k)
    (hrem : ∀ omega t, |Z omega t - Z omega (proj m t)| ≤ r)
    (hb : 0 ≤ b) (ha : ∀ k ∈ Finset.range m, 0 ≤ a k)
    (hbaseMeas : ∀ u ∈ N 0, AEMeasurable (fun omega ↦ Z omega u) mu)
    (hbaseBounds : ∀ u ∈ N 0,
      ∀ᵐ omega ∂mu, Z omega u ∈ Set.Icc lower0 upper0)
    (hbaseCentered : ∀ u ∈ N 0, ∫ omega, Z omega u ∂mu = 0)
    (hincrMeas : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k,
        AEMeasurable (fun omega ↦ Z omega u - Z omega v) mu)
    (hincrBounds : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k, ∀ᵐ omega ∂mu,
        Z omega u - Z omega v ∈ Set.Icc (lower k) (upper k))
    (hincrCentered : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k, ∫ omega, (Z omega u - Z omega v) ∂mu = 0) :
    mu.real {omega | ∃ t,
        b + (∑ k ∈ Finset.range m, a k) + r < |Z omega t|} ≤
      (N 0).card *
          (2 * exp (-b ^ 2 / (2 * (hoeffdingMGFProxy lower0 upper0 : ℝ)))) +
        ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) *
            (2 * exp (-(a k) ^ 2 /
              (2 * (hoeffdingMGFProxy (lower k) (upper k) : ℝ)))) := by
  apply measureReal_finiteChaining_largeDeviation_le_of_subgaussian
    Z N proj a (fun k ↦ hoeffdingMGFProxy (lower k) (upper k))
      b r (hoeffdingMGFProxy lower0 upper0) m hproj hrem hb ha
  · intro u hu
    simpa only [hoeffdingMGFProxy] using
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hbaseMeas u hu) (hbaseBounds u hu) (hbaseCentered u hu))
  · intro k hk u hu v hv
    simpa only [hoeffdingMGFProxy] using
      (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (hincrMeas k hk u hu v hv) (hincrBounds k hk u hu v hv)
        (hincrCentered k hk u hu v hv))

/-- Metric finite chaining.  A deterministic Lipschitz modulus and the
finest projection radius turn the abstract remainder into `L * eps`.
The right-hand side displays the cardinalities of all adjacent net levels.-/
theorem measureReal_finiteChaining_lipschitz_le_of_subgaussian
    [PseudoMetricSpace T] [IsProbabilityMeasure mu]
    (Z : Omega → T → ℝ) (N : ℕ → Finset T)
    (proj : ℕ → T → T) (a : ℕ → ℝ)
    (c : ℕ → ℝ≥0) (b L eps : ℝ) (c0 : ℝ≥0) (m : ℕ)
    (hproj : ∀ k, k ≤ m → ∀ t, proj k t ∈ N k)
    (hnear : ∀ t, dist t (proj m t) ≤ eps)
    (hlip : ∀ omega s t, |Z omega s - Z omega t| ≤ L * dist s t)
    (hL : 0 ≤ L) (hb : 0 ≤ b)
    (ha : ∀ k ∈ Finset.range m, 0 ≤ a k)
    (hbaseSubG : ∀ u ∈ N 0,
      HasSubgaussianMGF (fun omega ↦ Z omega u) c0 mu)
    (hincrSubG : ∀ k ∈ Finset.range m, ∀ u ∈ N (k + 1),
      ∀ v ∈ N k,
        HasSubgaussianMGF (fun omega ↦ Z omega u - Z omega v) (c k) mu) :
    mu.real {omega | ∃ t,
        b + (∑ k ∈ Finset.range m, a k) + L * eps < |Z omega t|} ≤
      (N 0).card *
          (2 * exp (-b ^ 2 / (2 * (c0 : ℝ)))) +
        ∑ k ∈ Finset.range m,
          ((N (k + 1)).card * (N k).card : ℕ) *
            (2 * exp (-(a k) ^ 2 / (2 * (c k : ℝ)))) := by
  apply measureReal_finiteChaining_largeDeviation_le_of_subgaussian
    Z N proj a c b (L * eps) c0 m hproj
  · intro omega t
    exact (hlip omega t (proj m t)).trans
      (mul_le_mul_of_nonneg_left (hnear t) hL)
  · exact hb
  · exact ha
  · exact hbaseSubG
  · exact hincrSubG

end ProbabilityTheory
