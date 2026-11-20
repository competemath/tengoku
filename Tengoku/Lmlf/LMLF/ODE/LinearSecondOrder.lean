import Tengoku.Seed.Analysis.Calculus.ContDiff.Deriv
import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Analysis.ODE.ExistUnique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global second-order linear initial-value problems

Existence and uniqueness on an arbitrary open real interval for homogeneous
second-order linear equations with continuous real or complex coefficients.
-/

open Function Metric Set
open scoped NNReal Topology

namespace LMLF.ODE

private theorem exists_stateSolutionOn_localIoo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E → E} {A B c d : ℝ}
    (hd : 0 < d) (hsub : Icc (c - d) (c + d) ⊆ Icc A B)
    (K : ℝ≥0) (hK : 0 < K)
    (hLip : ∀ t ∈ Icc A B, LipschitzWith K (F t))
    (hTime : ∀ z, ContinuousOn (fun t ↦ F t z) (Icc A B))
    (hGrow : ∀ t ∈ Icc A B, ∀ z, ‖F t z‖ ≤ (K : ℝ) * ‖z‖)
    (hdK : d ≤ 1 / (2 * (K : ℝ))) (z₀ : E) :
    ∃ X : ℝ → E, X c = z₀ ∧
      ∀ t ∈ Ioo (c - d) (c + d), HasDerivAt X (F t (X t)) t := by
  let R : ℝ≥0 := ⟨1 + ‖z₀‖, by positivity⟩
  let L : ℝ≥0 := 2 * K * R
  have hc : c ∈ Icc (c - d) (c + d) := by constructor <;> linarith
  let c' : Icc (c - d) (c + d) := ⟨c, hc⟩
  have hPL : IsPicardLindelof F c' z₀ R 0 L K := by
    constructor
    · intro t ht
      exact (hLip t (hsub ht)).lipschitzOnWith
    · intro z hz
      exact (hTime z).mono hsub
    · intro t ht z hz
      have hz' : ‖z‖ ≤ 2 * (R : ℝ) := by
        have hdist : ‖z - z₀‖ ≤ (R : ℝ) := by
          simpa [mem_closedBall, dist_eq_norm] using hz
        calc
          ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
            simpa only [sub_add_cancel] using norm_add_le (z - z₀) z₀
          _ ≤ (R : ℝ) + ‖z₀‖ := by gcongr
          _ ≤ 2 * (R : ℝ) := by
            change (1 + ‖z₀‖) + ‖z₀‖ ≤ 2 * (1 + ‖z₀‖)
            linarith
      calc
        ‖F t z‖ ≤ (K : ℝ) * ‖z‖ := hGrow t (hsub ht) z
        _ ≤ (K : ℝ) * (2 * (R : ℝ)) :=
          mul_le_mul_of_nonneg_left hz' K.2
        _ = (L : ℝ) := by simp [L]; ring
    · change (L : ℝ) * max ((c + d) - c) (c - (c - d)) ≤ (R : ℝ) - 0
      rw [show (c + d) - c = d by ring, show c - (c - d) = d by ring, max_self]
      simp only [L, NNReal.coe_mul, NNReal.coe_ofNat, sub_zero]
      have htwoK : 0 < 2 * (K : ℝ) := by positivity
      have hprod : (2 * (K : ℝ)) * d ≤ 1 := by
        calc
          (2 * (K : ℝ)) * d ≤ (2 * (K : ℝ)) * (1 / (2 * (K : ℝ))) :=
            mul_le_mul_of_nonneg_left hdK (le_of_lt htwoK)
          _ = 1 := by field_simp
      calc
        2 * (K : ℝ) * (R : ℝ) * d =
            ((2 * (K : ℝ)) * d) * (R : ℝ) := by ring
        _ ≤ 1 * (R : ℝ) := mul_le_mul_of_nonneg_right hprod R.2
        _ = (R : ℝ) := one_mul _
  obtain ⟨X, hXc, hX⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨X, hXc, fun t ht ↦ ?_⟩
  exact (hX t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

private theorem extend_stateSolution_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {p r c d : ℝ} (K : ℝ≥0)
    (hpc : p < c) (hcr : c < r) (hd : 0 < d)
    {X Y : ℝ → E}
    (hX : ∀ t ∈ Ioo p r, HasDerivAt X (F t (X t)) t)
    (hY : ∀ t ∈ Ioo (c - d) (c + d), HasDerivAt Y (F t (Y t)) t)
    (hXYc : X c = Y c)
    (hLip : ∀ t ∈ Ioo (c - d) (c + d), LipschitzWith K (F t)) :
    ∃ Z : ℝ → E,
      (∀ t, t ≤ c → Z t = X t) ∧
      ∀ t ∈ Ioo p (c + d), HasDerivAt Z (F t (Z t)) t := by
  let lo := max p (c - d)
  let hi := min r (c + d)
  have hcJ : c ∈ Ioo lo hi := by
    constructor
    · simp only [lo, max_lt_iff]
      exact ⟨hpc, by linarith⟩
    · simp only [hi, lt_min_iff]
      exact ⟨hcr, by linarith⟩
  have hEq : EqOn X Y (Ioo lo hi) := by
    apply ODE_solution_unique_of_mem_Ioo (K := K) (v := F) (s := fun _ ↦ univ)
      (t₀ := c)
    · intro t ht
      exact (hLip t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩).lipschitzOnWith
    · exact hcJ
    · intro t ht
      exact ⟨hX t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩, mem_univ _⟩
    · intro t ht
      exact ⟨hY t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩, mem_univ _⟩
    · exact hXYc
  let Z : ℝ → E := fun t ↦ if t ≤ c then X t else Y t
  refine ⟨Z, fun t ht ↦ by simp [Z, ht], ?_⟩
  intro t ht
  rcases lt_trichotomy t c with htc | htc | hct
  · have hZX : Z =ᶠ[nhds t] X := by
      filter_upwards [Iio_mem_nhds htc] with u hu
      change u < c at hu
      simp only [Z, ite_eq_left (le_of_lt hu)]
    have htOld : t ∈ Ioo p r := ⟨ht.1, lt_trans htc hcr⟩
    simpa [hZX.eq_of_nhds] using (hX t htOld).congr_of_eventuallyEq hZX
  · subst t
    have hZX : Z =ᶠ[nhds c] X := by
      filter_upwards [isOpen_Ioo.mem_nhds hcJ] with u hu
      by_cases huc : u ≤ c
      · simp [Z, huc]
      · simp only [Z, ite_eq_right huc]
        exact (hEq hu).symm
    have hcOld : c ∈ Ioo p r := ⟨hpc, hcr⟩
    simpa [hZX.eq_of_nhds] using (hX c hcOld).congr_of_eventuallyEq hZX
  · have hZY : Z =ᶠ[nhds t] Y := by
      filter_upwards [Ioi_mem_nhds hct] with u hu
      change c < u at hu
      simp only [Z, ite_eq_right (not_le_of_gt hu)]
    have htNew : t ∈ Ioo (c - d) (c + d) := ⟨by linarith, ht.2⟩
    simpa [hZY.eq_of_nhds] using (hY t htNew).congr_of_eventuallyEq hZY

private theorem extend_stateSolution_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {l q c d : ℝ} (K : ℝ≥0)
    (hlc : l < c) (hcq : c < q) (hd : 0 < d)
    {X Y : ℝ → E}
    (hX : ∀ t ∈ Ioo l q, HasDerivAt X (F t (X t)) t)
    (hY : ∀ t ∈ Ioo (c - d) (c + d), HasDerivAt Y (F t (Y t)) t)
    (hXYc : X c = Y c)
    (hLip : ∀ t ∈ Ioo (c - d) (c + d), LipschitzWith K (F t)) :
    ∃ Z : ℝ → E,
      (∀ t, c ≤ t → Z t = X t) ∧
      ∀ t ∈ Ioo (c - d) q, HasDerivAt Z (F t (Z t)) t := by
  let lo := max l (c - d)
  let hi := min q (c + d)
  have hcJ : c ∈ Ioo lo hi := by
    constructor
    · simp only [lo, max_lt_iff]
      exact ⟨hlc, by linarith⟩
    · simp only [hi, lt_min_iff]
      exact ⟨hcq, by linarith⟩
  have hEq : EqOn X Y (Ioo lo hi) := by
    apply ODE_solution_unique_of_mem_Ioo (K := K) (v := F) (s := fun _ ↦ univ)
      (t₀ := c)
    · intro t ht
      exact (hLip t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩).lipschitzOnWith
    · exact hcJ
    · intro t ht
      exact ⟨hX t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩, mem_univ _⟩
    · intro t ht
      exact ⟨hY t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩, mem_univ _⟩
    · exact hXYc
  let Z : ℝ → E := fun t ↦ if c ≤ t then X t else Y t
  refine ⟨Z, fun t ht ↦ by simp [Z, ht], ?_⟩
  intro t ht
  rcases lt_trichotomy t c with htc | htc | hct
  · have hZY : Z =ᶠ[nhds t] Y := by
      filter_upwards [Iio_mem_nhds htc] with u hu
      change u < c at hu
      simp only [Z, ite_eq_right (not_le_of_gt hu)]
    have htNew : t ∈ Ioo (c - d) (c + d) := ⟨ht.1, by linarith⟩
    simpa [hZY.eq_of_nhds] using (hY t htNew).congr_of_eventuallyEq hZY
  · subst t
    have hZX : Z =ᶠ[nhds c] X := by
      filter_upwards [isOpen_Ioo.mem_nhds hcJ] with u hu
      by_cases hcu : c ≤ u
      · simp [Z, hcu]
      · simp only [Z, ite_eq_right hcu]
        exact (hEq hu).symm
    have hcOld : c ∈ Ioo l q := ⟨hlc, hcq⟩
    simpa [hZX.eq_of_nhds] using (hX c hcOld).congr_of_eventuallyEq hZX
  · have hZX : Z =ᶠ[nhds t] X := by
      filter_upwards [Ioi_mem_nhds hct] with u hu
      change c < u at hu
      simp only [Z, ite_eq_left (le_of_lt hu)]
    have htOld : t ∈ Ioo l q := ⟨lt_trans hlc hct, ht.2⟩
    simpa [hZX.eq_of_nhds] using (hX t htOld).congr_of_eventuallyEq hZX

private theorem exists_stateSolutionOn_rightChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {t₀ d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hsd : s < d)
    (K : ℝ≥0) (n : ℕ)
    (hLocal : ∀ i : ℕ, i ≤ n → ∀ z : E,
      ∃ X : ℝ → E, X (t₀ + (i : ℝ) * s) = z ∧
        ∀ t ∈ Ioo (t₀ + (i : ℝ) * s - d) (t₀ + (i : ℝ) * s + d),
          HasDerivAt X (F t (X t)) t)
    (hLip : ∀ i : ℕ, i ≤ n → ∀ t ∈
      Ioo (t₀ + (i : ℝ) * s - d) (t₀ + (i : ℝ) * s + d),
      LipschitzWith K (F t)) (z₀ : E) :
    ∃ X : ℝ → E, X t₀ = z₀ ∧
      ∀ t ∈ Ioo (t₀ - d) (t₀ + (n : ℝ) * s + d),
        HasDerivAt X (F t (X t)) t := by
  induction n with
  | zero =>
      obtain ⟨X, hX₀, hX⟩ := hLocal 0 le_rfl z₀
      refine ⟨X, ?_, ?_⟩
      · simpa using hX₀
      · simpa using hX
  | succ n ih =>
      have hLocal' : ∀ i : ℕ, i ≤ n → ∀ z : E,
          ∃ X : ℝ → E, X (t₀ + (i : ℝ) * s) = z ∧
            ∀ t ∈ Ioo (t₀ + (i : ℝ) * s - d) (t₀ + (i : ℝ) * s + d),
              HasDerivAt X (F t (X t)) t :=
        fun i hi ↦ hLocal i (hi.trans n.le_succ)
      have hLip' : ∀ i : ℕ, i ≤ n → ∀ t ∈
          Ioo (t₀ + (i : ℝ) * s - d) (t₀ + (i : ℝ) * s + d),
          LipschitzWith K (F t) :=
        fun i hi ↦ hLip i (hi.trans n.le_succ)
      obtain ⟨X, hX₀, hX⟩ := ih hLocal' hLip'
      let c := t₀ + ((n + 1 : ℕ) : ℝ) * s
      obtain ⟨Y, hYc, hY⟩ := hLocal (n + 1) le_rfl (X c)
      have hpc : t₀ - d < c := by
        dsimp [c]
        push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      have hcr : c < t₀ + (n : ℝ) * s + d := by
        dsimp [c]
        push_cast
        linarith
      obtain ⟨Z, hZX, hZ⟩ := extend_stateSolution_right K hpc hcr hd hX hY hYc.symm
        (hLip (n + 1) le_rfl)
      refine ⟨Z, ?_, ?_⟩
      · rw [hZX t₀]
        · exact hX₀
        · dsimp [c]
          push_cast
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith
      · simpa [c, Nat.cast_add, Nat.cast_one, add_mul] using hZ

private theorem exists_stateSolutionOn_leftChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E → E} {t₀ d s : ℝ} (hd : 0 < d) (hs : 0 < s) (hsd : s < d)
    (K : ℝ≥0) (n : ℕ)
    (hLocal : ∀ i : ℕ, i ≤ n → ∀ z : E,
      ∃ X : ℝ → E, X (t₀ - (i : ℝ) * s) = z ∧
        ∀ t ∈ Ioo (t₀ - (i : ℝ) * s - d) (t₀ - (i : ℝ) * s + d),
          HasDerivAt X (F t (X t)) t)
    (hLip : ∀ i : ℕ, i ≤ n → ∀ t ∈
      Ioo (t₀ - (i : ℝ) * s - d) (t₀ - (i : ℝ) * s + d),
      LipschitzWith K (F t)) (z₀ : E) :
    ∃ X : ℝ → E, X t₀ = z₀ ∧
      ∀ t ∈ Ioo (t₀ - (n : ℝ) * s - d) (t₀ + d),
        HasDerivAt X (F t (X t)) t := by
  induction n with
  | zero =>
      obtain ⟨X, hX₀, hX⟩ := hLocal 0 le_rfl z₀
      refine ⟨X, ?_, ?_⟩
      · simpa using hX₀
      · simpa using hX
  | succ n ih =>
      have hLocal' : ∀ i : ℕ, i ≤ n → ∀ z : E,
          ∃ X : ℝ → E, X (t₀ - (i : ℝ) * s) = z ∧
            ∀ t ∈ Ioo (t₀ - (i : ℝ) * s - d) (t₀ - (i : ℝ) * s + d),
              HasDerivAt X (F t (X t)) t :=
        fun i hi ↦ hLocal i (hi.trans n.le_succ)
      have hLip' : ∀ i : ℕ, i ≤ n → ∀ t ∈
          Ioo (t₀ - (i : ℝ) * s - d) (t₀ - (i : ℝ) * s + d),
          LipschitzWith K (F t) :=
        fun i hi ↦ hLip i (hi.trans n.le_succ)
      obtain ⟨X, hX₀, hX⟩ := ih hLocal' hLip'
      let c := t₀ - ((n + 1 : ℕ) : ℝ) * s
      obtain ⟨Y, hYc, hY⟩ := hLocal (n + 1) le_rfl (X c)
      have hlc : t₀ - (n : ℝ) * s - d < c := by
        dsimp [c]
        push_cast
        linarith
      have hcq : c < t₀ + d := by
        dsimp [c]
        push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      obtain ⟨Z, hZX, hZ⟩ := extend_stateSolution_left K hlc hcq hd hX hY hYc.symm
        (hLip (n + 1) le_rfl)
      refine ⟨Z, ?_, ?_⟩
      · rw [hZX t₀]
        · exact hX₀
        · dsimp [c]
          push_cast
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith
      · simpa [c, Nat.cast_add, Nat.cast_one, add_mul] using hZ

private theorem exists_stateSolutionOn_Ioo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : ℝ → E → E} {A p t₀ q B : ℝ}
    (hAp : A < p) (hpt₀ : p < t₀) (ht₀q : t₀ < q) (hqB : q < B)
    (K : ℝ≥0) (hK : 0 < K)
    (hLip : ∀ t ∈ Icc A B, LipschitzWith K (F t))
    (hTime : ∀ z, ContinuousOn (fun t ↦ F t z) (Icc A B))
    (hGrow : ∀ t ∈ Icc A B, ∀ z, ‖F t z‖ ≤ (K : ℝ) * ‖z‖)
    (z₀ : E) :
    ∃ X : ℝ → E, X t₀ = z₀ ∧
      ∀ t ∈ Ioo p q, HasDerivAt X (F t (X t)) t := by
  classical
  let μ : ℝ := min (p - A) (B - q)
  have hμ : 0 < μ := by simp only [μ, lt_min_iff]; constructor <;> linarith
  let d : ℝ := min (μ / 2) (1 / (4 * (K : ℝ)))
  have hd : 0 < d := by
    simp only [d, lt_min_iff]
    constructor
    · positivity
    · positivity
  have hdμ : d ≤ μ / 2 := min_le_left _ _
  have hdK4 : d ≤ 1 / (4 * (K : ℝ)) := min_le_right _ _
  have hdK2 : d ≤ 1 / (2 * (K : ℝ)) := by
    calc
      d ≤ 1 / (4 * (K : ℝ)) := hdK4
      _ ≤ 1 / (2 * (K : ℝ)) := by
        have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hdpA : d < p - A := by
    have hμpa : μ ≤ p - A := min_le_left _ _
    nlinarith
  have hdBq : d < B - q := by
    have hμbq : μ ≤ B - q := min_le_right _ _
    nlinarith
  obtain ⟨nR, hnR⟩ := exists_nat_gt ((q - t₀) / d)
  have hnRpos : 0 < (nR : ℝ) := by
    have : 0 < (q - t₀) / d := div_pos (sub_pos.mpr ht₀q) hd
    exact lt_of_lt_of_le this (le_of_lt hnR)
  let sR : ℝ := (q - t₀) / (nR : ℝ)
  have hsR : 0 < sR := div_pos (sub_pos.mpr ht₀q) hnRpos
  have hsRd : sR < d := by
    apply (div_lt_iff₀ hnRpos).2
    exact (div_lt_iff₀ hd).1 hnR |>.trans_eq (mul_comm _ _)
  have hcenterR (i : ℕ) (hi : i ≤ nR) : t₀ + (i : ℝ) * sR ∈ Icc t₀ q := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) (le_of_lt hsR))
    · have hin : (i : ℝ) ≤ (nR : ℝ) := by exact_mod_cast hi
      have hsR0 : 0 ≤ sR := le_of_lt hsR
      calc
        t₀ + (i : ℝ) * sR ≤ t₀ + (nR : ℝ) * sR := by gcongr
        _ = q := by
          have hmul : (nR : ℝ) * sR = q - t₀ := by
            exact mul_div_cancel₀ (q - t₀) (ne_of_gt hnRpos)
          rw [hmul]
          ring
  have hslabR (i : ℕ) (hi : i ≤ nR) :
      Icc (t₀ + (i : ℝ) * sR - d) (t₀ + (i : ℝ) * sR + d) ⊆ Icc A B := by
    intro t ht
    rcases hcenterR i hi with ⟨hc₁, hc₂⟩
    rcases ht with ⟨ht₁, ht₂⟩
    constructor <;> linarith
  have hLocalR : ∀ i : ℕ, i ≤ nR → ∀ z : E,
      ∃ X : ℝ → E, X (t₀ + (i : ℝ) * sR) = z ∧
        ∀ t ∈ Ioo (t₀ + (i : ℝ) * sR - d) (t₀ + (i : ℝ) * sR + d),
          HasDerivAt X (F t (X t)) t := by
    intro i hi z
    exact exists_stateSolutionOn_localIoo hd (hslabR i hi) K hK hLip hTime hGrow hdK2 z
  have hLipR : ∀ i : ℕ, i ≤ nR → ∀ t ∈
      Ioo (t₀ + (i : ℝ) * sR - d) (t₀ + (i : ℝ) * sR + d),
      LipschitzWith K (F t) := by
    intro i hi t ht
    exact hLip t (hslabR i hi (Ioo_subset_Icc_self ht))
  obtain ⟨XR, hXR₀, hXR⟩ :=
    exists_stateSolutionOn_rightChain hd hsR hsRd K nR hLocalR hLipR z₀
  obtain ⟨nL, hnL⟩ := exists_nat_gt ((t₀ - p) / d)
  have hnLpos : 0 < (nL : ℝ) := by
    have : 0 < (t₀ - p) / d := div_pos (sub_pos.mpr hpt₀) hd
    exact lt_of_lt_of_le this (le_of_lt hnL)
  let sL : ℝ := (t₀ - p) / (nL : ℝ)
  have hsL : 0 < sL := div_pos (sub_pos.mpr hpt₀) hnLpos
  have hsLd : sL < d := by
    apply (div_lt_iff₀ hnLpos).2
    exact (div_lt_iff₀ hd).1 hnL |>.trans_eq (mul_comm _ _)
  have hcenterL (i : ℕ) (hi : i ≤ nL) : t₀ - (i : ℝ) * sL ∈ Icc p t₀ := by
    constructor
    · have hin : (i : ℝ) ≤ (nL : ℝ) := by exact_mod_cast hi
      have hsL0 : 0 ≤ sL := le_of_lt hsL
      calc
        p = t₀ - (nL : ℝ) * sL := by
          have hmul : (nL : ℝ) * sL = t₀ - p := by
            exact mul_div_cancel₀ (t₀ - p) (ne_of_gt hnLpos)
          rw [hmul]
          ring
        _ ≤ t₀ - (i : ℝ) * sL := by gcongr
    · exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg i) (le_of_lt hsL))
  have hslabL (i : ℕ) (hi : i ≤ nL) :
      Icc (t₀ - (i : ℝ) * sL - d) (t₀ - (i : ℝ) * sL + d) ⊆ Icc A B := by
    intro t ht
    rcases hcenterL i hi with ⟨hc₁, hc₂⟩
    rcases ht with ⟨ht₁, ht₂⟩
    constructor <;> linarith
  have hLocalL : ∀ i : ℕ, i ≤ nL → ∀ z : E,
      ∃ X : ℝ → E, X (t₀ - (i : ℝ) * sL) = z ∧
        ∀ t ∈ Ioo (t₀ - (i : ℝ) * sL - d) (t₀ - (i : ℝ) * sL + d),
          HasDerivAt X (F t (X t)) t := by
    intro i hi z
    exact exists_stateSolutionOn_localIoo hd (hslabL i hi) K hK hLip hTime hGrow hdK2 z
  have hLipL : ∀ i : ℕ, i ≤ nL → ∀ t ∈
      Ioo (t₀ - (i : ℝ) * sL - d) (t₀ - (i : ℝ) * sL + d),
      LipschitzWith K (F t) := by
    intro i hi t ht
    exact hLip t (hslabL i hi (Ioo_subset_Icc_self ht))
  obtain ⟨XL, hXL₀, hXL⟩ :=
    exists_stateSolutionOn_leftChain hd hsL hsLd K nL hLocalL hLipL z₀
  have hnRsR : t₀ + (nR : ℝ) * sR = q := by
    have hmul : (nR : ℝ) * sR = q - t₀ := by
      exact mul_div_cancel₀ (q - t₀) (ne_of_gt hnRpos)
    rw [hmul]
    ring
  have hnLsL : t₀ - (nL : ℝ) * sL = p := by
    have hmul : (nL : ℝ) * sL = t₀ - p := by
      exact mul_div_cancel₀ (t₀ - p) (ne_of_gt hnLpos)
    rw [hmul]
    ring
  have hEq : EqOn XL XR (Ioo (t₀ - d) (t₀ + d)) := by
    apply ODE_solution_unique_of_mem_Ioo (K := K) (v := F) (s := fun _ ↦ univ)
      (t₀ := t₀)
    · intro t ht
      apply (hLip t (hslabR 0 (Nat.zero_le _)
        (Ioo_subset_Icc_self (by simpa using ht)))).lipschitzOnWith
    · exact ⟨by linarith, by linarith⟩
    · intro t ht
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨hXL t ⟨by rw [hnLsL]; linarith, ht₂⟩, mem_univ _⟩
    · intro t ht
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨hXR t ⟨ht₁, by rw [hnRsR]; linarith⟩, mem_univ _⟩
    · exact hXL₀.trans hXR₀.symm
  let X : ℝ → E := fun t ↦ if t ≤ t₀ then XL t else XR t
  refine ⟨X, by simp [X, hXL₀], ?_⟩
  intro t ht
  rcases lt_trichotomy t t₀ with htt₀ | htt₀ | ht₀t
  · have hXXL : X =ᶠ[nhds t] XL := by
      filter_upwards [Iio_mem_nhds htt₀] with u hu
      change u < t₀ at hu
      simp only [X, ite_eq_left (le_of_lt hu)]
    have htL : t ∈ Ioo (t₀ - (nL : ℝ) * sL - d) (t₀ + d) := by
      rw [hnLsL]
      exact ⟨by linarith [ht.1], by linarith⟩
    simpa [hXXL.eq_of_nhds] using (hXL t htL).congr_of_eventuallyEq hXXL
  · subst t
    have hXXL : X =ᶠ[nhds t₀] XL := by
      filter_upwards [Ioo_mem_nhds (by linarith : t₀ - d < t₀)
        (by linarith : t₀ < t₀ + d)] with u hu
      by_cases hut₀ : u ≤ t₀
      · simp [X, hut₀]
      · simp only [X, ite_eq_right hut₀]
        exact (hEq hu).symm
    have htL : t₀ ∈ Ioo (t₀ - (nL : ℝ) * sL - d) (t₀ + d) := by
      rw [hnLsL]
      constructor <;> linarith
    simpa [hXXL.eq_of_nhds] using (hXL t₀ htL).congr_of_eventuallyEq hXXL
  · have hXXR : X =ᶠ[nhds t] XR := by
      filter_upwards [Ioi_mem_nhds ht₀t] with u hu
      change t₀ < u at hu
      simp only [X, ite_eq_right (not_le_of_gt hu)]
    have htR : t ∈ Ioo (t₀ - d) (t₀ + (nR : ℝ) * sR + d) := by
      rw [hnRsR]
      exact ⟨by linarith, by linarith [ht.2]⟩
    simpa [hXXR.eq_of_nhds] using (hXR t htR).congr_of_eventuallyEq hXXR

private theorem exists_open_Icc_around
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ∃ p q : ℝ, p < min x y ∧ max x y < q ∧ Icc p q ⊆ I := by
  have hmin : min x y ∈ I := by
    rcases le_total x y with hxy | hyx
    · simpa [min_eq_left hxy] using hx
    · simpa [min_eq_right hyx] using hy
  have hmax : max x y ∈ I := by
    rcases le_total x y with hxy | hyx
    · simpa [max_eq_right hxy] using hy
    · simpa [max_eq_left hyx] using hx
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.mp hI (min x y) hmin
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.mp hI (max x y) hmax
  let p := min x y - ε / 2
  let q := max x y + δ / 2
  have hp : p ∈ I := hεI (by
    rw [mem_ball, Real.dist_eq]
    dsimp [p]
    rw [show min x y - ε / 2 - min x y = -(ε / 2) by ring, abs_neg,
      abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hq : q ∈ I := hδI (by
    rw [mem_ball, Real.dist_eq]
    dsimp [q]
    rw [show max x y + δ / 2 - max x y = δ / 2 by ring,
      abs_of_pos (by positivity : 0 < δ / 2)]
    linarith)
  refine ⟨p, q, by dsimp [p]; linarith, by dsimp [q]; linarith, ?_⟩
  have hpq : p ≤ q := by
    have hminmax : min x y ≤ max x y := min_le_max
    dsimp [p, q]
    linarith
  rw [← uIcc_of_le hpq]
  exact hIc.ordConnected.uIcc_subset hp hq

private theorem exists_unique_stateSolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {F : ℝ → E → E}
    (hTime : ∀ z, ContinuousOn (fun t ↦ F t z) I)
    (hCompact : ∀ {A B : ℝ}, Icc A B ⊆ I →
      ∃ K : ℝ≥0, 0 < K ∧
        (∀ t ∈ Icc A B, LipschitzWith K (F t)) ∧
        (∀ t ∈ Icc A B, ∀ z, ‖F t z‖ ≤ (K : ℝ) * ‖z‖))
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (z₀ : E) :
    ∃ X : ℝ → E,
      X t₀ = z₀ ∧
      (∀ t ∈ I, HasDerivAt X (F t (X t)) t) ∧
      ∀ Y : ℝ → E,
        Y t₀ = z₀ →
        (∀ t ∈ I, HasDerivAt Y (F t (Y t)) t) →
        EqOn X Y I := by
  classical
  let W := {pq : ℝ × ℝ // pq.1 < t₀ ∧ t₀ < pq.2 ∧ Icc pq.1 pq.2 ⊆ I}
  have hWsol : ∀ w : W, ∃ X : ℝ → E, X t₀ = z₀ ∧
      ∀ t ∈ Ioo w.1.1 w.1.2, HasDerivAt X (F t (X t)) t := by
    intro w
    obtain ⟨A, B, hAw, hwB, hABI⟩ :=
      exists_open_Icc_around hI hIc
        (w.2.2.2 ⟨le_rfl, (w.2.1.trans w.2.2.1).le⟩)
        (w.2.2.2 ⟨(w.2.1.trans w.2.2.1).le, le_rfl⟩)
    have hpq : w.1.1 ≤ w.1.2 := (w.2.1.trans w.2.2.1).le
    have hA : A < w.1.1 := by simpa [min_eq_left hpq] using hAw
    have hB : w.1.2 < B := by simpa [max_eq_right hpq] using hwB
    obtain ⟨K, hK, hLip, hGrow⟩ := hCompact hABI
    exact exists_stateSolutionOn_Ioo hA w.2.1 w.2.2.1 hB K hK hLip
      (fun z ↦ (hTime z).mono hABI) hGrow z₀
  choose winSol hwinSol using hWsol
  have hCompat (w₁ w₂ : W) :
      EqOn (winSol w₁) (winSol w₂)
        (Ioo (max w₁.1.1 w₂.1.1) (min w₁.1.2 w₂.1.2)) := by
    let A := max w₁.1.1 w₂.1.1
    let B := min w₁.1.2 w₂.1.2
    have hAB : Icc A B ⊆ I := by
      intro t ht
      apply w₁.2.2.2
      exact ⟨le_trans (le_max_left _ _) ht.1, le_trans ht.2 (min_le_left _ _)⟩
    obtain ⟨K, hK, hLip, hGrow⟩ := hCompact hAB
    apply ODE_solution_unique_of_mem_Ioo (K := K) (v := F) (s := fun _ ↦ univ)
      (t₀ := t₀)
    · intro t ht
      exact (hLip t (Ioo_subset_Icc_self ht)).lipschitzOnWith
    · constructor
      · simp only [max_lt_iff]
        exact ⟨w₁.2.1, w₂.2.1⟩
      · simp only [lt_min_iff]
        exact ⟨w₁.2.2.1, w₂.2.2.1⟩
    · intro t ht
      exact ⟨(hwinSol w₁).2 t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_left _ _)⟩, mem_univ _⟩
    · intro t ht
      exact ⟨(hwinSol w₂).2 t ⟨lt_of_le_of_lt (le_max_right _ _) ht.1,
        lt_of_lt_of_le ht.2 (min_le_right _ _)⟩, mem_univ _⟩
    · exact (hwinSol w₁).1.trans (hwinSol w₂).1.symm
  have hWindow : ∀ x ∈ I, ∃ w : W, x ∈ Ioo w.1.1 w.1.2 := by
    intro x hx
    obtain ⟨p, q, hp, hq, hpqI⟩ := exists_open_Icc_around hI hIc ht₀ hx
    have hpt₀ : p < t₀ := lt_of_lt_of_le hp (min_le_left _ _)
    have hpx : p < x := lt_of_lt_of_le hp (min_le_right _ _)
    have ht₀q : t₀ < q := lt_of_le_of_lt (le_max_left _ _) hq
    have hxq : x < q := lt_of_le_of_lt (le_max_right _ _) hq
    exact ⟨⟨(p, q), hpt₀, ht₀q, hpqI⟩, hpx, hxq⟩
  choose window hwindow using hWindow
  let X : ℝ → E := fun x ↦ if hx : x ∈ I then winSol (window x hx) x else 0
  have hX₀ : X t₀ = z₀ := by
    simp only [X, dite_eq_left ht₀]
    exact (hwinSol (window t₀ ht₀)).1
  have hX : ∀ x ∈ I, HasDerivAt X (F x (X x)) x := by
    intro x hx
    let w := window x hx
    have hEq : X =ᶠ[nhds x] winSol w := by
      filter_upwards [isOpen_Ioo.mem_nhds (hwindow x hx)] with u hu
      have huI : u ∈ I := w.2.2.2 (Ioo_subset_Icc_self hu)
      simp only [X, dite_eq_left huI]
      apply hCompat (window u huI) w
      exact ⟨max_lt_iff.mpr ⟨(hwindow u huI).1, hu.1⟩,
        lt_min_iff.mpr ⟨(hwindow u huI).2, hu.2⟩⟩
    simpa [hEq.eq_of_nhds] using
      ((hwinSol w).2 x (hwindow x hx)).congr_of_eventuallyEq hEq
  refine ⟨X, hX₀, hX, ?_⟩
  intro Y hY₀ hY x hx
  let w := window x hx
  obtain ⟨K, hK, hLip, hGrow⟩ := hCompact w.2.2.2
  have hEq : EqOn X Y (Ioo w.1.1 w.1.2) := by
    apply ODE_solution_unique_of_mem_Ioo (K := K) (v := F) (s := fun _ ↦ univ)
      (t₀ := t₀)
    · intro t ht
      exact (hLip t (Ioo_subset_Icc_self ht)).lipschitzOnWith
    · exact ⟨w.2.1, w.2.2.1⟩
    · intro t ht
      exact ⟨hX t (w.2.2.2 (Ioo_subset_Icc_self ht)), mem_univ _⟩
    · intro t ht
      exact ⟨hY t (w.2.2.2 (Ioo_subset_Icc_self ht)), mem_univ _⟩
    · exact hX₀.trans hY₀.symm
  exact hEq (hwindow x hx)

private theorem contDiffOn_two_of_phase
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} (hI : IsOpen I) {y v h : ℝ → E}
    (hy : ∀ x ∈ I, HasDerivAt y (v x) x)
    (hv : ∀ x ∈ I, HasDerivAt v (h x) x)
    (hh : ContinuousOn h I) :
    ContDiffOn ℝ 2 y I := by
  have hv_diff : DifferentiableOn ℝ v I :=
    fun x hx ↦ (hv x hx).differentiableAt.differentiableWithinAt
  have hv_cd : ContDiffOn ℝ 1 v I := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hI).2 ⟨hv_diff, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact hh.congr fun x hx ↦ (hv x hx).deriv
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hI).2 ⟨?_, ?_, ?_⟩
  · exact fun x hx ↦ (hy x hx).differentiableAt.differentiableWithinAt
  · simp
  · exact hv_cd.congr fun x hx ↦ (hy x hx).deriv

private theorem hasDerivAt_fst_of_prod
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : ℝ → E × G} {x : ℝ} {a : E} {b : G}
    (hX : HasDerivAt X (a, b) x) : HasDerivAt (fun t ↦ (X t).1) a x := by
  have h := (ContinuousLinearMap.fst ℝ E G).hasFDerivAt.comp x hX.hasFDerivAt
  change HasDerivAt (Prod.fst ∘ X) a x
  simpa using h.hasDerivAt

private theorem hasDerivAt_snd_of_prod
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : ℝ → E × G} {x : ℝ} {a : E} {b : G}
    (hX : HasDerivAt X (a, b) x) : HasDerivAt (fun t ↦ (X t).2) b x := by
  have h := (ContinuousLinearMap.snd ℝ E G).hasFDerivAt.comp x hX.hasFDerivAt
  change HasDerivAt (Prod.snd ∘ X) b x
  simpa using h.hasDerivAt

private theorem exists_unique_linearState
    {𝔸 : Type*} [RCLike 𝔸]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝔸} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : 𝔸) :
    ∃ X : ℝ → 𝔸 × 𝔸,
      X x₀ = (y₀, v₀) ∧
      (∀ x ∈ I, HasDerivAt X
        (X x |>.2, -f x * (X x |>.2) - g x * (X x |>.1)) x) ∧
      ∀ Y : ℝ → 𝔸 × 𝔸,
        Y x₀ = (y₀, v₀) →
        (∀ x ∈ I, HasDerivAt Y
          (Y x |>.2, -f x * (Y x |>.2) - g x * (Y x |>.1)) x) →
        EqOn X Y I := by
  let F : ℝ → (𝔸 × 𝔸) → (𝔸 × 𝔸) :=
    fun t z ↦ (z.2, -f t * z.2 - g t * z.1)
  apply exists_unique_stateSolutionOn hI hIc (F := F) (t₀ := x₀)
  · intro z
    exact continuousOn_const.prodMk
      ((hf.neg.mul continuousOn_const).sub (hg.mul continuousOn_const))
  · intro A B hABI
    obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.mono hABI)
    obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.mono hABI)
    let K : ℝ≥0 := ⟨1 + |Mf| + |Mg|, by positivity⟩
    have hKLip : ∀ t ∈ Icc A B, LipschitzWith K (F t) := by
      intro t ht
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simp only [dist_eq_norm]
      have h₁ : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by
        simpa using norm_fst_le (z - w)
      have h₂ : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by
        simpa using norm_snd_le (z - w)
      have hf' : ‖f t‖ ≤ |Mf| := (hMf t ht).trans (le_abs_self Mf)
      have hg' : ‖g t‖ ≤ |Mg| := (hMg t ht).trans (le_abs_self Mg)
      have hsecond :
          ‖(-f t * z.2 - g t * z.1) - (-f t * w.2 - g t * w.1)‖ ≤
            (1 + |Mf| + |Mg|) * ‖z - w‖ := by
        calc
          ‖(-f t * z.2 - g t * z.1) - (-f t * w.2 - g t * w.1)‖ =
              ‖-f t * (z.2 - w.2) - g t * (z.1 - w.1)‖ := by
                congr 1
                ring
          _ ≤ ‖-f t * (z.2 - w.2)‖ + ‖g t * (z.1 - w.1)‖ := norm_sub_le _ _
          _ = ‖f t‖ * ‖z.2 - w.2‖ + ‖g t‖ * ‖z.1 - w.1‖ := by
            simp only [norm_mul, norm_neg]
          _ ≤ |Mf| * ‖z - w‖ + |Mg| * ‖z - w‖ := by
            gcongr
          _ ≤ (1 + |Mf| + |Mg|) * ‖z - w‖ := by
            have hn : 0 ≤ ‖z - w‖ := norm_nonneg _
            nlinarith
      simp only [F]
      apply max_le
      · have hKone : 1 ≤ (K : ℝ) := by
          change 1 ≤ 1 + |Mf| + |Mg|
          nlinarith [abs_nonneg Mf, abs_nonneg Mg]
        calc
          ‖z.2 - w.2‖ ≤ ‖z - w‖ := h₂
          _ ≤ (K : ℝ) * ‖z - w‖ := by
            nlinarith [norm_nonneg (z - w)]
      · change
          ‖(-f t * z.2 - g t * z.1) - (-f t * w.2 - g t * w.1)‖ ≤
            (1 + |Mf| + |Mg|) * ‖z - w‖
        exact hsecond
    refine ⟨K, ?_, hKLip, ?_⟩
    · change 0 < (1 + |Mf| + |Mg| : ℝ)
      positivity
    intro t ht z
    have hdist := (hKLip t ht).dist_le_mul z 0
    simpa [dist_eq_norm, F, Prod.norm_mk] using hdist
  · exact hx₀

private theorem exists_unique_linearIVP
    {𝔸 : Type*} [RCLike 𝔸]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝔸} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : 𝔸) :
    ∃ y v : ℝ → 𝔸,
      y x₀ = y₀ ∧ v x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt y (v x) x) ∧
      (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) ∧
      ContDiffOn ℝ 2 y I ∧
      ∀ y' v' : ℝ → 𝔸,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn y y' I ∧ EqOn v v' I := by
  obtain ⟨X, hX₀, hX, hXunique⟩ := exists_unique_linearState hI hIc hf hg hx₀ y₀ v₀
  let y : ℝ → 𝔸 := fun x ↦ (X x).1
  let v : ℝ → 𝔸 := fun x ↦ (X x).2
  have hy : ∀ x ∈ I, HasDerivAt y (v x) x := by
    intro x hx
    exact hasDerivAt_fst_of_prod (hX x hx)
  have hv : ∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x := by
    intro x hx
    exact hasDerivAt_snd_of_prod (hX x hx)
  have hycont : ContinuousOn y I := HasDerivAt.continuousOn hy
  have hvcont : ContinuousOn v I := HasDerivAt.continuousOn hv
  have hRhs : ContinuousOn (fun x ↦ -f x * v x - g x * y x) I :=
    (hf.neg.mul hvcont).sub (hg.mul hycont)
  have hyC2 : ContDiffOn ℝ 2 y I :=
    contDiffOn_two_of_phase hI hy hv hRhs
  refine ⟨y, v, congrArg Prod.fst hX₀, congrArg Prod.snd hX₀, hy, hv, hyC2, ?_⟩
  intro y' v' hy'₀ hv'₀ hy' hv'
  let Y : ℝ → 𝔸 × 𝔸 := fun x ↦ (y' x, v' x)
  have hY₀ : Y x₀ = (y₀, v₀) := by simp [Y, hy'₀, hv'₀]
  have hY : ∀ x ∈ I, HasDerivAt Y
      (Y x |>.2, -f x * (Y x |>.2) - g x * (Y x |>.1)) x := by
    intro x hx
    simpa only [Y] using (hy' x hx).prodMk (hv' x hx)
  have hEq := hXunique Y hY₀ hY
  constructor
  · intro x hx
    exact congrArg Prod.fst (hEq hx)
  · intro x hx
    exact congrArg Prod.snd (hEq hx)

/-- Existence and `EqOn` uniqueness for a complex second-order linear phase IVP.-/
theorem exists_unique_complexLinearIVP
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : ℂ) :
    ∃ y v : ℝ → ℂ,
      y x₀ = y₀ ∧ v x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt y (v x) x) ∧
      (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) ∧
      ContDiffOn ℝ 2 y I ∧
      ∀ y' v' : ℝ → ℂ,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn y y' I ∧ EqOn v v' I :=
  exists_unique_linearIVP hI hIc hf hg hx₀ y₀ v₀

/-- Existence and `EqOn` uniqueness for a real second-order linear phase IVP.-/
theorem exists_unique_realLinearIVP
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : ℝ) :
    ∃ y v : ℝ → ℝ,
      y x₀ = y₀ ∧ v x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt y (v x) x) ∧
      (∀ x ∈ I, HasDerivAt v (-f x * v x - g x * y x) x) ∧
      ContDiffOn ℝ 2 y I ∧
      ∀ y' v' : ℝ → ℝ,
        y' x₀ = y₀ → v' x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt y' (v' x) x) →
        (∀ x ∈ I, HasDerivAt v' (-f x * v' x - g x * y' x) x) →
        EqOn y y' I ∧ EqOn v v' I :=
  exists_unique_linearIVP hI hIc hf hg hx₀ y₀ v₀

private theorem exists_unique_secondOrderLinear
    {𝔸 : Type*} [RCLike 𝔸]
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝔸} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : 𝔸) :
    ∃ y : ℝ → 𝔸,
      ContDiffOn ℝ 2 y I ∧
      y x₀ = y₀ ∧ deriv y x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x) ∧
      ∀ z : ℝ → 𝔸,
        ContDiffOn ℝ 2 z I →
        z x₀ = y₀ → deriv z x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt (deriv z)
          (-f x * deriv z x - g x * z x) x) →
        EqOn y z I := by
  obtain ⟨y, v, hy₀, hv₀, hy, hv, hyC2, hunique⟩ :=
    exists_unique_linearIVP hI hIc hf hg hx₀ y₀ v₀
  have hdy : EqOn (deriv y) v I := fun x hx ↦ (hy x hx).deriv
  have hddy : ∀ x ∈ I, HasDerivAt (deriv y)
      (-f x * deriv y x - g x * y x) x := by
    intro x hx
    have hev : deriv y =ᶠ[nhds x] v := by
      filter_upwards [hI.mem_nhds hx] with u hu
      exact hdy hu
    simpa only [hev.eq_of_nhds] using (hv x hx).congr_of_eventuallyEq hev
  refine ⟨y, hyC2, hy₀, (hdy hx₀).trans hv₀, hddy, ?_⟩
  intro z hzC2 hz₀ hdz₀ hzEq
  have hzFirst : ∀ x ∈ I, HasDerivAt z (deriv z x) x := by
    intro x hx
    exact (((hzC2.differentiableOn (by norm_num)) x hx).differentiableAt
      (hI.mem_nhds hx)).hasDerivAt
  exact (hunique z (deriv z) hz₀ hdz₀ hzFirst hzEq).1

/-- Olver's source-form complex second-order linear IVP theorem.-/
theorem exists_unique_complexSecondOrderLinear
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : ℂ) :
    ∃ y : ℝ → ℂ,
      ContDiffOn ℝ 2 y I ∧
      y x₀ = y₀ ∧ deriv y x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x) ∧
      ∀ z : ℝ → ℂ,
        ContDiffOn ℝ 2 z I →
        z x₀ = y₀ → deriv z x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt (deriv z)
          (-f x * deriv z x - g x * z x) x) →
        EqOn y z I :=
  exists_unique_secondOrderLinear hI hIc hf hg hx₀ y₀ v₀

/-- Olver's source-form real second-order linear IVP theorem.-/
theorem exists_unique_realSecondOrderLinear
    {I : Set ℝ} (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) (y₀ v₀ : ℝ) :
    ∃ y : ℝ → ℝ,
      ContDiffOn ℝ 2 y I ∧
      y x₀ = y₀ ∧ deriv y x₀ = v₀ ∧
      (∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x) ∧
      ∀ z : ℝ → ℝ,
        ContDiffOn ℝ 2 z I →
        z x₀ = y₀ → deriv z x₀ = v₀ →
        (∀ x ∈ I, HasDerivAt (deriv z)
          (-f x * deriv z x - g x * z x) x) →
        EqOn y z I :=
  exists_unique_secondOrderLinear hI hIc hf hg hx₀ y₀ v₀

private theorem infinite_secondOrderLinearSolutions
    {𝔸 : Type*} [RCLike 𝔸]
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → 𝔸} (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    Set.Infinite {y : ℝ → 𝔸 |
      ContDiffOn ℝ 2 y I ∧
      ∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x} := by
  classical
  obtain ⟨x₀, hx₀⟩ := hIne
  let S : Set (ℝ → 𝔸) := {y | ContDiffOn ℝ 2 y I ∧
    ∀ x ∈ I, HasDerivAt (deriv y) (-f x * deriv y x - g x * y x) x}
  have hsol : ∀ c : 𝔸, ∃ y : ℝ → 𝔸, y ∈ S ∧ y x₀ = c := by
    intro c
    obtain ⟨y, hyC2, hy₀, hdy₀, hyEq, hyUnique⟩ :=
      exists_unique_secondOrderLinear hI hIc hf hg hx₀ c 0
    exact ⟨y, ⟨hyC2, hyEq⟩, hy₀⟩
  choose sol hsolMem hsolVal using hsol
  let Φ : 𝔸 → S := fun c ↦ ⟨sol c, hsolMem c⟩
  have hΦ : Injective Φ := by
    intro c d hcd
    have h := congrArg (fun z : S ↦ z.1 x₀) hcd
    simpa only [Φ, hsolVal] using h
  exact Set.infinite_coe_iff.mp (Infinite.of_injective Φ hΦ)

/-- There are infinitely many complex `C²` solutions of the homogeneous equation.-/
theorem infinite_complexSecondOrderLinearSolutions
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℂ} (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    Set.Infinite {y : ℝ → ℂ |
      ContDiffOn ℝ 2 y I ∧
      ∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x} :=
  infinite_secondOrderLinearSolutions hIne hI hIc hf hg

/-- There are infinitely many real `C²` solutions of the homogeneous equation.-/
theorem infinite_realSecondOrderLinearSolutions
    {I : Set ℝ} (hIne : I.Nonempty) (hI : IsOpen I) (hIc : IsPreconnected I)
    {f g : ℝ → ℝ} (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    Set.Infinite {y : ℝ → ℝ |
      ContDiffOn ℝ 2 y I ∧
      ∀ x ∈ I, HasDerivAt (deriv y)
        (-f x * deriv y x - g x * y x) x} :=
  infinite_secondOrderLinearSolutions hIne hI hIc hf hg

end LMLF.ODE
