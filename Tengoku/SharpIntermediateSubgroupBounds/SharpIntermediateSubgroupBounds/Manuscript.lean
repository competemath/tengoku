import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Gaussian
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.PrimePower
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.GroupMain
import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Escape

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Manuscript-facing sharpness certificates

This module states the elementary-abelian sharpness family directly in the
language of subgroup intervals.  It is deliberately a thin bridge: the exact
finite counts come from `PrimePower`, while the analytic limits and optimality
statements come from `Gaussian`.
-/

namespace SharpIntermediateSubgroupBounds

open Filter

noncomputable section

noncomputable local instance manuscriptSubgroupIntervalFintype
    {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype (Set.Ici H) :=
  Fintype.ofFinite _

/-- The standard elementary-abelian group of rank `n` over `ZMod p`.-/
abbrev ElementaryAbelianGroup (p n : ℕ) :=
  Multiplicative (Fin n → ZMod p)

/-- The closed subgroup interval above the trivial subgroup in the standard
elementary-abelian group.-/
abbrev elementaryAbelianInterval (p n : ℕ) :=
  Set.Ici (⊥ : Subgroup (ElementaryAbelianGroup p n))

/-- Exact subgroup-interval count for the elementary-abelian witness family.-/
theorem manuscript_elementaryAbelian_interval_card_eq (p n : ℕ)
    [Fact p.Prime] :
    Fintype.card (elementaryAbelianInterval p n) = totalQBinom p n :=
  elementaryAbelian_interval_card_eq_totalQBinom p n

/-- The index of the trivial subgroup in the even-rank elementary-abelian
witness is exactly `p^(2a)`.-/
theorem manuscript_elementaryAbelian_bottom_index (p a : ℕ)
    [Fact p.Prime] :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index = p ^ (2 * a) := by
  rw [Subgroup.index_bot]
  simp [ZMod.card]

/-- In every positive even rank, the least prime divisor of the witness
index is the prescribed prime `p`.-/
theorem manuscript_elementaryAbelian_bottom_index_minFac (p a : ℕ)
    [Fact p.Prime] (ha : 0 < a) :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index.minFac = p := by
  rw [manuscript_elementaryAbelian_bottom_index p a]
  exact (Fact.out : p.Prime).pow_minFac (by omega)

/-- The manuscript's index-logarithmic scale specializes to the centered
power `p^(a²)` on the even-rank elementary-abelian family.-/
theorem manuscript_elementaryAbelian_indexLog_rpow_eq (p a : ℕ)
    [Fact p.Prime] :
    (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
        (indexLog p
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)) =
      (p : ℝ) ^ (a * a) := by
  rw [manuscript_elementaryAbelian_bottom_index]
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  rw [indexLog, Nat.cast_pow, Real.log_pow]
  change ((p : ℝ) ^ (2 * a : ℕ) : ℝ) ^
      ((((2 * a : ℕ) : ℝ) * Real.log (p : ℝ) /
        Real.log (p : ℝ)) / 4) = (p : ℝ) ^ (a * a)
  rw [mul_div_cancel_right₀ _ hlog]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  rw [show ((2 * a : ℕ) : ℝ) * (((2 * a : ℕ) : ℝ) / 4) =
      ((a * a : ℕ) : ℝ) by
    push_cast
    ring]
  exact Real.rpow_natCast (p : ℝ) (a * a)

/-- The logarithm base `p` of the exact prime power `p^n` is `n`.-/
theorem manuscript_indexLog_primePower (p n : ℕ) (hp : 1 < p) :
    indexLog p (p ^ n) = n := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hpR).ne'
  rw [indexLog, Nat.cast_pow, Real.log_pow]
  exact mul_div_cancel_right₀ (n : ℝ) hlog

/-- On a prime power, the manuscript's real envelope is exactly the real
cast of the rational finite packing sum.-/
theorem manuscript_primePowerU_eq_ratCast_finiteUQ
    (p n : ℕ) (hp : 1 < p) :
    primePowerU p n = ((finiteUQ (p ^ n) p : ℚ) : ℝ) := by
  rw [ratCast_finiteUQ_eq_finiteThetaSum hp (pow_pos (by omega) _),
    manuscript_indexLog_primePower p n hp]
  rw [primePowerU, finiteThetaSum]
  simp only [Nat.floor_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ ↦
    (p : ℝ) ^ (r * (n - r)) * (gammaR (p : ℝ) r)⁻¹)]
  apply Finset.sum_congr rfl
  intro r hrmem
  have hr : r ≤ n := by
    simp only [Finset.mem_range] at hrmem
    omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  rw [show Real.log (p : ℝ) * (r : ℝ) *
      ((n : ℝ) - (r : ℝ)) =
        Real.log (p : ℝ) * ((r * (n - r) : ℕ) : ℝ) by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring]
  have hexp : Real.exp
      (Real.log (p : ℝ) * ((r * (n - r) : ℕ) : ℝ)) =
      (p : ℝ) ^ (r * (n - r)) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hpR]
  rw [hexp]
  ring

/-- The normalized number of subgroups of the elementary-abelian group of
even rank tends to the sharp Euler--theta constant.-/
theorem manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using
    gaussian_even_rank_asymptotic (Fact.out : p.Prime).two_le

/-- Literal displayed ratio: the interval count divided by the
index-logarithmic scale tends to the sharp constant.-/
theorem manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
          (indexLog p
            (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)))
      atTop (nhds (sharpConstant (p : ℝ))) := by
  apply (manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
    (p := p)).congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    dsimp only
    rw [manuscript_elementaryAbelian_indexLog_rpow_eq p a]
    simp only [div_eq_mul_inv, inv_pow]
    ring

/-- The elementary-abelian subgroup interval asymptotically exhausts the
finite prime-power envelope.-/
theorem manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        primePowerU p (2 * a)) atTop (nhds 1) := by
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using
    gaussian_total_div_primePowerU_tendsto_one (Fact.out : p.Prime).two_le

/-- Literal finite-sum ratio, using the rational packing envelope evaluated
at the witness index.-/
theorem manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by
  apply (manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
    (p := p)).congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    dsimp only
    rw [manuscript_elementaryAbelian_bottom_index p a,
      manuscript_primePowerU_eq_ratCast_finiteUQ p (2 * a)
        (Fact.out : p.Prime).one_lt]

/-- Any constant which bounds every normalized elementary-abelian subgroup
interval is at least the sharp Euler--theta constant.-/
theorem manuscript_sharpConstant_le_of_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply sharpConstant_le_of_even_rank_bound (Fact.out : p.Prime).two_le
  intro a
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using hC a

/-- Manuscript-domain form of constant optimality.  Only positive ranks are
assumed, exactly matching the `index > 1` domain of the sharp interval bound.-/
theorem manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply le_of_tendsto
    (manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant (p := p))
  exact Filter.eventually_atTop.2 ⟨1, fun a ha ↦ hC a (by omega)⟩

/-- The exponent `1/4` cannot be decreased, already on the standard
elementary-abelian subgroup intervals.-/
theorem manuscript_no_subquarter_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ,
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  intro h
  apply no_subquarter_rpow_bound (Fact.out : p.Prime).two_le halpha
  intro a
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using h a

/-- Manuscript-domain form of exponent optimality.  A putative bound only on
positive ranks can be enlarged at the single rank-zero term, contradicting
the all-rank version above.-/
theorem manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ, 0 < a →
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  intro hpositive
  apply manuscript_no_subquarter_elementaryAbelian_rpow_bound
    (p := p) (alpha := alpha) (C := max C 1) halpha
  intro a
  by_cases ha : a = 0
  · subst a
    rw [manuscript_elementaryAbelian_interval_card_eq]
    simp [totalQBinom]
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hpow : 0 ≤ Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) :=
      Real.rpow_nonneg (by positivity) _
    exact (hpositive a haPos).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) hpow)

/-- Every fixed index layer of the elementary-abelian witness attains the
Gaussian-binomial layer bound.-/
theorem manuscript_elementaryAbelian_fixed_layer_eq (p n k : ℕ)
    [Fact p.Prime] (hk : k ≤ n) :
    (primePowerLayer p k
      (⊥ : Subgroup (ElementaryAbelianGroup p n)) ⊤).card = qBinom p n k :=
  elementaryAbelian_primePowerLayer_card_eq_qBinom p n k hk

/-- A normal inclusion with elementary-abelian quotient has the exact same
closed-interval count as the standard witness.-/
theorem manuscript_normal_elementaryAbelian_quotient_interval_card_eq
    {G : Type*} [Group G] [Fintype G] {p n : ℕ}
    (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* ElementaryAbelianGroup p n) [Fact p.Prime] :
    Fintype.card (Set.Ici H) = totalQBinom p n :=
  normal_elementaryAbelian_quotient_interval_card_eq H e

/-! ## Literal generating-coset sharpness witness -/

/-- In the elementary-abelian witness with trivial bottom subgroup,
`generatedFrom` is exactly additive generation of the corresponding frame.-/
theorem manuscript_generatedFrom_bot_eq_top_iff_addClosure
    (p r : ℕ) [Fact p.Prime]
    (x : Fin r → ElementaryAbelianGroup p r) :
    generatedFrom (⊥ : Subgroup (ElementaryAbelianGroup p r)) x = ⊤ ↔
      AddSubgroup.closure (Set.range (fun i ↦ Multiplicative.toAdd (x i))) = ⊤ := by
  rw [generatedFrom, bot_sup_eq]
  have hrange : Multiplicative.ofAdd ⁻¹' Set.range x =
      Set.range (fun i ↦ Multiplicative.toAdd (x i)) := by
    ext y
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg Multiplicative.toAdd hi⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
  constructor
  · intro h
    have h' := congrArg Subgroup.toAddSubgroup' h
    simpa [Subgroup.toAddSubgroup'_closure, hrange] using h'
  · intro h
    apply Subgroup.toAddSubgroup'.injective
    simpa [Subgroup.toAddSubgroup'_closure, hrange] using h

/-- Raw generating tuples at the elementary-abelian bottom/top interval are
canonically the generating frames counted in Remark 2.4.-/
def manuscript_rawRelGenEquivGeneratingFrames (p r : ℕ) [Fact p.Prime] :
    RawRelGen (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r ≃
      GeneratingFramesFinZMod p r where
  toFun x := ⟨fun i ↦ Multiplicative.toAdd (x.1 i),
    (manuscript_generatedFrom_bot_eq_top_iff_addClosure p r x.1).mp x.2.2⟩
  invFun s := ⟨fun i ↦ Multiplicative.ofAdd (s.1 i),
    fun _ ↦ trivial,
    (manuscript_generatedFrom_bot_eq_top_iff_addClosure p r _).mpr s.2⟩
  left_inv := by intro x; apply Subtype.ext; rfl
  right_inv := by intro s; apply Subtype.ext; rfl

/-- Exact manuscript Remark 2.4 in its coset-tuple formulation.-/
theorem manuscript_cosetRelGen_elementaryAbelian_card_cast_eq_gammaR
    (p r : ℕ) [Fact p.Prime] :
    (Nat.card (CosetRelGen
      (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) : ℝ) =
      (p : ℝ) ^ (r * r) * gammaR (p : ℝ) r := by
  have hraw := rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
    (G := ElementaryAbelianGroup p r)
    (H := (⊥ : Subgroup (ElementaryAbelianGroup p r))) (K := ⊤) bot_le r
  have hcard : Nat.card (CosetRelGen
      (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) =
      Nat.card (GeneratingFramesFinZMod p r) := by
    calc
      Nat.card (CosetRelGen
          (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) =
          Nat.card (RawRelGen
            (⊥ : Subgroup (ElementaryAbelianGroup p r)) ⊤ r) := by
        simpa using hraw.symm
      _ = Nat.card (GeneratingFramesFinZMod p r) :=
        Nat.card_congr (manuscript_rawRelGenEquivGeneratingFrames p r)
  rw [hcard]
  exact card_generatingFrames_fin_zmod_cast_eq_gammaR p r

end

end SharpIntermediateSubgroupBounds
