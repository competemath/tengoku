/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Compose
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.PoweringBound
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Preprocess
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Amplification

/-!
# One round of Dinur's amplification

Preprocess, power, compose: the three steps assembled into a single
transformation of constraint graphs over a fixed alphabet, packaged as an
`Amplifier`. Given an expander family, the round

* preserves satisfiability,
* multiplies the number of edges by a constant, and
* at least doubles the unsatisfiability value until it reaches a universal
  threshold.

The alphabet is the one the composition produces, `Alpha ReadIdx`. Powering
blows it up to `KOpinion`, whose size is a fixed function of the powering
length and the preprocessed degree; composition brings it back.

The only free parameter is the killing rate `q`. The powering bound's slope
grows linearly in `q` while every other loss — preprocessing, composition —
is a constant, so a large enough `q` makes the round double the value.
`q` is chosen by an Archimedean argument, and the threshold is any rational
below the powering bound's floor.

## Main definitions

- `Complexity.DinurAlpha` — the fixed alphabet
- `Complexity.Dinur.step` — one round
- `Complexity.Dinur.amplifier` — the round as an `Amplifier`

## Main results

- `Complexity.Dinur.numEdges_step` — the edge count grows by a constant factor
- `Complexity.Dinur.satisfiable_step` — completeness
- `Complexity.Dinur.min_le_unsatVal_step` — the value at least doubles, up to
  the threshold
-/

@[expose] public section

namespace Complexity

open BooleanAnalysis

/-- The fixed alphabet of the amplification: the composition's alphabet. -/
abbrev DinurAlpha : Type := MultiTest.Alpha ReadIdx

namespace Dinur

variable (E : ExpanderFamily)

/-! ### The powered alphabet's size -/

/-- The degree after preprocessing. -/
def powDeg : ℕ := 2 + 2 * E.degree

/-- The number of walks of length at most `T` out of a vertex. -/
def walkCount (T : ℕ) : ℕ := ∑ ℓ ∈ Finset.range (T + 1), powDeg E ^ ℓ

/-- The number of powered labels, as bits of a one-hot encoding. -/
def bits (T : ℕ) : ℕ := Fintype.card DinurAlpha ^ walkCount E T

theorem card_varWalk (G : ConstraintGraph DinurAlpha) (T : ℕ) :
    Fintype.card (VarWalk (G.preprocess E).graph T) = walkCount E T := by
  have hD : Fintype.card (G.preprocess E).graph.D = powDeg E := by
    have := G.deg_preprocess E
    rw [RegGraph.deg] at this
    exact this
  rw [walkCount, ← Fin.sum_univ_eq_sum_range (fun ℓ => powDeg E ^ ℓ) (T + 1)]
  show Fintype.card (Σ ℓ : Fin (T + 1), Fin ℓ.val → (G.preprocess E).graph.D) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin, hD]

theorem card_kOpinion (G : ConstraintGraph DinurAlpha) (T : ℕ) :
    Fintype.card (KOpinion (G.preprocess E).graph T DinurAlpha) = bits E T := by
  show Fintype.card (VarWalk (G.preprocess E).graph T → DinurAlpha) = _
  rw [Fintype.card_fun, card_varWalk, bits]

/-! ### The encoding -/

theorem basisVec_injective (n : ℕ) : Function.Injective (basisVec (n := n)) := by
  intro i j hij
  have h := congrFun hij i
  by_contra hne
  simp only [basisVec, ite_true, ite_eq_right hne] at h
  exact absurd h (by decide)

/-- The encoding of a powered label: the basis vector at its index. -/
noncomputable def enc (G : ConstraintGraph DinurAlpha) (T : ℕ)
    (σ : KOpinion (G.preprocess E).graph T DinurAlpha) : Cube (bits E T) :=
  basisVec (Fin.cast (card_kOpinion E G T) (Fintype.equivFin _ σ))

theorem enc_injective (G : ConstraintGraph DinurAlpha) (T : ℕ) :
    Function.Injective (enc E G T) := by
  intro σ τ h
  have h1 := basisVec_injective _ h
  have h2 := Fin.cast_injective _ h1
  exact (Fintype.equivFin _).injective h2

/-! ### One round -/

/-- The alphabet's size, the `K` of the powering parameters.

Deliberately a `def` and not an `abbrev`. The alphabet has `2^23` symbols, and
`K` occurs inside `powT K q`, which is itself an exponent; letting a tactic
unfold `K` to a numeral there produces terms far too large to elaborate. -/
def K : ℕ := Fintype.card DinurAlpha

theorem one_le_K : 1 ≤ K := Fintype.card_pos

theorem card_dinurAlpha_eq : Fintype.card DinurAlpha = K := rfl

/-- **One round of amplification** with killing rate `q`. -/
noncomputable def step (q : ℕ) (hq : 0 < q) (G : ConstraintGraph DinurAlpha) :
    ConstraintGraph DinurAlpha :=
  (((G.preprocess E).killedPow q (powT K q) hq).compose (enc E G (powT K q))).toGraph

/-- The constant factor by which a round multiplies the edge count. -/
def edgeFactor (q : ℕ) : ℕ :=
  2 * (powDeg E ^ powT K q * q ^ powT K q) * 2 ^ Tester.ROf (bits E (powT K q)) * 22

theorem numEdges_step (q : ℕ) (hq : 0 < q) (G : ConstraintGraph DinurAlpha) :
    (step E q hq G).numEdges = edgeFactor E q * G.numEdges := by
  rw [step, MultiTest.numEdges_toGraph, card_readIdx, RegCSP.card_dart,
    RegCSP.card_dart_killedPow, G.order_preprocess, G.deg_preprocess, edgeFactor]
  show 2 * G.numEdges * ((2 + 2 * E.degree) ^ powT K q * q ^ powT K q)
    * 2 ^ Tester.ROf (bits E (powT K q)) * 22 = _
  rw [powDeg]
  ring

theorem satisfiable_step (q : ℕ) (hq : 0 < q) (G : ConstraintGraph DinurAlpha)
    (h : G.Satisfiable) : (step E q hq G).Satisfiable :=
  RegCSP.satisfiable_compose _ _
    (RegCSP.satisfiable_killedPow_of_satisfiable _ _ _ _
      (G.satisfiable_preprocess_of_satisfiable E h))

/-! ### The value -/

theorem preprocessLam_nonneg : 0 ≤ ConstraintGraph.preprocessLam E := by
  have := E.lam_nonneg
  rw [ConstraintGraph.preprocessLam]
  positivity

theorem preprocessConst_pos : 0 < ConstraintGraph.preprocessConst E DinurAlpha := by
  have hd : (0 : ℝ) < E.degree := by exact_mod_cast E.degree_pos
  have hl : 0 < 1 - E.lam := by linarith [E.lam_lt_one]
  rw [ConstraintGraph.preprocessConst, ConstraintGraph.reduceConst]
  have : 0 < min (1 : ℝ) ((1 - E.lam) * (E.degree : ℝ) / (Fintype.card DinurAlpha : ℝ)) := by
    apply lt_min one_pos
    positivity
  positivity

/-! ### Choosing the killing rate -/

/-- **A killing rate that doubles the value.** -/
theorem exists_q : ∃ q : ℕ, 2 ≤ q ∧ 1408
    ≤ RegCSP.powSlope (RegCSP.powConst q DinurAlpha) (powT K q) (ConstraintGraph.preprocessLam E)
        * ConstraintGraph.preprocessConst E DinurAlpha := by
  have hpc := preprocessConst_pos E
  have hl1 := ConstraintGraph.preprocessLam_lt_one E
  have hK0 : (0 : ℝ) < K := by exact_mod_cast one_le_K
  have hs : 0 < slopeUnit (K : ℝ) (ConstraintGraph.preprocessLam E) := by
    rw [slopeUnit]
    have : 0 < 1 - ConstraintGraph.preprocessLam E := by linarith
    positivity
  obtain ⟨n, hn⟩ := exists_nat_ge (1408 / (slopeUnit (K : ℝ) (ConstraintGraph.preprocessLam E)
    * ConstraintGraph.preprocessConst E DinurAlpha))
  refine ⟨n + 2, by omega, ?_⟩
  have hslope := slopeUnit_mul_le_powSlope (q := n + 2) one_le_K (by omega) hl1
  have hcast : (((n + 2 : ℕ) : ℝ) - 1) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hslope
  have hpc' : RegCSP.powConst (n + 2) DinurAlpha = ((n : ℝ) + 1) / (4 * (K : ℝ) ^ 2) := by
    rw [RegCSP.powConst, card_dinurAlpha_eq]
    push_cast
    ring
  rw [hpc']
  rw [div_le_iff₀ (by positivity)] at hn
  calc (1408 : ℝ)
      ≤ n * (slopeUnit (K : ℝ) (ConstraintGraph.preprocessLam E)
          * ConstraintGraph.preprocessConst E DinurAlpha) := hn
    _ ≤ slopeUnit (K : ℝ) (ConstraintGraph.preprocessLam E) * ((n : ℝ) + 1)
          * ConstraintGraph.preprocessConst E DinurAlpha := by
        nlinarith [hs, hpc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hslope hpc.le

/-- The chosen killing rate. -/
noncomputable def q₀ : ℕ := Classical.choose (exists_q E)

theorem two_le_q₀ : 2 ≤ q₀ E := (Classical.choose_spec (exists_q E)).1

theorem q₀_spec : 1408
    ≤ RegCSP.powSlope (RegCSP.powConst (q₀ E) DinurAlpha) (powT K (q₀ E))
        (ConstraintGraph.preprocessLam E) * ConstraintGraph.preprocessConst E DinurAlpha :=
  (Classical.choose_spec (exists_q E)).2

/-- The powering floor at the chosen rate. -/
noncomputable def floor₀ : ℝ :=
  RegCSP.powFloor (RegCSP.powConst (q₀ E) DinurAlpha) (powT K (q₀ E))
    (ConstraintGraph.preprocessLam E)

theorem floor₀_pos : 0 < floor₀ E := by
  rw [floor₀, RegCSP.powFloor]
  have hl : 0 < 1 - ConstraintGraph.preprocessLam E := by
    linarith [ConstraintGraph.preprocessLam_lt_one E]
  have hc : 0 < RegCSP.powConst (q₀ E) DinurAlpha := by
    rw [RegCSP.powConst, card_dinurAlpha_eq]
    have h2 : (2 : ℝ) ≤ q₀ E := by exact_mod_cast two_le_q₀ E
    have hK0 : (0 : ℝ) < K := by exact_mod_cast one_le_K
    apply div_pos
    · linarith
    · have hsq : (0 : ℝ) < (K : ℝ) ^ 2 := pow_pos hK0 2
      linarith
  have hT : (0 : ℝ) < powT K (q₀ E) := by
    have hpos : 0 < powT K (q₀ E) := by
      rw [powT]
      have h1 : 1 ≤ K := one_le_K
      have h2 : 2 ≤ q₀ E := two_le_q₀ E
      have h3 : 1 ≤ q₀ E - 1 := by omega
      calc 0 < 2 * (4 * 1 * 1) := by norm_num
        _ ≤ 2 * (4 * K * (q₀ E - 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h3)
    exact_mod_cast hpos
  have hT2 : 0 < (powT K (q₀ E) : ℝ) ^ 2 := pow_pos hT 2
  exact div_pos (div_pos (pow_pos hc 2) hT2)
    (add_pos (add_pos hc (mul_pos two_pos hT2)) (div_pos (mul_pos two_pos hT) hl))

/-- **A rational threshold** below the floor (after the composition's loss) and
below one. -/
theorem exists_gap : ∃ g : ℚ, 0 < g ∧ g ≤ 1 ∧ (g : ℝ) ≤ floor₀ E / 704 := by
  have h : (0 : ℝ) < min (floor₀ E / 704) 1 := lt_min (by linarith [floor₀_pos E]) one_pos
  obtain ⟨g, hg0, hg1⟩ := exists_rat_btwn h
  refine ⟨g, by exact_mod_cast hg0, ?_, ?_⟩
  · have : (g : ℝ) ≤ 1 := le_trans hg1.le (min_le_right _ _)
    exact_mod_cast this
  · exact le_trans hg1.le (min_le_left _ _)

/-- The chosen threshold. -/
noncomputable def gap₀ : ℚ := Classical.choose (exists_gap E)

theorem gap₀_pos : 0 < gap₀ E := (Classical.choose_spec (exists_gap E)).1
theorem gap₀_le_one : gap₀ E ≤ 1 := (Classical.choose_spec (exists_gap E)).2.1
theorem gap₀_le : ((gap₀ E : ℚ) : ℝ) ≤ floor₀ E / 704 := (Classical.choose_spec (exists_gap E)).2.2

/-- An edgeless graph has value zero. -/
theorem unsatVal_eq_zero_of_numEdges_eq_zero (G : ConstraintGraph DinurAlpha)
    (h : G.numEdges = 0) : G.unsatVal = 0 := by
  refine le_antisymm ?_ G.unsatVal_nonneg
  have a : G.Assignment := fun _ => Classical.arbitrary _
  refine le_trans (G.unsatVal_le a) ?_
  rw [ConstraintGraph.unsatFrac]
  have hz : (G.numEdges : ℚ) = 0 := by rw [h]; norm_num
  rw [hz, div_zero]

/-! ### The amplifier -/

end Dinur

end Complexity
