import Tengoku.TdaLib.TDA.Persistence.FiniteMatchingCost
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite matching costs for real exponents

Pair and boundary distances are raised to a real exponent before summing. The
finite matching family contains the all-unmatched matching, so its infimum is an
attained minimum. At exponents at least one, taking the reciprocal-power root
after minimizing agrees with minimizing the rooted candidate costs.

The supporting powered algebra is defined for real exponents; the persistence
interpretation uses `1 ≤ p`, positive lifetimes, finite deaths and unit mass per
occurrence. `FinitePMatchingCostLaws` supplies rooted distance laws for `1 ≤ p`.
No quotient or metric-space instance on raw occurrence presentations is supplied.
-/

noncomputable section
namespace TDA.Persistence
open scoped Classical

namespace OccurrenceMatching
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Unnormalized sum of powered pair/deletion/insertion distances.
Occurrence multiplicity is unchanged by the exponent.-/
def totalFinitePowerCost (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  M.totalBoundaryCost (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p) (fun j => (diagonalCost (y j)).toReal ^ p)

/--
@isnad1 id=le.0h6v.s5.83d83df95a22 from=translated src=- shape=a793ea67 vocab=3f64e212
-/
theorem totalFinitePowerCost_nonneg (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : 0 ≤ M.totalFinitePowerCost p x y :=
  M.totalBoundaryCost_nonneg _ _ _
    (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)

/--
@isnad1 id=eq.0h5v.s5.c782aa99b130 from=translated src=- shape=b917a964 vocab=301c5996
-/
@[simp] theorem totalFinitePowerCost_one (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    M.totalFinitePowerCost 1 x y = M.totalFiniteCost x y := by
  unfold totalFinitePowerCost totalBoundaryCost totalFiniteCost
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    cases M.finite i <;> simp only [Real.rpow_one]
  · simp only [Real.rpow_one]

/-- Transporting labels preserves each powered coefficient and the complete sum.
@isnad1 id=eq.0h10v.s7.20f576e192e5 from=translated src=- shape=598dd24b vocab=c3df8b84
-/
theorem totalFinitePowerCost_relabel {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFinitePowerCost p (x ∘ u) (y ∘ v) =
      M.totalFinitePowerCost p x y :=
  totalBoundaryCost_relabel u v M
    (fun i j => (finitePairCost (x i) (y j)).toReal ^ p)
    (fun i => (diagonalCost (x i)).toReal ^ p)
    (fun j => (diagonalCost (y j)).toReal ^ p)

end OccurrenceMatching

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Attained powered matching minimum, before taking a reciprocal-power root.-/
def finitePowerMatchingCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFinitePowerCost p x y

/-- Root of the optimized powered sum; the PD exponent domain is `1 ≤ p`.-/
def finitePMatchingCost (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  finitePowerMatchingCost p x y ^ p⁻¹

/--
@isnad1 id=ex.0h5v.s5.38946736622c from=translated src=- shape=cbb8e740 vocab=8f19c4b0
-/
theorem exists_minimizing_powerMatching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y = finitePowerMatchingCost p x y := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  exact exists_eq_ciInf_of_finite

/--
@isnad1 id=le.0h6v.s5.ed7e3a1b8eec from=translated src=- shape=72558dfd vocab=428f9390
-/
theorem finitePowerMatchingCost_le_matching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    finitePowerMatchingCost p x y ≤ M.totalFinitePowerCost p x y :=
  ciInf_le ⟨0, by rintro _ ⟨N, rfl⟩; exact N.totalFinitePowerCost_nonneg p x y⟩ M

/--
@isnad1 id=iff.0h6v.s5.a1d1ce1f49d9 from=translated src=- shape=5e311f7d vocab=428f9390
-/
theorem le_finitePowerMatchingCost_iff (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (c : ℝ) :
    c ≤ finitePowerMatchingCost p x y ↔
      ∀ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, c ≤ M.totalFinitePowerCost p x y := by
  constructor
  · intro h M
    exact h.trans (finitePowerMatchingCost_le_matching p x y M)
  · intro h
    obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    exact hM ▸ h M

/--
@isnad1 id=le.0h5v.s5.0815ce13b138 from=translated src=- shape=96f5c5ea vocab=fac36870
-/
theorem finitePowerMatchingCost_nonneg (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ finitePowerMatchingCost p x y :=
  (le_finitePowerMatchingCost_iff p x y 0).mpr fun M => M.totalFinitePowerCost_nonneg p x y

/--
@isnad1 id=le.0h5v.s5.82e2e9885eda from=translated src=- shape=96f5c5ea vocab=6af3225b
-/
theorem finitePMatchingCost_nonneg (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ finitePMatchingCost p x y := Real.rpow_nonneg (finitePowerMatchingCost_nonneg p x y) _

/-- A rooted candidate bounds the rooted minimum; coefficients were optimized first.
@isnad1 id=le.1h6v.s6.e314ec4fe068 from=translated src=- shape=39ea3ff1 vocab=c54863fe
-/
theorem finitePMatchingCost_le_matching {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    finitePMatchingCost p x y ≤ M.totalFinitePowerCost p x y ^ p⁻¹ :=
  Real.rpow_le_rpow (finitePowerMatchingCost_nonneg p x y)
    (finitePowerMatchingCost_le_matching p x y M) (inv_nonneg.mpr (le_trans zero_le_one hp))

/-- The matching attaining the powered minimum also realizes its reciprocal-power root.
@isnad1 id=ex.0h5v.s6.3c1b5a777fc0 from=translated src=- shape=92c44794 vocab=b4e8b8c6
-/
theorem exists_minimizing_pMatching (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFinitePowerCost p x y ^ p⁻¹ = finitePMatchingCost p x y := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  exact ⟨M, by rw [hM]; rfl⟩

/-- Attainment justifies placing the root inside the infimum, without a limit argument.
@isnad1 id=eq.1h5v.s6.4f8162d0ea96 from=translated src=- shape=6978d706 vocab=529daa9b
-/
theorem finitePMatchingCost_eq_iInf {p : ℝ} (hp : 1 ≤ p)
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y =
      ⨅ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFinitePowerCost p x y ^ p⁻¹ := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  have hbd : BddBelow (Set.range fun M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} =>
      M.totalFinitePowerCost p x y ^ p⁻¹) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨M, rfl⟩
    exact Real.rpow_nonneg (M.totalFinitePowerCost_nonneg p x y) _
  apply le_antisymm
  · exact le_ciInf fun M => finitePMatchingCost_le_matching hp x y M
  · obtain ⟨M, hM⟩ := exists_minimizing_pMatching p x y
    exact (ciInf_le hbd M).trans_eq hM

/--
@isnad1 id=eq.0h4v.s5.adbfae17255f from=translated src=- shape=aab87b45 vocab=707d1efb
-/
@[simp] theorem finitePowerMatchingCost_one (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost 1 x y = finiteFirstOrderMatchingCost x y := by
  simp only [finitePowerMatchingCost, OccurrenceMatching.totalFinitePowerCost_one,
    finiteFirstOrderMatchingCost]

/--
@isnad1 id=eq.0h4v.s5.0d5bf7b349cd from=translated src=- shape=aab87b45 vocab=9bdeaa94
-/
@[simp] theorem finitePMatchingCost_one (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost 1 x y = finiteFirstOrderMatchingCost x y := by
  simp [finitePMatchingCost]

/--
@isnad1 id=eq.0h5v.s5.cc2a71dbfcc6 from=translated src=- shape=b96489cd vocab=3a5d5733
-/
theorem finitePowerMatchingCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = ∑ i, (diagonalCost (x i)).toReal ^ p := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  have hn (i : I) : M.finite i = none := by
    cases h : M.finite i with
    | none => rfl
    | some j => exact isEmptyElim j
  rw [← hM]
  simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hn]

/--
@isnad1 id=eq.0h5v.s5.e7471ed7bd9e from=translated src=- shape=1514b76f vocab=3a5d5733
-/
theorem finitePowerMatchingCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p x y = ∑ j, (diagonalCost (y j)).toReal ^ p := by
  obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
  rw [← hM]
  simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]

/--
@isnad1 id=eq.0h5v.s5.50392a5aef56 from=translated src=- shape=224fad33 vocab=200e8323
-/
@[simp] theorem finitePowerMatchingCost_empty [IsEmpty I] [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finitePowerMatchingCost p x y = 0 := by
  rw [finitePowerMatchingCost_of_isEmpty_right]; exact Fintype.sum_empty _

/--
@isnad1 id=eq.0h5v.s6.675583e0bd6b from=translated src=- shape=5568a38f vocab=0a36e349
-/
theorem finitePMatchingCost_of_isEmpty_right [IsEmpty J]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = (∑ i, (diagonalCost (x i)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePMatchingCost, finitePowerMatchingCost_of_isEmpty_right]

/--
@isnad1 id=eq.0h5v.s6.7fb6a24920e9 from=translated src=- shape=9269f699 vocab=0a36e349
-/
theorem finitePMatchingCost_of_isEmpty_left [IsEmpty I]
    (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = (∑ j, (diagonalCost (y j)).toReal ^ p) ^ p⁻¹ := by
  rw [finitePMatchingCost, finitePowerMatchingCost_of_isEmpty_left]

/--
@isnad1 id=eq.1h5v.s5.2d9fb7c47dd7 from=translated src=- shape=24831e73 vocab=006e4a45
-/
@[simp] theorem finitePMatchingCost_empty [IsEmpty I] [IsEmpty J]
    {p : ℝ} (hp : 1 ≤ p) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p x y = 0 := by
  rw [finitePMatchingCost, finitePowerMatchingCost_empty]
  exact Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)))

/--
@isnad1 id=eq.0h9v.s6.351cc4992621 from=translated src=- shape=2fbafb3a vocab=e127de39
-/
theorem finitePowerMatchingCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePowerMatchingCost p (x ∘ u) (y ∘ v) = finitePowerMatchingCost p x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_powerMatching p x y
    calc
      _ ≤ (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFinitePowerCost
          p (x ∘ u) (y ∘ v) := finitePowerMatchingCost_le_matching _ _ _ _
      _ = _ := by rw [M.totalFinitePowerCost_relabel, hM]
  · obtain ⟨N, hN⟩ := exists_minimizing_powerMatching p (x ∘ u) (y ∘ v)
    obtain ⟨M, hM⟩ :=
      (OccurrenceMatching.relabelEquiv u v (Equiv.refl PEmpty.{1})
        (Equiv.refl PEmpty.{1})).surjective N
    have hcost := M.totalFinitePowerCost_relabel u v p x y
    change M.relabel u v (Equiv.refl _) (Equiv.refl _) = N at hM
    rw [hM] at hcost
    calc
      _ ≤ M.totalFinitePowerCost p x y := finitePowerMatchingCost_le_matching _ _ _ _
      _ = _ := hcost.symm.trans hN

/--
@isnad1 id=eq.0h9v.s6.cdbd82fc2d95 from=translated src=- shape=2fbafb3a vocab=1438846e
-/
theorem finitePMatchingCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (p : ℝ) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finitePMatchingCost p (x ∘ u) (y ∘ v) = finitePMatchingCost p x y := by
  simp only [finitePMatchingCost, finitePowerMatchingCost_reindex]

/-- For one occurrence on each side, pairing and deleting both are the two candidates.
@isnad1 id=eq.0h3v.s6.775a67bc5518 from=translated src=- shape=21371f6a vocab=00ffd06e
-/
theorem finitePowerMatchingCost_singleton (p : ℝ) (x y : ℝ × ℝ) :
    finitePowerMatchingCost p (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) =
      min ((finitePairCost x y).toReal ^ p)
        ((diagonalCost x).toReal ^ p + (diagonalCost y).toReal ^ p) := by
  let pair : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1} :=
    ⟨fun i => some i, by intro i i' j hi hi'; simpa using hi.trans hi'.symm, Equiv.refl _⟩
  let delete : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1} :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  apply le_antisymm
  · apply le_min
    · simpa [pair, OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]
        using finitePowerMatchingCost_le_matching p (fun _ => x) (fun _ => y) pair
    · simpa [delete, OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost]
        using finitePowerMatchingCost_le_matching p (fun _ => x) (fun _ => y) delete
  · apply (le_finitePowerMatchingCost_iff p _ _ _).mpr
    intro M
    cases h : M.finite 0 with
    | none =>
      have hf (i : Fin 1) : M.finite i = none := by
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using h
      simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hf]
    | some j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      have hf (i : Fin 1) : M.finite i = some 0 := by
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using h
      simp [OccurrenceMatching.totalFinitePowerCost, OccurrenceMatching.totalBoundaryCost, hf]

end TDA.Persistence
