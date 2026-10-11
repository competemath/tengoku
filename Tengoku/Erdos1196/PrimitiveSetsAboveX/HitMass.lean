module

public import Tengoku.Erdos1196.PrimitiveSetsAboveX.Markov
public import Tengoku

/-!
# Hit mass and final reductions

This file develops the `ENNReal` mass-flow layer behind the Markov-chain argument. It defines
exact-step arrival mass, surviving mass before the first hit of a set `A`, and the total first-hit
mass of `A`.

The central estimate is a telescope: if the restricted initial mass is at most `1` and each row of
the transition kernel has total mass at most `1`, then the total first-hit mass of `A` is at most
`1`. For primitive `A`, this is the visit-mass inequality used in the final argument, because finite
paths in the multiplicative chain can meet `A` at most once.

## Main definitions

* `initialMass`
* `transitionKernel`
* `arrivalMass`
* `survivingArrivalMass`
* `firstHitMassAtStep`
* `visitMass`

## Main statements

* `MarkovLayer.kernelRowBound`
* `tsum_initialMass_eq_one`
* `visitMass_le_of_bounds`
* `PrimitiveSet.summable_indicator_visitProbability_and_tsum_le_one_of_visitMass_le_one`
-/

@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

/-- The normalized initial mass restricted to the state space `n ≥ x`. -/
noncomputable def initialMass (x Y n : ℕ) : ENNReal :=
  ENNReal.ofReal (if x ≤ n then initialDistribution x Y n else 0)

/--
The transition kernel on states `n ≥ x`, viewed as an `ENNReal`-valued mass function.

The state `m` can send mass to `n` only when `m ≥ x`, `m ∣ n`, and the quotient `n / m` is a
valid jump factor `q ≥ Y`.
-/
noncomputable def transitionKernel (x Y m n : ℕ) : ENNReal :=
  if x ≤ m ∧ m ∣ n ∧ Y ≤ n / m then
    ENNReal.ofReal (transitionWeight Y m (n / m))
  else
    0

/-- Exact-step arrival mass at state `n` after `k` steps in the multiplicative chain. -/
noncomputable def arrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) : ℕ → ℕ → ENNReal
  | 0, n => initialMass x Y n
  | k + 1, n => ∑' m : ℕ, arrivalMass chain k m * transitionKernel x Y m n

/--
The surviving mass at state `n` after `k` steps, obtained by discarding every path that has already
hit `A`.
-/
noncomputable def survivingArrivalMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ℕ → ENNReal
  | 0, n => Aᶜ.indicator (initialMass x Y) n
  | k + 1, n =>
      Aᶜ.indicator
        (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The mass that first hits `A` exactly at step `k`.

For `k = 0` this is the initial mass already inside `A`, and for `k + 1` it is the mass
propagated from the surviving mass at step `k` into `A`.
-/
noncomputable def firstHitMassAtStep {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) :
    ℕ → ENNReal
  | 0 => ∑' n : ℕ, A.indicator (initialMass x Y) n
  | k + 1 =>
      ∑' n : ℕ,
        A.indicator
          (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n) n

/--
The total visit mass of `A`, counted by the first hit of `A` along each path. For primitive sets,
this agrees with the usual total mass of visits because finite multiplicative paths meet `A` at
most once.
-/
noncomputable def visitMass {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ) : ENNReal :=
  ∑' k : ℕ, firstHitMassAtStep chain A k

/-- Once `B_x > 0`, the restricted initial mass has total mass exactly `1`. -/
lemma tsum_initialMass_eq_one {x Y : ℕ} (hB : 0 < normalizationConstant x Y) :
    (∑' n : ℕ, initialMass x Y n) = 1 := by
  let f : ℕ → ℝ := fun n => if x ≤ n then entryWeight x Y n else 0
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    by_cases hn : x ≤ n
    · simpa [f, hn, entryWeight_eq_smallPrimeEntryWeight_add_firstEntryEntryWeight] using
        add_nonneg (smallPrimeEntryWeight_nonneg Y n) (firstEntryEntryWeight_nonneg x Y n)
    · simp [f, hn]
  have hf_summable : Summable f := by
    by_contra hf
    exact hB.ne' (by simpa [normalizationConstant, f] using (tsum_eq_zero_of_not_summable hf))
  calc
    ∑' n : ℕ, initialMass x Y n = ∑' n : ℕ, ENNReal.ofReal (f n / normalizationConstant x Y) := by
      refine tsum_congr ?_
      intro n
      by_cases hn : x ≤ n <;> simp [initialMass, f, initialDistribution, hn]
    _ = ENNReal.ofReal (∑' n : ℕ, f n / normalizationConstant x Y) := by
      rw [ENNReal.ofReal_tsum_of_nonneg
        (fun n => div_nonneg (hf_nonneg n) hB.le)
        (by simpa [div_eq_mul_inv] using hf_summable.mul_right ((normalizationConstant x Y)⁻¹))]
    _ = ENNReal.ofReal ((∑' n : ℕ, f n) / normalizationConstant x Y) := by
      congr 1
      rw [show (fun n : ℕ => f n / normalizationConstant x Y) =
        fun n => f n * (normalizationConstant x Y)⁻¹ by
          funext n
          simp [div_eq_mul_inv]]
      rw [tsum_mul_right]
      simp [div_eq_mul_inv]
    _ = 1 := by
      rw [show ∑' n : ℕ, f n = normalizationConstant x Y by simp [normalizationConstant, f]]
      field_simp [hB.ne']
      simp
/-- A kernel term landing below `x` is zero once `Y ≥ 1` and `x > 0`. -/
private lemma transitionKernel_eq_zero_of_lt {x Y m n : ℕ} (hY : 1 ≤ Y) (hn : n < x) :
    transitionKernel x Y m n = 0 := by
  by_cases hcond : x ≤ m ∧ m ∣ n ∧ Y ≤ n / m
  · have hqm : 1 ≤ n / m := le_trans hY hcond.2.2
    have hm_le_prod : m ≤ m * (n / m) := by
      simpa [one_mul] using Nat.mul_le_mul_left m hqm
    have hprod_le_n : m * (n / m) ≤ n := Nat.mul_div_le n m
    lia
  · simp [transitionKernel, hcond]

/-- States below `x` carry no surviving mass either. -/
private lemma survivingArrivalMass_eq_zero_of_lt {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y) :
    ∀ k {n : ℕ}, n < x → survivingArrivalMass chain A k n = 0
  | 0, n, hn => by
      by_cases hnA : n ∈ A <;> simp [survivingArrivalMass, initialMass, hnA, hn.not_ge]
  | k + 1, n, hn => by
      by_cases hnA : n ∈ A
      · simp [survivingArrivalMass, Set.indicator, hnA]
      · rw [survivingArrivalMass]
        have hnAc : n ∈ Aᶜ := by simpa using hnA
        rw [Set.indicator_of_mem hnAc]
        apply (ENNReal.tsum_eq_zero).2
        intro m
        by_cases hm : x ≤ m
        · simp [transitionKernel_eq_zero_of_lt (m := m) hY hn]
        · simp [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]

/-- Splitting a series into the part supported on `A` and the part supported on `Aᶜ` recovers the
original total mass. -/
private lemma tsum_indicator_add_tsum_indicator_compl (A : Set ℕ) (f : ℕ → ENNReal) :
    (∑' n : ℕ, A.indicator f n) + (∑' n : ℕ, Aᶜ.indicator f n) = ∑' n : ℕ, f n := by
  rw [← ENNReal.tsum_add]
  exact congrArg (fun g : ℕ → ENNReal => ∑' n : ℕ, g n) (Set.indicator_self_add_compl A f)

/-- The step-0 hit mass together with the step-0 surviving mass is exactly the initial mass. -/
private lemma firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) :
    firstHitMassAtStep chain A 0 + (∑' n : ℕ, survivingArrivalMass chain A 0 n) =
      ∑' n : ℕ, initialMass x Y n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A (initialMass x Y)

/--
At step `k + 1`, the first-hit mass together with the surviving mass is exactly the mass
propagated from the surviving mass at step `k`.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) =
      ∑' n : ℕ, ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n := by
  simpa [firstHitMassAtStep, survivingArrivalMass] using
    tsum_indicator_add_tsum_indicator_compl A
      (fun n => ∑' m : ℕ, survivingArrivalMass chain A k m * transitionKernel x Y m n)

/--
The next first-hit mass together with the next surviving mass is bounded by the current surviving
mass.
-/
private lemma firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) (k : ℕ) :
    firstHitMassAtStep chain A (k + 1) +
        (∑' n : ℕ, survivingArrivalMass chain A (k + 1) n) ≤
      ∑' n : ℕ, survivingArrivalMass chain A k n := by
  rw [firstHitMassAtStep_succ_add_tsum_survivingArrivalMass]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  calc
    ∑' m : ℕ, survivingArrivalMass chain A k m * (∑' n : ℕ, transitionKernel x Y m n)
      ≤ ∑' m : ℕ, survivingArrivalMass chain A k m * 1 := by
          refine ENNReal.tsum_le_tsum ?_
          intro m
          by_cases hm : x ≤ m
          · gcongr
            exact hkernel hm
          · rw [survivingArrivalMass_eq_zero_of_lt chain A hx hY k (lt_of_not_ge hm)]
            simp
    _ = ∑' m : ℕ, survivingArrivalMass chain A k m := by simp

/--
The partial first-hit mass up to step `N`, together with the surviving mass at time `N`, stays
within the initial mass budget.
-/
private lemma sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
    {x Y : ℕ}
    (chain : MarkovLayer x Y) (A : Set ℕ) (hx : 0 < x) (hY : 1 ≤ Y)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    ∀ N : ℕ,
      (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k) +
          (∑' n : ℕ, survivingArrivalMass chain A N n) ≤
        ∑' n : ℕ, initialMass x Y n
  | 0 => by
      simpa using (firstHitMassAtStep_zero_add_tsum_survivingArrivalMass_zero chain A).le
  | N + 1 => by
      exact le_trans
        (by
          simpa [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm] using
            add_le_add_left
              (firstHitMassAtStep_succ_add_tsum_survivingArrivalMass_le
                chain A hx hY hkernel N)
              (∑ k ∈ Finset.range (N + 1), firstHitMassAtStep chain A k))
        (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
          chain A hx hY hkernel N)

/-- If the initial mass is at most `1` and every kernel row is sub-Markov, then the total
first-hit mass is at most `1`. -/
lemma visitMass_le_of_bounds {x Y : ℕ} (chain : MarkovLayer x Y) (A : Set ℕ)
    (hx : 0 < x) (hY : 1 ≤ Y)
    (hinit : (∑' n : ℕ, initialMass x Y n) ≤ 1)
    (hkernel : ∀ ⦃m : ℕ⦄, x ≤ m → (∑' n : ℕ, transitionKernel x Y m n) ≤ 1) :
    visitMass chain A ≤ 1 := by
  rw [visitMass]
  exact le_trans
    (by
      refine ENNReal.tsum_le_of_sum_range_le ?_
      intro N
      cases N with
      | zero => simp
      | succ N =>
          exact le_trans (le_add_right le_rfl)
            (sum_firstHitMassAtStep_add_tsum_survivingArrivalMass_le_initialMass
              chain A hx hY hkernel N))
    hinit

end PrimitiveSetsAboveX
