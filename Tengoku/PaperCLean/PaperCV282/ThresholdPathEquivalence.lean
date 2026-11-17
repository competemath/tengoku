import Tengoku.PaperCLean.PaperCV282.MovingMarkedLevels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact configurations and their complete threshold paths

A finite-mass natural sequence is a finitely supported configuration. Its
whole tail-sum path is again finitely supported and antitone. Consecutive
natural differences recover every exact count, giving a measurable bijection
and exact preservation of total variation, without a threshold union bound.
-/
namespace PaperC.V282.ThresholdPathEquivalence

open FiniteFieldTotalVariation MassPushforward MovingMarkedLevels MeasureTheory
open scoped BigOperators

noncomputable section

/-- Count all marks at or above m, retaining the whole path.-/
def tailCount (c : ℕ →₀ ℕ) (m : ℕ) : ℕ :=
  ∑ e ∈ c.support, if m ≤ e then c e else 0

/--
@isnad1 id=eq.1h2v.s5.b4ff3f1efec7 from=translated src=- shape=b1eda5d2 vocab=510271e7
-/
theorem tailCount_zero_of_support_lt (c : ℕ →₀ ℕ) {m : ℕ}
    (hm : c.support.sup id < m) : tailCount c m = 0 := by
  unfold tailCount
  apply Finset.sum_eq_zero
  intro e he
  have he' : e ≤ c.support.sup id := Finset.le_sup (f := id) he
  simp [show ¬m ≤ e by omega]

/--
@isnad1 id=antitone.0h1v.s3.6026bac57c49 from=translated src=- shape=b5e23c52 vocab=1b01e962
-/
theorem tailCount_antitone (c : ℕ →₀ ℕ) : Antitone (tailCount c) := by
  intro m n hmn
  apply Finset.sum_le_sum
  intro e he
  split_ifs <;> omega

/--
@isnad1 id=eq.0h2v.s5.7c12edfeeeb5 from=translated src=- shape=99027096 vocab=71495bbd
-/
theorem tailCount_succ (c : ℕ →₀ ℕ) (m : ℕ) :
    tailCount c m = c m + tailCount c (m+1) := by
  have hsplit : tailCount c m =
      (∑ e ∈ c.support, if m=e then c e else 0) + tailCount c (m+1) := by
    unfold tailCount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> omega
  rw [hsplit]
  congr 1
  simp only [Finset.sum_ite_eq]
  by_cases hm : m ∈ c.support
  · simp [hm]
  · simp [hm, Finsupp.notMem_support_iff.mp hm]

/-- The finite-support representation of the complete threshold path.-/
def tailConfiguration (c : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range (c.support.sup id+1)) (tailCount c) (by
    intro m hm
    apply Finset.mem_range.mpr
    by_contra h
    exact hm (tailCount_zero_of_support_lt c (by omega)))

/--
@isnad1 id=eq.0h2v.s5.7b0349ec5230 from=translated src=- shape=c23c7a7c vocab=dae60dec
-/
theorem tailConfiguration_apply (c : ℕ →₀ ℕ) (m : ℕ) :
    tailConfiguration c m = tailCount c m := rfl

/-- Every threshold path is antitone and has finite support.-/
def ThresholdPath := {t : ℕ →₀ ℕ // Antitone t}

/--
@isnad1 id=countabl.0h0v.s1.1678a87cbca0 from=translated src=- shape=49959d42 vocab=f38dc2e5
-/
instance instCountableThresholdPath : Countable ThresholdPath :=
  inferInstanceAs (Countable {t : ℕ →₀ ℕ // Antitone t})

/-- Consecutive differences recover the exact-level masses.-/
def differenceConfiguration (t : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset t.support (fun m => t m-t (m+1)) (by
    intro m hm
    apply Finsupp.mem_support_iff.mpr
    intro hz
    simp [hz] at hm)

/--
@isnad1 id=eq.0h2v.s6.57008a49c39a from=translated src=- shape=8a2a78d9 vocab=a3e11ba6
-/
theorem differenceConfiguration_apply (t : ℕ →₀ ℕ) (m : ℕ) :
    differenceConfiguration t m = t m-t (m+1) := rfl

/--
@isnad1 id=eq.0h1v.s4.a9cc9cff651a from=translated src=- shape=55dc2d38 vocab=61e8046b
-/
theorem difference_tailConfiguration (c : ℕ →₀ ℕ) :
    differenceConfiguration (tailConfiguration c) = c := by
  ext m
  simp only [differenceConfiguration_apply,tailConfiguration_apply]
  have := tailCount_succ c m
  omega

/--
@isnad1 id=eq.1h1v.s5.341e9b10a072 from=translated src=- shape=233fe3a1 vocab=a27f54d7
-/
theorem tail_differenceConfiguration (t : ℕ →₀ ℕ) (ht : Antitone t) :
    tailConfiguration (differenceConfiguration t) = t := by
  ext m
  let K := max (t.support.sup id) ((differenceConfiguration t).support.sup id) + 1
  have hzero : ∀ k, K ≤ k → tailCount (differenceConfiguration t) k = t k := by
    intro k hk
    have hc : (differenceConfiguration t).support.sup id < k := by
      dsimp [K] at hk
      omega
    have hz : t k=0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hmem
      have hk' : k ≤ t.support.sup id := Finset.le_sup (f := id) hmem
      dsimp [K] at hk
      omega
    rw [tailCount_zero_of_support_lt _ hc,hz]
  change tailCount (differenceConfiguration t) m = t m
  by_cases hm : K ≤ m
  · exact hzero m hm
  · refine Nat.decreasingInduction' (P := fun k => tailCount (differenceConfiguration t) k = t k) (n := K) (m := m) ?_ (by omega) (hzero K le_rfl)
    intro k hk hmk ih
    have hrec := tailCount_succ (differenceConfiguration t) k
    rw [differenceConfiguration_apply,ih] at hrec
    have hmono := ht (show k ≤ k+1 by omega)
    omega

/-- A bijection, with no support cutoff and no loss of thresholds.-/
def thresholdEquiv : (ℕ →₀ ℕ) ≃ ThresholdPath where
  toFun c := ⟨tailConfiguration c,tailCount_antitone c⟩
  invFun t := differenceConfiguration t.val
  left_inv := difference_tailConfiguration
  right_inv t := by
    apply Subtype.ext
    exact tail_differenceConfiguration t.val t.property

/--
@isnad1 id=eq.0h2v.s7.d800849467e6 from=translated src=- shape=0dd2d3d0 vocab=68d3f7e1
-/
theorem thresholdEquiv_apply (c : ℕ →₀ ℕ) (m : ℕ) :
    (thresholdEquiv c).val m = ∑ e ∈ c.support, if m ≤ e then c e else 0 := rfl

/--
@isnad1 id=eq.0h2v.s7.5fe7f5badd64 from=translated src=- shape=12d528b2 vocab=8602f230
-/
theorem thresholdEquiv_symm_apply (t : ThresholdPath) (m : ℕ) :
    thresholdEquiv.symm t m = t.val m-t.val (m+1) := rfl

/-- The literal infinite path, not merely its finite-support encoding.-/
def thresholdFunction (c : ℕ →₀ ℕ) : ℕ → ℕ := tailCount c

/--
@isnad1 id=injectiv.0h0v.s3.4183ecfdf69b from=translated src=- shape=ddf547f8 vocab=e081fd53
-/
theorem thresholdFunction_injective : Function.Injective thresholdFunction := by
  intro c k h
  apply thresholdEquiv.injective
  apply Subtype.ext
  ext m
  exact congrFun h m

/--
@isnad1 id=eq.0h2v.s5.ae5d0dd7c711 from=translated src=- shape=8a5fe940 vocab=a7dc7934
-/
theorem threshold_function_totalVariation_eq (p q : (ℕ →₀ ℕ) → ℝ) :
    massTotalVariation (pushforwardMass thresholdFunction p)
      (pushforwardMass thresholdFunction q) = massTotalVariation p q :=
  massTotalVariation_injective _ thresholdFunction_injective p q

/-- Signs or other retained labels are transformed jointly, not marginally.-/
def labelledThresholdEquiv (σ : Type*) : (σ → (ℕ →₀ ℕ)) ≃ (σ → ThresholdPath) :=
  Equiv.piCongrRight (fun _ => thresholdEquiv)

/--
@isnad1 id=measurab.0h0v.s6.3f577e399c03 from=translated src=- shape=66e98f39 vocab=b448d62c
-/
theorem measurable_thresholdEquiv [MeasurableSpace (ℕ →₀ ℕ)]
    [MeasurableSingletonClass (ℕ →₀ ℕ)] [MeasurableSpace ThresholdPath] :
    Measurable thresholdEquiv := measurable_of_countable _

/--
@isnad1 id=measurab.0h0v.s6.60288dcc825b from=translated src=- shape=10f3e369 vocab=773cc7fd
-/
theorem measurable_thresholdEquiv_symm [MeasurableSpace ThresholdPath]
    [MeasurableSingletonClass ThresholdPath] [MeasurableSpace (ℕ →₀ ℕ)] :
    Measurable thresholdEquiv.symm := measurable_of_countable _

end
end PaperC.V282.ThresholdPathEquivalence
