import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.Order.Filter.AtTopBot.Archimedean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms CriticalGK2.Growth.upperExponent_ge_two_of_quadratic_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms CriticalGK2.Growth.gkExponent_eq_two_of_quadratic_lower_near_two_upper` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# The numerical growth-exponent endpoint

The growth function is an actual natural-valued function. Polynomial upper
exponents are defined by literal global bounds C*n^d for positive integer n.
The exponent is their infimum. Quadratic lower growth excludes every exponent
d<2 by the proved divergence of n^(2-d), and upper bounds at every 2+epsilon
make the infimum equal to two. Nonemptiness and boundedness below of the
actual exponent set ensure that its infimum has the stated value.

The ordinary numerical bounds remain explicit inputs in this module. Their
actual algebraic construction is supplied in the separate filtered-growth
and support-budget modules.
-/

namespace CriticalGK2.Growth

open Filter

noncomputable section

/-- Literal global polynomial upper exponents of the actual growth function.-/
def UpperExponentSet (γ : ℕ → ℕ) : Set ℝ :=
  {d | ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (γ n : ℝ) ≤ C * (n : ℝ) ^ d}

/-- The growth-infimum definition of the exponent. At the theorem below
its defining set is proved nonempty and bounded below.-/
def GKExponent (γ : ℕ → ℕ) : ℝ := sInf (UpperExponentSet γ)

/-- A quadratic lower bound and a literal C*n^d upper bound give a literal
upper bound on n^(2-d), with division justified by n>=1.
@isnad1 id=le.3h4v.s7.201f358171b3 from=translated src=- shape=646661b2 vocab=81fe82b2
-/
theorem rpow_gap_bound_of_quadratic_lower_upper (γ : ℕ → ℕ) (d C : ℝ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (hupper : ∀ n : ℕ, 1 ≤ n → (γ n : ℝ) ≤ C * (n : ℝ) ^ d)
    (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ ((2 : ℝ) - d) ≤ 2 * C := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpd : 0 < (n : ℝ) ^ d := Real.rpow_pos_of_pos hnpos d
  rw [Real.rpow_sub hnpos (2 : ℝ) d, Real.rpow_two]
  apply (div_le_iff₀ hpd).mpr
  calc
    (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ) := hlower n hn
    _ ≤ 2 * (C * (n : ℝ) ^ d) :=
      mul_le_mul_of_nonneg_left (hupper n hn) (by norm_num)
    _ = (2 * C) * (n : ℝ) ^ d := by ring

/-- No literal polynomial upper exponent below two is compatible with
actual quadratic lower growth. The contradiction uses n^(2-d) at real atTop
composed with the actual natural-number cast.
@isnad1 id=le.2h2v.s6.0aec1766c14a from=translated src=- shape=b9c5c6d1 vocab=3e5c2ade
-/
theorem upperExponent_ge_two_of_quadratic_lower (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (d : ℝ) (hd : d ∈ UpperExponentSet γ) : 2 ≤ d := by
  by_contra h
  have hgap : 0 < (2 : ℝ) - d := by linarith
  obtain ⟨C, _hC, hupper⟩ := hd
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - d)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hgap).comp hcast
  have he : ∀ᶠ n : ℕ in atTop, 2 * C < (n : ℝ) ^ ((2 : ℝ) - d) :=
    ht.eventually (eventually_gt_atTop (2 * C))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  have hbig : 2 * C < ((max N 1 : ℕ) : ℝ) ^ ((2 : ℝ) - d) :=
    hN (max N 1) (le_max_left N 1)
  have hbound := rpow_gap_bound_of_quadratic_lower_upper γ d C hlower hupper
    (max N 1) (le_max_right N 1)
  linarith

/-- The actual upper-exponent set has two as a proved lower bound.
@isnad1 id=bddbelow.1h1v.s6.9a488fd7eaa1 from=translated src=- shape=81c3b9f7 vocab=3b7fbe47
-/
theorem upperExponentSet_bddBelow_of_quadratic_lower (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ)) :
    BddBelow (UpperExponentSet γ) :=
  ⟨2, fun d hd => upperExponent_ge_two_of_quadratic_lower γ hlower d hd⟩

/-- Near-quadratic polynomial upper bounds give a literal nonempty set.
@isnad1 id=nonempty.1h1v.s5.8044bbe6c5d3 from=translated src=- shape=d3ca5608 vocab=30962d3c
-/
theorem upperExponentSet_nonempty_of_near_two_upper (γ : ℕ → ℕ)
    (hupper : ∀ ε : ℝ, 0 < ε → 2 + ε ∈ UpperExponentSet γ) :
    (UpperExponentSet γ).Nonempty :=
  ⟨2 + 1, hupper 1 (by norm_num)⟩

/-- The exact growth exponent equals two under the explicit numerical lower
and all-positive-epsilon upper bounds. All infimum side conditions are proved.
@isnad1 id=eq.2h1v.s6.f321878557d3 from=translated src=- shape=b7ce8118 vocab=d25f6358
-/
theorem gkExponent_eq_two_of_quadratic_lower_near_two_upper (γ : ℕ → ℕ)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (2 : ℕ) ≤ 2 * (γ n : ℝ))
    (hupper : ∀ ε : ℝ, 0 < ε → 2 + ε ∈ UpperExponentSet γ) : GKExponent γ = 2 := by
  have hne := upperExponentSet_nonempty_of_near_two_upper γ hupper
  have hbd := upperExponentSet_bddBelow_of_quadratic_lower γ hlower
  have hl : (2 : ℝ) ≤ sInf (UpperExponentSet γ) :=
    le_csInf hne (fun d hd => upperExponent_ge_two_of_quadratic_lower γ hlower d hd)
  have hu : sInf (UpperExponentSet γ) ≤ (2 : ℝ) := by
    by_contra h
    have heps : 0 < (sInf (UpperExponentSet γ) - 2) / 2 := by linarith
    have hclose := csInf_le hbd (hupper _ heps)
    linarith
  exact le_antisymm hu hl

end

end CriticalGK2.Growth
