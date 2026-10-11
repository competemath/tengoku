import Tengoku

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346
namespace PolynomialWeights

open MvPolynomial

variable {R σ : Type*} [CommSemiring R] [Fintype σ]

/-- The Euler derivation associated with natural-number weights. -/
def weightedEuler (w : σ → ℕ) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  ∑ i : σ, (w i) • ((X i : MvPolynomial σ R) • pderiv i)

section Blocks

variable {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq β]

/-- Weight one on one coordinate block, and zero on all spectator blocks. -/
def blockWeight (u : β) (ki : β × ι) : ℕ := if ki.1 = u then 1 else 0

/-- A polynomial is homogeneous of the specified degree in one block. -/
def IsBlockHomogeneous (u : β) (f : MvPolynomial (β × ι) R) (n : ℕ) : Prop :=
  f.IsWeightedHomogeneous (blockWeight u) n

omit [Fintype β] [Fintype ι] in
@[simp] theorem blockWeight_apply (u k : β) (i : ι) :
    blockWeight u (k, i) = if k = u then 1 else 0 := rfl

omit [Fintype β] [Fintype ι] in
/-- Differentiating in a block lowers its degree by one, provided that degree is positive. -/
theorem block_pderiv_source {u : β} {n : ℕ} {f : MvPolynomial (β × ι) R}
    (hf : IsBlockHomogeneous u f n) (hn : 0 < n) (i : ι) :
    IsBlockHomogeneous u (pderiv (u, i) f) (n - 1) := by
  apply IsWeightedHomogeneous.pderiv hf
  simp only [blockWeight_apply]
  exact Nat.sub_add_cancel hn

omit [Fintype β] [Fintype ι] in
/-- Differentiating in another block leaves the indicated block degree unchanged. -/
theorem block_pderiv_other {u k : β} (hku : k ≠ u) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (i : ι) :
    IsBlockHomogeneous u (pderiv (k, i) f) n := by
  apply IsWeightedHomogeneous.pderiv hf
  simp [blockWeight_apply, hku]

omit [Fintype β] in
/-- A directional shift lowers its source block degree by one. -/
theorem block_shift_degree_source {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous u f n) (hn : 0 < n) :
    IsBlockHomogeneous u (∑ i : ι, X (v, i) * pderiv (u, i) f) (n - 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight u) (n - 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight u) 0 := by
    simpa [blockWeight_apply, Ne.symm huv] using
      (isWeightedHomogeneous_X (R := R) (blockWeight u) (v, i))
  simpa using hx.mul (block_pderiv_source hf hn i)

omit [Fintype β] in
/-- A directional shift raises its destination block degree by one. -/
theorem block_shift_degree_destination {u v : β} (huv : u ≠ v) {n : ℕ}
    {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous v f n) :
    IsBlockHomogeneous v (∑ i : ι, X (v, i) * pderiv (u, i) f) (n + 1) := by
  apply (weightedHomogeneousSubmodule R (blockWeight v) (n + 1)).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight v) 1 := by
    simpa [blockWeight_apply] using
      (isWeightedHomogeneous_X (R := R) (blockWeight v) (v, i))
  simpa [Nat.add_comm] using hx.mul (block_pderiv_other huv hf i)

omit [Fintype β] in
/-- A directional shift leaves every spectator block degree unchanged. -/
theorem block_shift_degree_spectator {u v k : β} (huk : u ≠ k) (hvk : v ≠ k)
    {n : ℕ} {f : MvPolynomial (β × ι) R} (hf : IsBlockHomogeneous k f n) :
    IsBlockHomogeneous k (∑ i : ι, X (v, i) * pderiv (u, i) f) n := by
  apply (weightedHomogeneousSubmodule R (blockWeight k) n).sum_mem
  intro i hi
  have hx : (X (v, i) : MvPolynomial (β × ι) R).IsWeightedHomogeneous
      (blockWeight k) 0 := by
    simpa [blockWeight_apply, hvk] using
      (isWeightedHomogeneous_X (R := R) (blockWeight k) (v, i))
  simpa using hx.mul (block_pderiv_other huk hf i)

end Blocks

end PolynomialWeights
end Problem346

end

end OAI
