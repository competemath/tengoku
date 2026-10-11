import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.EnergyEstimates

namespace OAI

universe uH

noncomputable section
namespace LipschitzCounterexample.CompactWSC
open scoped ContDiff BigOperators NNReal Topology
open Set Filter FreeSpace LocalizedLinearization
variable {H : Type uH} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

local instance : NormedAddCommGroup (Space H) := inferInstance
local instance : NormedSpace ℝ (Space H) := inferInstance
local instance (K : Set H) : NormedAddCommGroup (supported K) := inferInstance
local instance (K : Set H) : NormedSpace ℝ (supported K) := inferInstance
local instance (K : Set H) : NormedAddCommGroup ((supported K) →L[ℝ] ℝ) := inferInstance
local instance (K : Set H) : NormedSpace ℝ ((supported K) →L[ℝ] ℝ) := inferInstance

def molPair (a : MolecularData H) : (H → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ i, a.coeff i*(f (a.p i)-f (a.q i))
  map_add' f g := by simp only [Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring
  map_smul' c f := by simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]; congr 1; funext i; ring

def smoothPair (a : MolecularData H) : Smooth H →ₗ[ℝ] ℝ := (molPair a).comp (smoothSubmodule H).subtype

@[simp] theorem smoothPair_apply {H : Type uH} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (a : MolecularData H) (f : Smooth H) :
    smoothPair a f = molPair a f.val := rfl

structure RowItem (K : Set H) (C ρ : ℝ) (μ : ℕ → Space H) where
  f : Smooth H
  lip : LipschitzWith 1 f.val
  zero : f.val 0 = 0
  a : MolecularData H
  support : ∀ i, a.p i ∈ K ∧ a.q i ∈ K
  cost_le : a.cost ≤ C
  close : ∃ n, ‖μ n-a.vector‖ < ρ

def triangularRows (K : Set H) (C ρ α : ℝ) (μ : ℕ → Space H) :
    RowFamily (RowItem K C ρ μ) where
  accepts v := (∀ i j, j ≤ i → 4*α ≤ smoothPair (v i).a (v j).f) ∧
    (∀ i j, i < j → |smoothPair (v i).a (v j).f| ≤ α)
  hereditary e _ hv := ⟨fun i j h => hv.1 (e i) (e j) (e.monotone h),
    fun i j h => hv.2 (e i) (e j) (e.strictMono h)⟩

end LipschitzCounterexample.CompactWSC
end

end OAI
