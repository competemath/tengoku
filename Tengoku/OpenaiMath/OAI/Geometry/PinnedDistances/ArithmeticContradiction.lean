import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.BoundedContradiction

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned

lemma sequence_bounded_subsequence (W : ℕ → ℝ) (hW : ¬Tendsto W atTop atTop)
    (p : ℕ → Prop) (hp : ∀ᶠ n in atTop,p n) :
    ∃ (φ : ℕ → ℕ) (C : ℝ),Tendsto φ atTop atTop ∧ 0≤C ∧ ∀ n,W (φ n)≤C ∧ p (φ n) := by
  rw [tendsto_atTop] at hW
  push Not at hW
  obtain ⟨C,hC⟩ := hW
  obtain ⟨φ,hφ,hφC⟩ := exists_seq_forall_of_frequently (hC.and_eventually hp)
  exact ⟨φ,max C 0,hφ,le_max_right _ _,fun n => ⟨(hφC n).1.le.trans (le_max_left _ _),(hφC n).2⟩⟩

end WeakPinned

end
end
section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned
open Global

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]

end WeakPinned

end
end

end OAI
