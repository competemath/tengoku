import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.Cocycle
import Tengoku

namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
local instance : DecidableEq I := Classical.decEq I
abbrev Space (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] := lp E 2

def inclusion (i : I) : E i →L[ℂ] Space E := lp.singleContinuousLinearMap ℂ E 2 i

def evaluation (i : I) : Space E →L[ℂ] E i := lp.evalCLM ℂ E 2 i

@[simp] theorem inclusion_apply (i : I) (x : E i) : inclusion i x = lp.single 2 i x := rfl
@[simp] theorem evaluation_apply (i : I) (x : Space E) : evaluation i x = x i := rfl

def boundedSum (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ} (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) :
    Space E →L[ℂ] Space E := lp.mapCLM 2 T hκ hT

@[simp] theorem boundedSum_apply (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) (x : Space E) (i : I) :
    boundedSum T hκ hT x i = T i (x i) := rfl

theorem unitary_bound {index : I} (U : G →* (E index →L[ℂ] E index))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) :
    ‖U g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [hU]

def representation (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) : G →* (Space E →L[ℂ] Space E) where
  toFun g := boundedSum (fun i => U i g) zero_le_one (fun i => unitary_bound (U i) (hU i) g)
  map_one' := by ext x i; change U i 1 (x i) = x i; simp
  map_mul' g h := by
    ext x i
    change U i (g*h) (x i) = U i g (U i h (x i))
    rw [map_mul]; rfl

@[simp] theorem representation_apply (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) (i : I) :
    representation U hU g x i = U i g (x i) := rfl

def cocycle (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) : Space E →L[ℂ] Space E :=
  boundedSum (fun i => D i g) hκ (fun i => hb i g)

omit [Group G] in
@[simp] theorem cocycle_apply (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (g : G) (x : Space E) (i : I) :
    cocycle D hκ hb g x i = D i g (x i) := rfl

theorem cocycle_one (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (h1 : ∀ i, D i 1 = 0) :
    cocycle D hκ hb 1 = 0 := by ext x i; simp [h1]

def compression (B : Space E →L[ℂ] Space E) (i : I) : E i →L[ℂ] E i :=
  (evaluation i).comp (B.comp (inclusion i))

theorem compression_norm_le (B : Space E →L[ℂ] Space E) (i : I) : ‖compression B i‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖B (lp.single 2 i x) i‖ ≤ ‖B‖ * ‖x‖
  calc
    _ ≤ ‖B (lp.single 2 i x)‖ := lp.norm_apply_le_norm (by norm_num) _ i
    _ ≤ ‖B‖ * ‖lp.single 2 i x‖ := B.le_opNorm _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

/-- Countably many separable fibres have a separable Hilbert sum. The proof
uses the dense span of coordinate inclusions and convergence of finite sums. -/
theorem separableSpace [Countable I] [∀ i, TopologicalSpace.SeparableSpace (E i)] :
    TopologicalSpace.SeparableSpace (Space E) := by
  let s : Set (Space E) := ⋃ i, Set.range (inclusion (E := E) i)
  let V : Submodule ℂ (Space E) := Submodule.span ℂ s
  have hs : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.IsSeparable.iUnion (fun i =>
      TopologicalSpace.isSeparable_range (inclusion (E := E) i).continuous)
  have hv : TopologicalSpace.IsSeparable (V : Set (Space E)) := hs.span
  have hd : Dense (V : Set (Space E)) := by
    intro x
    apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro F
    apply subset_closure
    apply V.sum_mem
    intro i hi
    exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨i, ⟨x i, rfl⟩⟩)
  exact hd.isSeparable_iff.mp hv

end HilbertSum
end Dixmier

end

end OAI
