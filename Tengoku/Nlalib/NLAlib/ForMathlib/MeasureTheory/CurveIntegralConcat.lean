import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Basic
import Tengoku.Seed.Topology.Subpath
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Integrating finite native chains of paths

The existing native `Path.concat` represents a finite chain with matching
endpoints. Integrability and integration concatenate piece by piece; no
smoothness of the concatenation at its joins is required. The empty chain
is the constant path and has integral zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Finset
open scoped unitInterval

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ} {ω : E → E →L[𝕜] F}

/-- An actual finite native chain is curve integrable whenever each of its
pieces is curve integrable. Matching endpoints are encoded by `Path.concat`;
no differentiability at a join is assumed.
@isnad1 id=curveint.1h7v.s8.f42557389b2a from=translated src=- shape=0b001044 vocab=42ffda22
-/
protected theorem CurveIntegrable.concat (p : Fin (n + 1) → E)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hγ : ∀ i, CurveIntegrable ω (γ i)) : CurveIntegrable ω (Path.concat p γ) := by
  induction n with
  | zero => simp only [Path.concat_zero]; exact CurveIntegrable.refl _ _
  | succ n ih =>
    rw [Path.concat_succ]
    exact (ih (p ∘ Fin.castSucc) (fun i => γ i.castSucc) (fun i => hγ i.castSucc)).trans
      (hγ (Fin.last n))

/-- The native integral of a finite chain is the sum of the actual native
piece integrals, including the empty chain. This extends integration to
piecewise C¹ paths without declaring their concatenation globally C¹.
@isnad1 id=eq.1h7v.s8.46f9f35564f0 from=translated src=- shape=77f679fb vocab=60876d86
-/
theorem curveIntegral_concat (p : Fin (n + 1) → E)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hγ : ∀ i, CurveIntegrable ω (γ i)) :
    curveIntegral ω (Path.concat p γ) = ∑ i : Fin n, curveIntegral ω (γ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Path.concat_succ]
    erw [curveIntegral_trans
      (CurveIntegrable.concat (p ∘ Fin.castSucc) (fun i => γ i.castSucc) (fun i => hγ i.castSucc))
      (hγ (Fin.last n)), ih _ _ (fun i => hγ i.castSucc), Fin.sum_univ_castSucc]

namespace Path

/-- A finite native concatenation remains in a set whenever its initial
point and all its pieces do. The initial point is needed for the empty chain.
@isnad1 id=mem.2h6v.s8.4f3fc9fcf0fb from=translated src=- shape=dc779a6a vocab=8db12d92
-/
theorem forall_mem_concat (p : Fin (n + 1) → E)
    (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ)) {s : Set E}
    (hp : p 0 ∈ s) (hγ : ∀ i, ∀ r, γ i r ∈ s) : ∀ r, concat p γ r ∈ s := by
  induction n with
  | zero => intro r; simpa only [concat_zero, Path.refl_apply] using hp
  | succ n ih =>
    intro r
    rw [concat_succ]
    have hr : (concat (p ∘ Fin.castSucc) (fun i => γ i.castSucc)).trans (γ (Fin.last n)) r ∈
        range (concat (p ∘ Fin.castSucc) (fun i => γ i.castSucc)) ∪ range (γ (Fin.last n)) := by
      rw [← Path.trans_range]
      exact mem_range_self r
    rcases hr with ⟨t, ht⟩ | ⟨t, ht⟩
    · erw [← ht]
      exact ih (p ∘ Fin.castSucc) (fun i => γ i.castSucc) hp (fun i => hγ i.castSucc) t
    · erw [← ht]
      exact hγ (Fin.last n) t

end Path
