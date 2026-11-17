import Tengoku.PaperCLean.PaperC.Affine.StartSystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The affine system of two touching starts

Two starts of the same positive length `L`, based at `x` and `x + L`,
are encoded by a single system with row type `Sum (Fin L) (Fin L)`.
The left summand contains the rows of the start at `x`, and the right
summand those of the start at `x + L`.
-/

namespace PaperC
namespace Affine

noncomputable section

/-- A row of the joint system of starts at `x` and `x + L`.-/
def touchingRow (M x L : ℕ) :
    Sum (Fin L) (Fin L) → SampleSpace M →ₗ[F₂] F₂
  | Sum.inl i => startRow M x L i
  | Sum.inr i => startRow M (x + L) L i

/-- The joint linear system of two touching starts.-/
def touchingSystem (M x L : ℕ) :
    SampleSpace M →ₗ[F₂] (Sum (Fin L) (Fin L) → F₂) :=
  LinearMap.pi (touchingRow M x L)

/-- The joint right-hand side: one boundary equation in each start block.-/
def touchingRhs (L : ℕ) : Sum (Fin L) (Fin L) → F₂
  | Sum.inl i => startRhs L i
  | Sum.inr i => startRhs L i

/--
@isnad1 id=eq.0h5v.s9.4da29ba98c8b from=translated src=- shape=16eff5d0 vocab=752080a6
-/
@[simp]
theorem touchingSystem_apply_inl
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    touchingSystem M x L ω (Sum.inl i) =
      startSystem M x L ω i := by
  rfl

/--
@isnad1 id=eq.0h5v.s9.d5730c66bcb5 from=translated src=- shape=af0916ae vocab=dcc42e9c
-/
@[simp]
theorem touchingSystem_apply_inr
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    touchingSystem M x L ω (Sum.inr i) =
      startSystem M (x + L) L ω i := by
  rfl

/--
@isnad1 id=eq.0h2v.s4.018a50fe8923 from=translated src=- shape=c542b7f0 vocab=cf297b30
-/
@[simp]
theorem touchingRhs_apply_inl (L : ℕ) (i : Fin L) :
    touchingRhs L (Sum.inl i) = startRhs L i :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.e658fadfa2a0 from=translated src=- shape=c542b7f0 vocab=5b5141d4
-/
@[simp]
theorem touchingRhs_apply_inr (L : ℕ) (i : Fin L) :
    touchingRhs L (Sum.inr i) = startRhs L i :=
  rfl

/--
Solving the joint affine system is equivalent to simultaneous starts at
`x` and `x + L`.
@isnad1 id=iff.1h4v.s8.7fa07d818eda from=translated src=- shape=baa61d6d vocab=c2294c98
-/
theorem touchingSystem_eq_touchingRhs_iff
    {M x L : ℕ} (ω : SampleSpace M) (hL : 0 < L) :
    touchingSystem M x L ω = touchingRhs L ↔
      StartEvent (valueBit ω) x L ∧
        StartEvent (valueBit ω) (x + L) L := by
  rw [← startSystem_eq_startRhs_iff ω hL,
    ← startSystem_eq_startRhs_iff ω hL]
  constructor
  · intro h
    constructor
    · funext i
      exact congrFun h (Sum.inl i)
    · funext i
      exact congrFun h (Sum.inr i)
  · rintro ⟨hleft, hright⟩
    funext i
    cases i with
    | inl i => exact congrFun hleft i
    | inr i => exact congrFun hright i

/--
Every integer vertex used by the two touching starts is below the cylinder
cutoff `dyadicCutoff N (2 * L)`.
@isnad1 id=le.2h4v.s6.454fdbc1048c from=translated src=- shape=8eae86c9 vocab=fa53c847
-/
theorem touchingWindow_le_dyadicCutoff
    {N L x j : ℕ} (hx : x ∈ dyadicBlock N) (hj : j < 2 * L) :
    x + j ≤ dyadicCutoff N (2 * L) := by
  have hxUpper :
      x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  unfold dyadicCutoff
  omega

/-- The omitted root `x - 1` is covered by the same touching cylinder.
@isnad1 id=le.1h3v.s5.4ede3018927c from=translated src=- shape=765fda63 vocab=f7e1ef0f
-/
theorem touchingRoot_le_dyadicCutoff
    {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    x - 1 ≤ dyadicCutoff N (2 * L) := by
  have hxUpper :
      x < 2 * N :=
    (Finset.mem_Ico.mp (by simpa [dyadicBlock] using hx)).2
  unfold dyadicCutoff
  omega

end

end Affine
end PaperC
