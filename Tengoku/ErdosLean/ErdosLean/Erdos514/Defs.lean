import Tengoku.ErdosLean.ErdosLean.Erdos514.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős #514 — shared definitions

* `shift f n`: the iterated Taylor shift, `shift f 0 = f`,
  `shift f (n+1) = dslope (shift f n) 0`; for `z ≠ 0`,
  `shift f n z = (f z - ∑_{k<n} aₖ zᵏ) / zⁿ` where `aₖ = shift f k 0` are the Taylor
  coefficients.  For entire `f` every `shift f n` is entire (removable singularity).
* `superlevel g K = {z | K < ‖g z‖}` and `tract g K z₀`, the connected component of the
  superlevel set through `z₀`.
-/

open Set

namespace Erdos514

/-- Iterated Taylor shift of `f` at `0`.-/
noncomputable def shift (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (shift f n) 0

/--
@isnad1 id=eq.0h1v.s4.7a5a3074597e from=translated src=- shape=a8e85303 vocab=f945b333
-/
@[simp] lemma shift_zero (f : ℂ → ℂ) : shift f 0 = f := rfl

/--
@isnad1 id=eq.0h2v.s5.35c7088ae92c from=translated src=- shape=abd3f1a6 vocab=e48414fc
-/
@[simp] lemma shift_succ (f : ℂ → ℂ) (n : ℕ) : shift f (n + 1) = dslope (shift f n) 0 := rfl

/-- The superlevel set `{z | K < ‖g z‖}`.-/
def superlevel (g : ℂ → ℂ) (K : ℝ) : Set ℂ := {z | K < ‖g z‖}

/-- The tract of `g` at level `K` through `z₀`: the connected component of
`{z | K < ‖g z‖}` containing `z₀` (empty if `‖g z₀‖ ≤ K`).-/
def tract (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) : Set ℂ := connectedComponentIn (superlevel g K) z₀

/--
@isnad1 id=iff.0h3v.s4.905f264476bf from=translated src=- shape=7572d0ba vocab=efc964b4
-/
lemma mem_superlevel {g : ℂ → ℂ} {K : ℝ} {z : ℂ} : z ∈ superlevel g K ↔ K < ‖g z‖ := Iff.rfl

/--
@isnad1 id=isopen.1h2v.s5.917f45b59c4e from=translated src=- shape=69fd229e vocab=a4d867eb
-/
lemma isOpen_superlevel {g : ℂ → ℂ} (hg : Continuous g) (K : ℝ) : IsOpen (superlevel g K) :=
  isOpen_lt continuous_const (continuous_norm.comp hg)

/--
@isnad1 id=isopen.1h3v.s5.20215d081cb2 from=translated src=- shape=a6b1e109 vocab=4d40fc12
-/
lemma isOpen_tract {g : ℂ → ℂ} (hg : Continuous g) (K : ℝ) (z₀ : ℂ) :
    IsOpen (tract g K z₀) :=
  (isOpen_superlevel hg K).connectedComponentIn

/--
@isnad1 id=le.0h3v.s4.b1afad1aed65 from=translated src=- shape=84f7bbfe vocab=bdb408e3
-/
lemma tract_subset_superlevel (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) :
    tract g K z₀ ⊆ superlevel g K :=
  connectedComponentIn_subset _ _

/--
@isnad1 id=isprecon.0h3v.s4.61d713ee63f7 from=translated src=- shape=cd3ac19a vocab=8dcc083e
-/
lemma isPreconnected_tract (g : ℂ → ℂ) (K : ℝ) (z₀ : ℂ) : IsPreconnected (tract g K z₀) :=
  isPreconnected_connectedComponentIn

/--
@isnad1 id=mem.1h3v.s4.3e059253d7a8 from=translated src=- shape=98262eb3 vocab=8332883c
-/
lemma mem_tract_self {g : ℂ → ℂ} {K : ℝ} {z₀ : ℂ} (h : K < ‖g z₀‖) : z₀ ∈ tract g K z₀ :=
  mem_connectedComponentIn h

end Erdos514
