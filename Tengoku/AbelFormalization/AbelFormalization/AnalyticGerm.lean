import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Topology.Germ
import Tengoku.Seed.Algebra.Ring.Subring.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The actual ring of real-analytic germs

The coefficient ring in Section 3 consists of analytic germs, with equality
given by agreement on a neighborhood. This module constructs it as a subring
of mathlib's neighborhood germs and supplies analytic representatives and the
evaluation homomorphism. No Noetherian or dimension property is assumed.
-/

noncomputable section

namespace AbelFormalization

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Functions analytic at a fixed point form a subring of all real functions.-/
def analyticFunctionSubring (x : E) : Subring (E → ℝ) where
  carrier := {f | AnalyticAt ℝ f x}
  zero_mem' := analyticAt_const
  one_mem' := analyticAt_const
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  neg_mem' hf := hf.neg

/-- The subring of neighborhood germs admitting an analytic representative.-/
def analyticGermSubring (x : E) : Subring (Germ (𝓝 x) ℝ) :=
  (analyticFunctionSubring x).map (Germ.coeRingHom (𝓝 x))

/-- The ring of real-analytic germs at a specified point.-/
abbrev AnalyticGermAt (x : E) := analyticGermSubring x

/-- The manuscript's ring of real-analytic germs in `p` variables at zero.-/
abbrev RealAnalyticGerm (p : ℕ) := AnalyticGermAt (0 : Fin p → ℝ)

/-- Pass from an analytic representative to its neighborhood germ.-/
def analyticGermOf {x : E} (f : E → ℝ) (hf : AnalyticAt ℝ f x) : AnalyticGermAt x :=
  ⟨(f : Germ (𝓝 x) ℝ), ⟨f, hf, rfl⟩⟩

/--
@isnad1 id=iff.2h4v.s8.4924bf06bc6e from=translated src=- shape=15328c19 vocab=2bff848a
-/
theorem analyticGermOf_eq_iff {x : E} {f g : E → ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    analyticGermOf f hf = analyticGermOf g hg ↔ f =ᶠ[𝓝 x] g := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

/-- Every element of the ring has a genuinely analytic representative.
@isnad1 id=ex.0h3v.s8.b1cad22075b1 from=translated src=- shape=a681c558 vocab=c48cbb59
-/
theorem exists_analyticGerm_representative {x : E} (g : AnalyticGermAt x) :
    ∃ f : E → ℝ, ∃ hf : AnalyticAt ℝ f x, g = analyticGermOf f hf := by
  obtain ⟨f, hf, he⟩ := g.property
  refine ⟨f, hf, ?_⟩
  apply Subtype.ext
  exact he.symm

/-- Evaluation of the germ at its base point is well-defined and is a ring map.-/
def analyticGermValue (x : E) : AnalyticGermAt x →+* ℝ :=
  Germ.valueRingHom.comp (analyticGermSubring x).subtype

/--
@isnad1 id=eq.1h3v.s10.496693d0016a from=translated src=- shape=9168bec7 vocab=cd9012b0
-/
@[simp]
theorem analyticGermValue_of {x : E} (f : E → ℝ) (hf : AnalyticAt ℝ f x) :
    analyticGermValue x (analyticGermOf f hf) = f x := rfl

/--
@isnad1 id=surjecti.0h2v.s10.117f555f2da1 from=translated src=- shape=b02c5692 vocab=6ef8113a
-/
theorem analyticGermValue_surjective (x : E) : Function.Surjective (analyticGermValue x) := by
  intro c
  exact ⟨analyticGermOf (fun _ : E => c) analyticAt_const, rfl⟩

/--
@isnad1 id=eq.2h4v.s10.041ee6453c49 from=translated src=- shape=3715d13c vocab=07a24f58
-/
@[simp]
theorem analyticGermOf_add {x : E} {f g : E → ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    analyticGermOf (f + g) (hf.add hg) = analyticGermOf f hf + analyticGermOf g hg := rfl

/--
@isnad1 id=eq.2h4v.s10.88084f9ccf52 from=translated src=- shape=3715d13c vocab=a48063ee
-/
@[simp]
theorem analyticGermOf_mul {x : E} {f g : E → ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    analyticGermOf (f * g) (hf.mul hg) = analyticGermOf f hf * analyticGermOf g hg := rfl

end AbelFormalization
