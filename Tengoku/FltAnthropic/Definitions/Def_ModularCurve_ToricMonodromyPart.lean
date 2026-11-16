import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]

def toricMonodromyPart (q : ℕ) (I : Subgroup G) : Submodule HeckeAlg J :=
  Submodule.span HeckeAlg
    {y : J | ∃ σ ∈ I, ∃ x : J, (∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ m • x = 0) ∧ y = σ • x - x}

/--
@isnad1 id=mem.4h7v.s8.d7cd4c8f2540 from=translated src=- shape=4f7f76ac vocab=00b4be43
-/
theorem smul_sub_self_mem_toricMonodromyPart {q : ℕ} {I : Subgroup G} {σ : G} (hσ : σ ∈ I) {x : J}
    {m : ℕ} (hm : 0 < m) (hmq : m.Coprime q) (hx : m • x = 0) :
    σ • x - x ∈ toricMonodromyPart (J := J) q I :=
  Submodule.subset_span ⟨σ, hσ, x, ⟨m, hm, hmq, hx⟩, rfl⟩

end ModularCurve

end
