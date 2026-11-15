import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodMap
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups

def HasEquivariantPrimitive (N : ℕ) (f : CuspForm (Gamma0 N) 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    IsEquivariantPrimitive (Gamma0 N) F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

noncomputable def periodMap (N : ℕ) (f : CuspForm (Gamma0 N) 2) : Additive (Gamma0 N) →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F then h.choose_spec.2.2.1.periodHom else 0

/--
@isnad1 id=ex.1h3v.s10.d97126fcaff0 from=translated src=- shape=d218a22c vocab=45d5e26c
-/
theorem periodMap_def (N : ℕ) (f : CuspForm (Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : HasEquivariantPrimitive N f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitive N f F₀), periodMap N f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dite_eq_left h⟩

end ModularCurve
