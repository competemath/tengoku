import Tengoku.Seed.Probability.HasLaw
import Tengoku.Seed.MeasureTheory.Integral.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Selecting distinct coordinates and mixing independent product samples

Injective coordinate selection preserves the corresponding product law. In
particular, coordinatewise selection between two independent copies preserves
their product law. These are law-level tools for finite-product integration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ProbabilityTheory

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace E]
  (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)]

/-- Selecting distinct coordinates of a product sample has the selected product
law; the individual coordinate laws need not be equal.
@isnad1 id=haslaw.1h5v.s6.f1888b9f04c9 from=translated src=- shape=4a13f288 vocab=67219dec
-/
theorem hasLaw_pi_select (g : κ → ι) (hg : Function.Injective g) :
    HasLaw (fun x : ι → E => fun j => x (g j))
      (Measure.pi (fun j => ν (g j))) (Measure.pi ν) := by
  have hi : iIndepFun (fun i (x : ι → E) => x i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact (hi.precomp hg).hasLaw_pi (fun j => (measurePreserving_eval ν (g j)).hasLaw)

/-- A product of integrable functions of distinct product coordinates is
integrable. This permits unused coordinates in the original product space.
@isnad1 id=integrab.2h7v.s7.f0319a969e5a from=translated src=- shape=f5958c64 vocab=97b587d0
-/
theorem integrable_prod_pi_select {𝕜 : Type*} [RCLike 𝕜]
    (g : κ → ι) (hg : Function.Injective g) (f : κ → E → 𝕜)
    (hf : ∀ j, Integrable (f j) (ν (g j))) :
    Integrable (fun x : ι → E => ∏ j, f j (x (g j))) (Measure.pi ν) := by
  have hm := (hasLaw_pi_select ν g hg).measurePreserving (by fun_prop)
  exact hm.integrable_comp_of_integrable (Integrable.fintype_prod hf)

/-- The expectation of a product of functions of distinct product coordinates
is the product of their expectations.
@isnad1 id=eq.2h7v.s8.5bede7c7471e from=translated src=- shape=011e8bd5 vocab=c9095f7e
-/
theorem integral_prod_pi_select {𝕜 : Type*} [RCLike 𝕜]
    (g : κ → ι) (hg : Function.Injective g) (f : κ → E → 𝕜)
    (hf : ∀ j, Integrable (f j) (ν (g j))) :
    (∫ x : ι → E, ∏ j, f j (x (g j)) ∂Measure.pi ν) =
      ∏ j, ∫ x, f j x ∂ν (g j) := by
  calc
    _ = ∫ x : κ → E, ∏ j, f j (x j) ∂Measure.pi (fun j => ν (g j)) := by
      simpa only [Function.comp_apply] using
        (hasLaw_pi_select ν g hg).integral_comp
          (Integrable.fintype_prod hf).aestronglyMeasurable
    _ = _ := integral_fintype_prod_eq_prod _

/-- Replacing any chosen subset of coordinates by an independent copy preserves
the complete product law.
@isnad1 id=haslaw.0h4v.s7.eaea22afc8b8 from=translated src=- shape=a1871e3c vocab=d215ca0a
-/
theorem hasLaw_pi_mix (p : ι → Prop) [DecidablePred p] :
    HasLaw (fun x : (ι → E) × (ι → E) =>
      fun i => if p i then x.1 i else x.2 i)
      (Measure.pi ν) ((Measure.pi ν).prod (Measure.pi ν)) := by
  let g : ι → ι ⊕ ι := fun i => if p i then Sum.inl i else Sum.inr i
  have hg : Function.Injective g := by
    intro i j hij
    have he := congrArg (Sum.elim id id) hij
    simpa [g, apply_ite] using he
  haveI : ∀ j : ι ⊕ ι, IsProbabilityMeasure (Sum.elim ν ν j) := by
    intro j
    cases j with
    | inl i => simpa only [Sum.elim_inl] using (inferInstance : IsProbabilityMeasure (ν i))
    | inr i => simpa only [Sum.elim_inr] using (inferInstance : IsProbabilityMeasure (ν i))
  have hs := hasLaw_pi_select (fun j : ι ⊕ ι => Sum.elim ν ν j) g hg
  have hc := (measurePreserving_sumPiEquivProdPi_symm
    (fun j : ι ⊕ ι => Sum.elim ν ν j)).hasLaw
  convert hs.comp hc using 1
  · funext x i
    dsimp [g, Function.comp_def, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi]
    split_ifs <;> rfl
  · congr 1
    funext i
    dsimp [g]
    split_ifs <;> rfl
  · simp

end ProbabilityTheory
