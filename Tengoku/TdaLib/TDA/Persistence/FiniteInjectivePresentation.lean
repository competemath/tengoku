import Tengoku.TdaLib.TDA.Persistence.PrincipalDownsetInjective
import Tengoku.TdaLib.TDA.Persistence.RankProjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite injective presentations

Over a finite poset, the basis coordinates of a pointwise finite-dimensional
module give an embedding into a finite biproduct of principal-downset
injectives. Each basis coordinate contributes its own occurrence. An ordinary
injective module is exactly one for which this embedding admits a retraction.

This supplies finite pointwise finite-dimensional injective presentations used
in the two-injective step of BOOS, arXiv:2208.00300v3, Theorem 5.16. It makes no
minimality or direct-sum classification assertion.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteInjectivePresentation

open CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Finite P]

noncomputable section

local instance : Fintype P := Fintype.ofFinite P

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable (M : PModule.{u,0,u} k P)

/-- A separate occurrence for every basis coordinate at every grade.-/
abbrev Index := Σ p : P, Fin (Module.finrank k (M.obj p))

instance indexFintype : Fintype (Index M) := by unfold Index; infer_instance

/-- The principal-downset injective assigned to each occurrence.-/
abbrev family (t : Index M) : PModule.{u,0,u} k P := PrincipalDownsetInjective.module t.1

/-- The actual finite categorical biproduct of the selected injectives.-/
def module : PModule.{u,0,u} k P := ⨁ family M

/-- The finite biproduct is an ordinary injective object.
@isnad1 id=injectiv.0h3v.s6.eaf82b1efc6c from=translated src=- shape=70f3a147 vocab=c00a4e23
-/
instance isInjective : Injective (module M) := by
  unfold module
  have : ∀ t : Index M, Injective (family M t) := fun t =>
    PrincipalDownsetInjective.isInjective t.1
  infer_instance

/-- Its fibers are finite-dimensional.
@isnad1 id=finitedi.0h4v.s7.a2bfc899b1f6 from=translated src=- shape=62dd5a1c vocab=6fc35e52
-/
instance finiteDimensional (p : P) : FiniteDimensional k ((module M).obj p) := by
  exact FiniteBiproduct.finiteDimensional (family M) p

variable [∀ p, FiniteDimensional k (M.obj p)]

/-- The chosen finite-basis coordinate functional.-/
def coordinate (p : P) (j : Fin (Module.finrank k (M.obj p))) : M.obj p →ₗ[k] k :=
  (Module.finBasis k (M.obj p)).coord j

/-- Coextend the coordinate functional into its principal downset.-/
def summandMap (t : Index M) : M ⟶ family M t :=
  PrincipalDownsetInjective.extension t.1 M (coordinate M t.1 t.2)

/-- Assemble all coordinate coextensions into the finite biproduct.-/
def embedding : M ⟶ module M := biproduct.lift (summandMap M)

/-- Projection recovers the selected coordinate coextension.
@isnad1 id=eq.0h4v.s8.9fb303351452 from=translated src=- shape=0cd22a21 vocab=096faf87
-/
@[reassoc] theorem embedding_π (t : Index M) :
    embedding M ≫ biproduct.π (family M) t = summandMap M t := biproduct.lift_π _ _

/-- The coefficient of every projected component, both inside and outside the downset.
@isnad1 id=eq.0h6v.s12.182474a4c116 from=translated src=- shape=ba450b53 vocab=ab8a91e2
-/
theorem embedding_π_app_val (t : Index M) (q : P) (x : M.obj q) :
    (((biproduct.π (family M) t).app q).hom (((embedding M).app q).hom x) : k) =
      if h : q ≤ t.1 then coordinate M t.1 t.2 (structureMapLinear M h x) else 0 := by
  have h := congrArg (fun f : M ⟶ family M t => ((f.app q).hom x : k)) (embedding_π M t)
  exact h.trans (PrincipalDownsetInjective.extension_app_val t.1 M _ q x)

/-- At its own grade, a projected component is the original basis coordinate.
@isnad1 id=eq.0h6v.s12.879c5b817527 from=translated src=- shape=823173cb vocab=e8f83d2f
-/
@[simp] theorem embedding_coordinate (q : P) (j : Fin (Module.finrank k (M.obj q)))
    (x : M.obj q) :
    (((biproduct.π (family M) ⟨q, j⟩).app q).hom (((embedding M).app q).hom x) : k) =
      coordinate M q j x := by
  rw [embedding_π_app_val]
  simp

/-- The coordinates at grade `q` separate vectors, even in dimension zero.
@isnad1 id=injectiv.0h4v.s9.938d979625a4 from=translated src=- shape=50979141 vocab=46504971
-/
theorem component_injective (q : P) : Function.Injective ((embedding M).app q).hom := by
  intro x y h
  apply (Module.finBasis k (M.obj q)).repr.injective
  ext j
  have hj := congrArg (fun z => (((biproduct.π (family M) ⟨q, j⟩).app q).hom z : k)) h
  rw [embedding_coordinate, embedding_coordinate] at hj
  exact hj

/-- The coordinate embedding is a categorical monomorphism.
@isnad1 id=mono.0h3v.s7.2f34e51960bf from=translated src=- shape=4311ded7 vocab=490f3c11
-/
instance embedding_mono : Mono (embedding M) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro q
  exact (ModuleCat.mono_iff_injective _).mpr (component_injective M q)

/-- A chosen retraction of the coordinate embedding for an injective module.-/
def retraction [Injective M] : module M ⟶ M := Injective.factorThru (𝟙 M) (embedding M)

/-- The chosen retraction splits the coordinate embedding.
@isnad1 id=eq.0h3v.s8.6e0c6d2ff7d3 from=translated src=- shape=47332240 vocab=1c48d122
-/
@[reassoc (attr := simp)] theorem embedding_retraction [Injective M] :
    embedding M ≫ retraction M = 𝟙 M := Injective.comp_factorThru _ _

/-- Ordinary injectivity is equivalent to splitting the constructed embedding.
@isnad1 id=iff.0h3v.s8.3df53ac01a61 from=translated src=- shape=9a60a41a vocab=25fdae5a
-/
theorem injective_iff_splits : Injective M ↔
    ∃ r : module M ⟶ M, embedding M ≫ r = 𝟙 M := by
  constructor
  · intro h
    have := h
    exact ⟨retraction M, embedding_retraction M⟩
  · rintro ⟨r, hr⟩
    exact (show Retract M (module M) from ⟨embedding M, r, hr⟩).injective

/-- The finite pointwise finite-dimensional ordinary injective presentation.-/
def presentation : InjectivePresentation M where
  J := module M
  f := embedding M

/-- The presentation's actual injective target has finite-dimensional fibers.
@isnad1 id=finitedi.0h4v.s8.59eec7ae585c from=translated src=- shape=ae094cb1 vocab=a0a84313
-/
theorem presentation_finiteDimensional (p : P) :
    FiniteDimensional k ((presentation M).J.obj p) := finiteDimensional M p

end

end TDA.Persistence.FiniteInjectivePresentation
