import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.CoindBasic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A basis for coinduced representations

This file constructs an explicit basis for the coinduced representation
`FDRep.coind H σ`.

If `bV : Module.Basis ι k σ` is a basis of the representation of the
subgroup `H`, then `FDRep.coindBasis H σ bV` is a basis of the coinduced
representation indexed by
w
`Quotient (QuotientGroup.rightRel H) × ι`.

The basis vector indexed by `(q, i)` is supported on the right coset `q`; at an
element `x` of that coset it is obtained by transporting the basis vector
`bV i` using the element `x * q.out⁻¹ ∈ H`.
-/

universe u v

variable {k : Type u} {G : Type u}

namespace FDRep

variable [CommRing k] [IsNoetherianRing k] [Group G] [Finite G]

/--
The coefficient functional of a coinduced representation at coset `q` and basis
index `i`.-/
noncomputable def coindCoeff
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι) :
    (FDRep.coind I σ) →ₗ[k] k :=
  (Finsupp.lapply i).comp
    (bV.repr.toLinearMap.comp (coindEval I σ q.out))

/--
@isnad1 id=eq.0h9v.s12.a0b4863b06d0 from=translated src=- shape=5b40177f vocab=d100b78a
-/
@[simp]
lemma coindCoeff_apply
    (I : Subgroup G) (σ : FDRep k I)
    {ι : Type*}
    (bV : Module.Basis ι k σ)
    (q : Quotient (QuotientGroup.rightRel I)) (i : ι)
    (v : (FDRep.coind I σ)) :
    coindCoeff I σ bV q i v = bV.repr (v.val q.out) i :=
  rfl

/-! ### Finrank of coinduced representations -/

section Finrank

variable {k : Type u} [Field k]

end Finrank

end FDRep
