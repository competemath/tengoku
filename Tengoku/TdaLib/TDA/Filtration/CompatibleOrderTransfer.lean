import Tengoku.TdaLib.TDA.Filtration.CompatibleOrder
import Tengoku.TdaLib.TDA.Filtration.OrderingEquivalent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v w
namespace TDA.Filtration
variable {V : Type u} {α : Type v} {β : Type w}
variable [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]
variable {f : FilterFunction K α} {g : FilterFunction K β}

/-- Keep exactly the given face enumeration when the new grades are monotone along it.-/
def CompatibleOrder.transfer (e : CompatibleOrder f)
    (hg : Monotone (g.value ∘ e.enum)) : CompatibleOrder g where
  enum := e.enum
  face_lt := e.face_lt
  monotone := hg

/-- Direct transfer preserves the supplied enumeration definitionally.
@isnad1 id=eq.1h7v.s7.e773684cc6cf from=translated src=- shape=3bee028f vocab=21c30c82
-/
theorem CompatibleOrder.transfer_enum (e : CompatibleOrder f)
    (hg : Monotone (g.value ∘ e.enum)) :
    (e.transfer hg).enum = e.enum := rfl

/-- Ordering equivalence transports monotonicity along a compatible enumeration.
@isnad1 id=monotone.1h7v.s7.a8841900f1f9 from=translated src=- shape=ab33a830 vocab=0416c9e7
-/
theorem OrderingEquivalent.monotone_comp (h : OrderingEquivalent f g)
    (e : CompatibleOrder f) : Monotone (g.value ∘ e.enum) := by
  intro i j hij
  exact (h (e.enum i) (e.enum j)).mp (e.monotone hij)

/-- Transfer an order along the comparisons shared by ordering-equivalent filters.-/
def CompatibleOrder.transferOfOrderingEquivalent (e : CompatibleOrder f)
    (h : OrderingEquivalent f g) : CompatibleOrder g :=
  e.transfer (h.monotone_comp e)

/-- Transfer by ordering equivalence preserves the supplied enumeration definitionally.
@isnad1 id=eq.1h7v.s6.6941528a9d79 from=translated src=- shape=f00e8a2b vocab=24e2c42d
-/
theorem CompatibleOrder.transferOfOrderingEquivalent_enum
    (e : CompatibleOrder f) (h : OrderingEquivalent f g) :
    (e.transferOfOrderingEquivalent h).enum = e.enum := rfl

end TDA.Filtration
