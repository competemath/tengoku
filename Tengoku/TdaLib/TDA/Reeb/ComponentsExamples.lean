import Tengoku.TdaLib.TDA.Reeb.Components
import Tengoku.Seed.Topology.Connected.TotallyDisconnected

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path-component functor fixtures

Regression fixtures for `TDA.Reeb.componentFunctor` and `TDA.Reeb.componentNatTrans`:

* empty domain and empty base values;
* a disconnected domain, the discrete two-point space `Bool` over a one-point base, whose
  components at `⊤` are exactly two distinct classes;
* a noninjective natural map, the collapse from that `Bool` space to the one-point domain;
* the composition law at two nonidentity maps, the swap `Bool.not` followed by the collapse;
* a proper inclusion of open sets `{false} ≤ ⊤` for the identity on discrete `Bool`, where the
  inverse-image support changes.

The discrete classification uses only pinned totally-disconnected facts; it does not identify
path components with connected components. No global `Inhabited` or `Nonempty` instance is
added.
-/

open CategoryTheory

namespace TDA.Reeb.Examples

universe u v

/-- In a discrete space, joined points are equal (pinned totally-disconnected facts).-/
theorem eq_of_joined_of_discrete {T : Type*} [TopologicalSpace T] [DiscreteTopology T]
    {a b : T} (hab : Joined a b) : a = b := by
  obtain ⟨p⟩ := hab
  have hs := (isPreconnected_range p.continuous).subsingleton
  simpa using hs ⟨0, rfl⟩ ⟨1, rfl⟩

/-- The constant map from discrete `Bool` to a one-point base.-/
def boolToUnit : C(Bool, Unit) := ContinuousMap.const Bool ()

/-- The class of `b` in `C_{boolToUnit}(⊤)`.-/
def boolClass (b : Bool) : (componentFunctor boolToUnit).obj ⊤ :=
  ZerothHomotopy.mk ⟨b, TopologicalSpace.Opens.mem_top _⟩

/-- Exhaustive classification: `C_{boolToUnit}(⊤) ≃ Bool`.-/
def boolComponentsEquiv : (componentFunctor boolToUnit).obj ⊤ ≃ Bool where
  toFun := ZerothHomotopy.lift (fun x => x.1)
    (fun _ _ p => congrArg Subtype.val (eq_of_joined_of_discrete ⟨p⟩))
  invFun := boolClass
  left_inv c := by
    induction c using ZerothHomotopy.rec with
    | mk x => rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.0h1v.s9.a83ae4b976a3 from=translated src=- shape=f32a365a vocab=97f444d8
-/
theorem boolComponentsEquiv_boolClass (b : Bool) : boolComponentsEquiv (boolClass b) = b := rfl

/--
@isnad1 id=ne.0h0v.s6.e48da212bbbc from=translated src=- shape=366f654f vocab=f5dea409
-/
theorem boolClass_false_ne_true : boolClass false ≠ boolClass true := fun hc => by
  have hb := congrArg boolComponentsEquiv hc
  rw [boolComponentsEquiv_boolClass, boolComponentsEquiv_boolClass] at hb
  exact Bool.false_ne_true hb

/--
@isnad1 id=or.0h1v.s8.8865ded032c3 from=translated src=- shape=559dc770 vocab=f5dea409
-/
theorem boolClass_exhaustive (c : (componentFunctor boolToUnit).obj ⊤) :
    c = boolClass false ∨ c = boolClass true := by
  rcases hb : boolComponentsEquiv c with _ | _
  · left; rw [← boolComponentsEquiv.symm_apply_apply c, hb]; rfl
  · right; rw [← boolComponentsEquiv.symm_apply_apply c, hb]; rfl

/-- Collapse `Bool → Unit` over the same constant base map, as a natural transformation.-/
def collapseNatTrans : componentFunctor boolToUnit ⟶ componentFunctor (ContinuousMap.id Unit) :=
  componentNatTrans (ContinuousMap.const Bool ()) (fun _ => rfl)

/--
@isnad1 id=eq.0h0v.s10.80e5ea8d8205 from=translated src=- shape=dc33f49c vocab=a93db6cf
-/
theorem collapseNatTrans_identifies :
    collapseNatTrans.app ⊤ (boolClass false) = collapseNatTrans.app ⊤ (boolClass true) := rfl

/--
@isnad1 id=not.0h0v.s10.dbb78f735adf from=translated src=- shape=068c0fb5 vocab=bf98da62
-/
theorem collapseNatTrans_not_injective : ¬ Function.Injective (collapseNatTrans.app ⊤) :=
  fun hinj => boolClass_false_ne_true (hinj collapseNatTrans_identifies)

/-- The nonidentity swap `Bool.not` over the same constant base map.-/
def boolNot : C(Bool, Bool) := ⟨not, continuous_of_discreteTopology⟩

/-- The swap as a natural transformation `C_{boolToUnit} ⟶ C_{boolToUnit}`.-/
def swapNatTrans : componentFunctor boolToUnit ⟶ componentFunctor boolToUnit :=
  componentNatTrans boolNot (fun _ => rfl)

/--
@isnad1 id=eq.0h1v.s9.e3460a5f14f5 from=translated src=- shape=8339cae4 vocab=dcbaae79
-/
theorem swapNatTrans_boolClass (b : Bool) : swapNatTrans.app ⊤ (boolClass b) = boolClass (!b) :=
  rfl

/-- Composition law at two nonidentity maps: swap, then collapse.
@isnad1 id=eq.0h0v.s7.5e2a695b96f1 from=translated src=- shape=0e83986a vocab=dcd40936
-/
theorem collapse_comp_swap :
    componentNatTrans ((ContinuousMap.const Bool ()).comp boolNot) (fun _ => rfl) =
      swapNatTrans ≫ collapseNatTrans :=
  componentNatTrans_comp boolNot (fun _ => rfl) (ContinuousMap.const Bool ()) (fun _ => rfl)
    (fun _ => rfl)

/-- Proper open inclusion: identity on discrete `Bool`, `U = {false}`, `V = ⊤`.-/
def falseOpen : TopologicalSpace.Opens Bool := ⟨{false}, isOpen_discrete _⟩

/--
@isnad1 id=le.0h0v.s6.21bc466ccf8f from=translated src=- shape=e0b023cc vocab=d4bca7bb
-/
theorem falseOpen_le_top : falseOpen ≤ ⊤ := le_top

/--
@isnad1 id=ne.0h0v.s6.5c0a8870ee7f from=translated src=- shape=e0b023cc vocab=f96d66a1
-/
theorem falseOpen_ne_top : falseOpen ≠ ⊤ := fun hU => by
  have : (true : Bool) ∈ falseOpen := hU ▸ TopologicalSpace.Opens.mem_top true
  simp [falseOpen] at this

/--
@isnad1 id=eq.0h1v.s6.7c7230081122 from=translated src=- shape=90ccd6f5 vocab=a3cf948d
-/
theorem true_absent_falseOpen (x : {b : Bool // ContinuousMap.id Bool b ∈ falseOpen}) :
    x.1 = false := x.2

/--
@isnad1 id=eq.0h0v.s10.25a4f462f142 from=translated src=- shape=69b512bc vocab=0035cc4e
-/
theorem falseOpen_inclusion_mk :
    (componentFunctor (ContinuousMap.id Bool)).map (homOfLE falseOpen_le_top)
        (ZerothHomotopy.mk ⟨false, rfl⟩) =
      ZerothHomotopy.mk ⟨false, TopologicalSpace.Opens.mem_top _⟩ := rfl

end TDA.Reeb.Examples
