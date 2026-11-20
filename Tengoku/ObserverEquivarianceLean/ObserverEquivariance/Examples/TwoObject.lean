import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Components
import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.ProductModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A two-object base with a noninvertible arrow (paper example after `prop:nocleavage`)

Paper labels covered:
* the example following `prop:nocleavage`: the base with two objects `0, 1` and one nonidentity
  arrow `0 → 1` (`hom_subsingleton`, `hom_one_zero_isEmpty`), `G = C₂`, the product
  presentation `O = S × Pair(C₂)` (four objects, `card_objects`);
  equivariant automorphisms over the identity flip the two fibers independently, giving
  `C₂ × C₂`; preserving the chosen comparison `(0,g) → (1,g)` forces the two flips to agree,
  leaving the diagonal `C₂`;
* `prop:nocleavage` and `prop:components` / `def:lifts` — used through
  `kerΦEquivOverMulEquiv`, `autEquivOver_preservesCleavage_iff`, and
  `mem_range_autBoxGOverToAutEquivOver_iff` (module `Components`).

Model.
* The base is `Fin 2` with its preorder category structure (`Preorder.smallCategory`): the only
  nonidentity arrow is `0 ⟶ 1`.  It is connected, the arrow `0 ⟶ 1` is not an isomorphism, and
  `StrictAut (Fin 2)` is trivial, so the only choice of base subgroup is `H = ⊤ = ⊥`.
* `G = Multiplicative (ZMod 2)` (the cyclic group `C₂`), `d = productData (Fin 2) G`.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

namespace TwoObjectExample

/-! ## 1. The base `0 → 1` -/

/-- The unique nonidentity arrow `0 ⟶ 1` of the two-object base (paper example after
    `prop:nocleavage`).-/
def arrow01 : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

/-- Every hom-set of the base is a subsingleton (paper example after `prop:nocleavage`: "one
    nonidentity arrow").-/
theorem hom_subsingleton (a b : Fin 2) : Subsingleton (a ⟶ b) := inferInstance

/-- There is no arrow `1 ⟶ 0` (paper example after `prop:nocleavage`: "one nonidentity arrow
    `0 → 1`"); together with `hom_subsingleton`, `arrow01` is the only nonidentity arrow.-/
theorem hom_one_zero_isEmpty : IsEmpty ((1 : Fin 2) ⟶ 0) :=
  ⟨fun f => absurd (leOfHom f) (by decide)⟩

/-- The base arrow `0 ⟶ 1` is genuinely noninvertible (paper example after `prop:nocleavage`:
    "a genuinely noninvertible base arrow").-/
theorem arrow01_not_isIso : ¬ IsIso arrow01 := by
  intro h
  have h10 : (1 : Fin 2) ≤ 0 := leOfHom (inv arrow01)
  exact absurd h10 (by decide)

/-! ## 2. The product model and the unrestricted kernel `C₂ × C₂` -/

/-- The cyclic group of order two, `C₂ = Multiplicative (ZMod 2)` (paper example after
    `prop:nocleavage`: `G = C₂`).-/
abbrev C2 := Multiplicative (ZMod 2)

/-- The product presentation `O = Fin 2 × Pair(C₂)` over the two-object base, with its four
    objects (paper example after `prop:nocleavage`: "The product has four objects").-/
abbrev twoObjData : OEData C2 (CategoryTheory.Prod.fst (Fin 2) (Pair C2)) :=
  productData (Fin 2) C2

/-- The objects of `Pair X` are the elements of `X` (helper for paper example after
    `prop:nocleavage`: "The product has four objects").-/
def pairEquiv (X : Type*) : Pair X ≃ X := ⟨Pair.pt, Pair.mk, fun _ => rfl, fun _ => rfl⟩

/-- The product `O = Fin 2 × Pair(C₂)` has four objects (paper example after `prop:nocleavage`:
    "The product has four objects").-/
theorem card_objects : Nat.card (Fin 2 × Pair C2) = 4 := by
  rw [Nat.card_prod, Nat.card_congr (pairEquiv C2), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  rfl

/-- Functions on the two base objects are pairs, as groups: `(Fin 2 → G) ≃* G × G`,
    `γ ↦ (γ 0, γ 1)` (helper for paper example after `prop:nocleavage`, `G^{Ob S} = G × G`).-/
def finTwoFunMulEquiv (G : Type*) [Group G] : (Fin 2 → G) ≃* G × G where
  toFun γ := (γ 0, γ 1)
  invFun x := ![x.1, x.2]
  left_inv γ := funext fun i => by fin_cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- (helper for paper example after `prop:nocleavage`)-/
@[simp] theorem finTwoFunMulEquiv_apply (G : Type*) [Group G] (γ : Fin 2 → G) :
    finTwoFunMulEquiv G γ = (γ 0, γ 1) := rfl

/-- Equivariant automorphisms over the identity flip the two fibers independently (paper example
    after `prop:nocleavage`): `(ΦEquivOver d ⊤).ker ≃* C₂ × C₂`, via `prop:nocleavage`
    (`kerΦEquivOverMulEquiv`), `e = Λ_γ ↦ (γ 0, γ 1)`.-/
noncomputable def kerEquivProd : (ΦEquivOver twoObjData ⊤).ker ≃* C2 × C2 :=
  (kerΦEquivOverMulEquiv twoObjData ⊤).trans (finTwoFunMulEquiv C2)

/-! ## 3. The transport-preserving kernel is the diagonal `C₂` -/

/-- The diagonal subgroup `{(a, a)}` of `G × G` (paper example after `prop:nocleavage`:
    "leaving the diagonal `C₂`").-/
def diagSubgroup (G : Type*) [Group G] : Subgroup (G × G) where
  carrier := {x | x.1 = x.2}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by
    show x.1 * y.1 = x.2 * y.2
    rw [show x.1 = x.2 from hx, show y.1 = y.2 from hy]
  inv_mem' {x} hx := by
    show x.1⁻¹ = x.2⁻¹
    rw [show x.1 = x.2 from hx]

/-- (paper example after `prop:nocleavage`)-/
theorem mem_diagSubgroup {G : Type*} [Group G] (x : G × G) : x ∈ diagSubgroup G ↔ x.1 = x.2 :=
  Iff.rfl

/-- The diagonal is a copy of `G`, `(a, a) ↦ a` (paper example after `prop:nocleavage`).-/
def diagMulEquiv (G : Type*) [Group G] : diagSubgroup G ≃* G where
  toFun x := x.1.1
  invFun a := ⟨(a, a), rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl x.2)
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Transport-preserving lifts over the identity are, in particular, unrestricted lifts over the
    identity (paper example after `prop:nocleavage`, via the forgetful map of `prop:nocleavage`
    vs `def:lifts`).-/
def transportKerToKer : (ΦOver twoObjData ⊤).ker →* (ΦEquivOver twoObjData ⊤).ker :=
  ((autBoxGOverToAutEquivOver twoObjData ⊤).comp (ΦOver twoObjData ⊤).ker.subtype).codRestrict
    (ΦEquivOver twoObjData ⊤).ker (fun e => MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 e.2))

/-- The flips `(γ 0, γ 1) ∈ C₂ × C₂` of a transport-preserving automorphism over the identity
    (paper example after `prop:nocleavage`).-/
noncomputable def transportKerToProd : (ΦOver twoObjData ⊤).ker →* C2 × C2 :=
  (kerEquivProd).toMonoidHom.comp transportKerToKer

/-- A transport-preserving automorphism over the identity is determined by its two flips (paper
    example after `prop:nocleavage`).-/
theorem transportKerToProd_injective : Function.Injective transportKerToProd := by
  intro e₁ e₂ h
  have h' : transportKerToKer e₁ = transportKerToKer e₂ := (kerEquivProd).injective h
  have h'' : autBoxGOverToAutEquivOver twoObjData ⊤ e₁.1
      = autBoxGOverToAutEquivOver twoObjData ⊤ e₂.1 := congrArg Subtype.val h'
  exact Subtype.ext (autBoxGOverToAutEquivOver_injective twoObjData ⊤ h'')

/-- Preserving the chosen comparison `(0, g) → (1, g)` forces the two flips to agree, and every
    agreeing pair occurs (paper example after `prop:nocleavage`): the image of the
    transport-preserving kernel `(ΦOver d ⊤).ker` in `C₂ × C₂` is exactly the diagonal.-/
theorem transportKerToProd_range : transportKerToProd.range = diagSubgroup C2 := by
  ext x
  rw [MonoidHom.mem_range, mem_diagSubgroup]
  constructor
  · rintro ⟨e, rfl⟩
    have pc : PreservesCleavage twoObjData (autBoxGOverToAutEquivOver twoObjData ⊤ e.1).hom
        (autBoxGOverToAutEquivOver twoObjData ⊤ e.1).base.1.hom :=
      (mem_range_autBoxGOverToAutEquivOver_iff twoObjData ⊤ _).1 ⟨e.1, rfl⟩
    exact (autEquivOver_preservesCleavage_iff twoObjData ⊤ _).1 pc arrow01
  · intro hx
    set k := (kerEquivProd).symm x with hk_def
    have hk : finTwoFunMulEquiv C2 (kerΦEquivOverMulEquiv twoObjData ⊤ k) = x :=
      (kerEquivProd).apply_symm_apply x
    have hconst : ∀ s : Fin 2, kerΦEquivOverMulEquiv twoObjData ⊤ k s = x.1 :=
      Fin.forall_fin_two.2 ⟨congrArg Prod.fst hk, (congrArg Prod.snd hk).trans hx.symm⟩
    have pc : PreservesCleavage twoObjData k.1.hom k.1.base.1.hom :=
      (autEquivOver_preservesCleavage_iff twoObjData ⊤ k.1).2 fun {s t} _ =>
        (hconst s).trans (hconst t).symm
    obtain ⟨e, he⟩ := (mem_range_autBoxGOverToAutEquivOver_iff twoObjData ⊤ k.1).2 pc
    have hmem : e ∈ (ΦOver twoObjData ⊤).ker := by
      rw [MonoidHom.mem_ker]
      show ΦEquivOver twoObjData ⊤ (autBoxGOverToAutEquivOver twoObjData ⊤ e) = 1
      rw [he]
      exact MonoidHom.mem_ker.1 k.2
    refine ⟨⟨e, hmem⟩, ?_⟩
    have hkk : transportKerToKer ⟨e, hmem⟩ = k := Subtype.ext he
    show kerEquivProd (transportKerToKer ⟨e, hmem⟩) = x
    rw [hkk, hk_def, MulEquiv.apply_symm_apply]

/-- The transport-preserving kernel over the identity is the diagonal `C₂` (paper example after
    `prop:nocleavage`): `(ΦOver d ⊤).ker ≃* C₂`, `e ↦` its common flip.-/
noncomputable def transportKerMulEquiv : (ΦOver twoObjData ⊤).ker ≃* C2 :=
  (MonoidHom.ofInjective transportKerToProd_injective).trans
    ((MulEquiv.subgroupCongr transportKerToProd_range).trans (diagMulEquiv C2))

/-! ## 4. Transport preservation is a genuine restriction -/

/-- The diagonal is a proper subgroup of `C₂ × C₂` (paper example after `prop:nocleavage`):
    transport preservation cuts the unrestricted kernel `C₂ × C₂` down to `C₂`.-/
theorem diagSubgroup_ne_top : diagSubgroup C2 ≠ ⊤ := by
  intro h
  have hmem : ((1 : C2), Multiplicative.ofAdd (1 : ZMod 2)) ∈ diagSubgroup C2 :=
    h ▸ Subgroup.mem_top _
  rw [mem_diagSubgroup] at hmem
  exact absurd hmem (by decide)

end TwoObjectExample
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
