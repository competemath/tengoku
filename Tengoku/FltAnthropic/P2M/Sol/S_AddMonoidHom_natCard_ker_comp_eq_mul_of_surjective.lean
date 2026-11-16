import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective

set_option autoImplicit false

namespace P2mKerMul

variable {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]

def kerMap (f : A →+ B) (g : B →+ C) : (g.comp f).ker →+ g.ker :=
  (f.domRestrict (g.comp f).ker).codRestrict g.ker fun x => by
    rw [AddMonoidHom.domRestrict_apply, AddMonoidHom.mem_ker]
    have hx := x.2
    rwa [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply] at hx

/--
@isnad1 id=eq.0h6v.s10.731ac1db8e9e from=translated src=- shape=2cb3cf1a vocab=e5c10899
-/
@[scoped simp] theorem kerMap_apply (f : A →+ B) (g : B →+ C) (x : (g.comp f).ker) :
    (kerMap f g x : B) = f x := rfl

/--
@isnad1 id=surjecti.1h5v.s10.7e2c8aea0b02 from=translated src=- shape=7c1c16ed vocab=f47af581
-/
theorem kerMap_surjective (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Function.Surjective (kerMap f g) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ (g.comp f).ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
    rwa [AddMonoidHom.mem_ker] at hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

/--
@isnad1 id=le.0h5v.s7.b1c7fb13c599 from=translated src=- shape=2d1fa2bc vocab=1a39765f
-/
theorem ker_le (f : A →+ B) (g : B →+ C) : f.ker ≤ (g.comp f).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, hx, map_zero]

/--
@isnad1 id=eq.0h5v.s8.a21a4b4fbbf9 from=translated src=- shape=072fd2fa vocab=5fe47a11
-/
theorem ker_kerMap (f : A →+ B) (g : B →+ C) :
    (kerMap f g).ker = f.ker.addSubgroupOf (g.comp f).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker,
    ← kerMap_apply]
  exact ⟨fun h => by rw [h, AddSubgroup.coe_zero], fun h => Subtype.ext h⟩

/--
@isnad1 id=eq.1h5v.s7.abf52111b4cc from=translated src=- shape=e71ea44b vocab=ae927e96
-/
theorem natCard_ker_comp (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker := by
  calc Nat.card (g.comp f).ker
      = Nat.card ((g.comp f).ker ⧸ (kerMap f g).ker) * Nat.card (kerMap f g).ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    _ = Nat.card g.ker * Nat.card f.ker := by
        rw [Nat.card_congr
            (QuotientAddGroup.quotientKerEquivOfSurjective _ (kerMap_surjective f g hf)).toEquiv,
          ker_kerMap, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (ker_le f g)).toEquiv]

end P2mKerMul
open scoped _root_.P2MW.S_AddMonoidHom_natCard_ker_comp_eq_mul_of_surjective.P2mKerMul

/--
@isnad1 id=eq.1h5v.s7.abf52111b4cc from=translated src=- shape=e71ea44b vocab=ae927e96
-/
theorem solution {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f) :
    Nat.card (g.comp f).ker = Nat.card g.ker * Nat.card f.ker :=
  P2mKerMul.natCard_ker_comp f g hf
