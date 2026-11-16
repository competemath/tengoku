import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy

set_option autoImplicit false

namespace P2mLwFree

open Module Submodule Function

variable {M : Type*} [AddCommGroup M]

/--
@isnad1 id=eq.0h3v.s7.37e9f72338a0 from=translated src=- shape=9f234cc9 vocab=d00c39ce
-/
theorem nsmul_coe_torsionBy (k : ℕ) (x : torsionBy ℤ M ((k : ℕ) : ℤ)) : k • (x : M) = 0 := by
  have := (mem_torsionBy_iff _ _).1 x.2
  rwa [natCast_zsmul] at this

@[reducible] def modInst (k : ℕ) : Module (ZMod k) (torsionBy ℤ M ((k : ℕ) : ℤ)) :=
  AddCommGroup.zmodModule fun x => Subtype.ext (by
    rw [Submodule.coe_smul_of_tower, Submodule.coe_zero]
    exact nsmul_coe_torsionBy k x)

attribute [local instance] modInst

/--
@isnad1 id=iff.0h3v.s8.cb5b874b52ee from=translated src=- shape=d5bc083d vocab=3cbc392f
-/
theorem mem_range_subtype_iff (k : ℕ) (x : M) :
    x ∈ ((torsionBy ℤ M ((k : ℕ) : ℤ)).subtype.toAddMonoidHom).range ↔ ((k : ℕ) : ℤ) • x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_torsionBy_iff _ _).1 v.2
  · intro hx
    exact ⟨⟨x, (mem_torsionBy_iff _ _).2 hx⟩, rfl⟩

/--
@isnad1 id=nonempty.0h3v.s5.4c37507b9cfd from=translated src=- shape=e98abf64 vocab=90569d65
-/
theorem nonempty_basis_of_subsingleton {R : Type*} [Semiring R] [Subsingleton R] {W : Type*}
    [AddCommMonoid W] [Module R W] [Subsingleton W] (r : ℕ) : Nonempty (Basis (Fin r) R W) :=
  ⟨Basis.ofEquivFun (LinearEquiv.ofSubsingleton W (Fin r → R))⟩

/--
@isnad1 id=nonempty.0h3v.s7.b14d7ba79f63 from=translated src=- shape=275a2939 vocab=656e323e
-/
theorem levelZero (ℓ r : ℕ) :
    Nonempty (Basis (Fin r) (ZMod (ℓ ^ 0)) (torsionBy ℤ M ((ℓ ^ 0 : ℕ) : ℤ))) := by
  haveI : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero ℓ)
  haveI : Subsingleton (torsionBy ℤ M ((ℓ ^ 0 : ℕ) : ℤ)) := ⟨fun x y => Subtype.ext (by
    have hx : (1 : ℕ) • (x : M) = 0 := by simpa only [pow_zero] using nsmul_coe_torsionBy (ℓ ^ 0) x
    have hy : (1 : ℕ) • (y : M) = 0 := by simpa only [pow_zero] using nsmul_coe_torsionBy (ℓ ^ 0) y
    rw [one_smul] at hx hy
    rw [hx, hy])⟩
  exact nonempty_basis_of_subsingleton r

/--
@isnad1 id=nonempty.2h5v.s8.4439e7a41865 from=translated src=- shape=5399c313 vocab=ad1d997d
-/
theorem nonempty_basis_torsionBy (ℓ : ℕ) [Fact ℓ.Prime] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r) :
    ∀ j ≤ m, Nonempty (Basis (Fin r) (ZMod (ℓ ^ j)) (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ))) := by
  intro j
  induction j with
  | zero => exact fun _ => levelZero ℓ r
  | succ j ih =>
    intro hj
    obtain ⟨c⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨c', -⟩ := AddCommGroup.exists_basis_smul_eq_of_card_torsionBy ℓ r j
      (fun i hi => hcard i (hi.trans hj))
      (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)).subtype.toAddMonoidHom Subtype.val_injective
      (mem_range_subtype_iff (ℓ ^ j))
      (torsionBy ℤ M ((ℓ ^ (j + 1) : ℕ) : ℤ)).subtype.toAddMonoidHom Subtype.val_injective
      (mem_range_subtype_iff (ℓ ^ (j + 1))) c
    exact ⟨c'⟩

/--
@isnad1 id=nonempty.2h6v.s8.b78d2b8720c7 from=translated src=- shape=dbb3fd56 vocab=4f8d3aa7
-/
theorem nonempty_basis_of_carrier (n : ℕ) {ι' : Type*} (b : Basis ι' (ZMod n) (torsionBy ℤ M ((n : ℕ) : ℤ)))
    {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0) :
    Nonempty (Basis ι' (ZMod n) V) := by
  let f : V →+ torsionBy ℤ M ((n : ℕ) : ℤ) :=
    ι.codRestrict (torsionBy ℤ M ((n : ℕ) : ℤ)) fun v =>
      (mem_torsionBy_iff _ _).2 ((hιr _).1 ⟨v, rfl⟩)
  have hf : Bijective f := by
    refine ⟨fun v w h => hι (Subtype.ext_iff.1 h), fun x => ?_⟩
    obtain ⟨v, hv⟩ := (hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
    exact ⟨v, Subtype.ext hv⟩
  let e : V ≃ₗ[ZMod n] torsionBy ℤ M ((n : ℕ) : ℤ) :=
    LinearEquiv.ofBijective (f.toZModLinearMap n) hf
  exact ⟨b.map e.symm⟩

end P2mLwFree

/--
@isnad1 id=nonempty.3h6v.s8.f3f9eaa19481 from=translated src=- shape=a2b2afb1 vocab=dc2f7e85
-/
theorem solution (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) := by
  letI := P2mLwFree.modInst (M := M) (ℓ ^ m)
  obtain ⟨b⟩ := P2mLwFree.nonempty_basis_torsionBy ℓ r m hcard m le_rfl
  exact P2mLwFree.nonempty_basis_of_carrier (ℓ ^ m) b ι hι hιr
