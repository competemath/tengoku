/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Colimit.DirectLimit
public import Tengoku.Seed.Data.Finset.Order
public import Tengoku.Seed.RingTheory.FreeCommRing
public import Tengoku.Seed.RingTheory.Ideal.Maps
public import Tengoku.Seed.RingTheory.Ideal.Quotient.Defs
public import Tengoku.Seed.Tactic.SuppressCompilation

/-!
# Direct limit of rings, and fields

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable rings or fields.

It is constructed as a quotient of the free commutative ring instead of a quotient of
the disjoint union so as to make the operations (addition etc.) "computable".

## Main definition

* `Ring.DirectLimit G f`

-/

@[expose] public section

assert_not_exists Cardinal

suppress_compilation
noncomputable section -- needed for `deriving`

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

open Submodule

namespace Ring

variable [∀ i, CommRing (G i)]

section

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

/-- The direct limit of a directed system is the ring obtained by gluing the components along the
maps. -/
def DirectLimit : Type _ :=
  FreeCommRing (Σ i, G i) ⧸
    Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
            (∃ i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              ∃ i x y, of (⟨i, x * y⟩ : Σ i, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
deriving Zero, One, AddCommMonoid, Ring, CommRing, Inhabited

namespace DirectLimit

/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i →+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x ↦ Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σ i, G i))
      map_one' := Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inl ⟨i, rfl⟩
      map_mul' := fun x y ↦
        Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inr ⟨i, x, y, rfl⟩ }
    fun x y ↦ Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inl ⟨i, x, y, rfl⟩

variable {G f}

/--
@isnad1 id=eq.0h5v.s13.ae61a7c82e7f from=seed src=0 shape=6a59c233 vocab=8251e707
-/
theorem quotientMk_of (i x) : Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x :=
  rfl

/--
@isnad1 id=eq.1h6v.s8.db921ee02438 from=seed src=0 shape=67c7ee79 vocab=912e275e
-/
@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Ideal.Quotient.eq.2 <| subset_span <| Or.inl ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system.
@isnad1 id=ex.0h4v.s7.6a10fc97b345 from=seed src=0 shape=097690b5 vocab=cd034d66
-/
theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : DirectLimit G f) :
    ∃ i x, of G f i x = z := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine z.induction_on ⟨Classical.arbitrary ι, -1, by simp; rfl⟩ (fun ⟨i, x⟩ ↦ ⟨i, x, rfl⟩) ?_ ?_
    <;> rintro x' y' ⟨i, x, hx⟩ ⟨j, y, hy⟩ <;> have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  · exact ⟨k, f i k hik x + f j k hjk y, by rw [map_add, of_f, of_f, hx, hy]; rfl⟩
  · exact ⟨k, f i k hik x * f j k hjk y, by rw [map_mul, of_f, of_f, hx, hy]; rfl⟩

section

open Polynomial

variable {f' : ∀ i j, i ≤ j → G i →+* G j}

/--
@isnad1 id=ex.0h4v.s10.64d8454010a9 from=seed src=0 shape=709eac1f vocab=bc941dc2
-/
nonrec theorem Polynomial.exists_of [Nonempty ι] [IsDirectedOrder ι]
    (q : Polynomial (DirectLimit G fun i j h ↦ f' i j h)) :
    ∃ i p, Polynomial.map (of G (fun i j h ↦ f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z ↦
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ ↦
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2), by
        rw [Polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂]
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, of_f]⟩)
    fun n z _ ↦
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩

end

/--
@isnad1 id=var.0h6v.s7.961a5d83eb50 from=seed src=0 shape=8f1218e8 vocab=cd034d66
-/
@[elab_as_elim]
theorem induction_on [Nonempty ι] [IsDirectedOrder ι] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

variable (P : Type*) [CommRing P]

open FreeCommRing

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σ i, G i ↦ g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σ i : ι, G i ↦ g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [map_sub, lift_of, Hg, map_one, map_add, map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

/--
@isnad1 id=eq.1h7v.s9.96697032d8d2 from=seed src=0 shape=be38265f vocab=bdceab82
-/
@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _

/--
@isnad1 id=eq.1h6v.s8.930a3c2bf093 from=seed src=0 shape=fba01609 vocab=3b27dc15
-/
@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
  Ideal.Quotient.ringHom_ext <| FreeCommRing.hom_ext fun ⟨i, x⟩ => congr($(h i) x)

/--
@isnad1 id=eq.0h5v.s7.f87e0ab37678 from=seed src=0 shape=a4311fc0 vocab=a13e6fbd
-/
@[simp]
theorem lift_comp_of (F : DirectLimit G f →+* P) :
    lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

/--
@isnad1 id=eq.0h3v.s7.f39d1b465263 from=seed src=0 shape=7c92f2da vocab=9ffa4ca8
-/
@[simp]
theorem lift_of' : lift G f _ (of G f) (fun i j hij x ↦ by simp) = .id _ := by
  ext; simp

/--
@isnad1 id=injectiv.2h5v.s8.4e2edbe17d19 from=seed src=0 shape=a1966bc8 vocab=faddff17
-/
lemma lift_injective [Nonempty ι] [IsDirectedOrder ι]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) := by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intro z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, map_zero]

section OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G fun i j h ↦ f' i j h] [IsDirectedOrder ι]
variable (G f)

open _root_.DirectLimit in
/-- The direct limit constructed as a quotient of the free commutative ring is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
def ringEquiv [Nonempty ι] : DirectLimit G (f' · · ·) ≃+* _root_.DirectLimit G f' :=
  .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext; simp)
    (by ext; simp)

/--
@isnad1 id=eq.0h5v.s12.c72c17e671ae from=seed src=0 shape=6e1f50ab vocab=6cd58a61
-/
@[simp]
theorem ringEquiv_of [Nonempty ι] {i g} : ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧ := by
  simp [ringEquiv]

/--
@isnad1 id=eq.0h4v.s13.f7b132f6dabd from=seed src=0 shape=03c75c41 vocab=d2f2eb8f
-/
@[simp]
theorem ringEquiv_symm_mk [Nonempty ι] {g} : (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2 := rfl

variable {G f'}
/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system.
@isnad1 id=ex.1h5v.s11.4bcef49d1af7 from=seed src=0 shape=70bcf9fd vocab=f7259cb7
-/
theorem of.zero_exact {i x} (hix : of G (f' · · ·) i x = 0) :
    ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0 := by
  have := Nonempty.intro i
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix

end OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective.
@isnad1 id=injectiv.1h4v.s10.4f37d6bfb5e2 from=seed src=0 shape=85525498 vocab=3dc243be
-/
theorem of_injective [IsDirectedOrder ι] [DirectedSystem G fun i j h ↦ f' i j h]
    (hf : ∀ i j hij, Function.Injective (f' i j hij)) (i) :
    Function.Injective (of G (fun i j h ↦ f' i j h) i) :=
  have := Nonempty.intro i
  ((ringEquiv _ _).comp_injective _).mp
    fun _ _ eq ↦ DirectLimit.mk_injective f' hf _ (by simpa only [← ringEquiv_of])

section functorial

variable {f : ∀ i j, i ≤ j → G i →+* G j}
variable {G' : ι → Type*} [∀ i, CommRing (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+* G' j}
variable {G'' : ι → Type*} [∀ i, CommRing (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →+* G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of ring homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a ring
homomorphism `lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

/--
@isnad1 id=eq.1h8v.s12.8c23ec1c5734 from=seed src=0 shape=98c64396 vocab=e8adabb6
-/
@[simp] lemma map_apply_of (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G _ _ x) = of G' (fun _ _ h ↦ f' _ _ h) i (g i x) :=
  lift_of _ _ _ _ _

/--
@isnad1 id=eq.0h3v.s10.90b146fc486d from=seed src=0 shape=2c181158 vocab=cd6dd5f4
-/
@[simp] lemma map_id :
    map (fun _ ↦ RingHom.id _) (fun _ _ _ ↦ rfl) = .id (DirectLimit G fun _ _ h ↦ f _ _ h) := by
  ext; simp

/--
@isnad1 id=eq.2h9v.s11.9954ebc5db3a from=seed src=0 shape=0c030271 vocab=b74ce083
-/
lemma map_comp (g₁ : (i : ι) → G i →+* G' i) (g₂ : (i : ι) → G' i →+* G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [RingHom.comp_assoc, hg₁ i, ← RingHom.comp_assoc, hg₂ i, RingHom.comp_assoc] :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) := by
  ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) ≃+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  RingEquiv.ofRingHom
    (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

/--
@isnad1 id=eq.1h8v.s13.f7a0604f96da from=seed src=0 shape=fc408bdc vocab=e15612a7
-/
lemma congr_apply_of (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G _ i g) = of G' (fun _ _ h ↦ f' _ _ h) i (e i g) :=
  map_apply_of _ he _

/--
@isnad1 id=eq.1h8v.s13.bd576418244e from=seed src=0 shape=2f20417a vocab=36d18e50
-/
lemma congr_symm_apply_of (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' _ i g) = of G (fun _ _ h ↦ f _ _ h) i ((e i).symm g) := by
  simp only [congr, RingEquiv.ofRingHom_symm_apply, map_apply_of, RingHom.coe_coe]

end functorial

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, Field (G i)]
variable (f : ∀ i j, i ≤ j → G i → G j)
variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

/--
@isnad1 id=nontrivi.0h3v.s8.ab6c1b3144ee from=seed src=0 shape=396ee5d2 vocab=11f116e7
-/
instance nontrivial [DirectedSystem G (f' · · ·)] :
    Nontrivial (Ring.DirectLimit G (f' · · ·)) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι ↦ by
        change (0 : Ring.DirectLimit G (f' · · ·)) ≠ 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩

/--
@isnad1 id=ex.1h4v.s8.756f85c98e4d from=seed src=0 shape=1063acd0 vocab=b77388fc
-/
theorem exists_inv {p : Ring.DirectLimit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
  Ring.DirectLimit.induction_on p fun i x H ↦
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul,
        mul_inv_cancel₀ fun h : x = 0 ↦ H <| by rw [h, (Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

section


open scoped Classical in
/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
noncomputable def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)

/--
@isnad1 id=eq.1h4v.s8.fa68878dfe89 from=seed src=0 shape=31fdeafd vocab=a93c5cf8
-/
protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * inv G f p = 1 := by
  rw [inv, dite_eq_right hp, Classical.choose_spec (DirectLimit.exists_inv G f hp)]

/--
@isnad1 id=eq.1h4v.s8.6d07f3587f27 from=seed src=0 shape=7d04fa10 vocab=a93c5cf8
-/
protected theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : inv G f p * p = 1 := by
  rw [_root_.mul_comm, DirectLimit.mul_inv_cancel G f hp]

/-- Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances]. -/
protected noncomputable abbrev field [DirectedSystem G (f' · · ·)] :
    Field (Ring.DirectLimit G (f' · · ·)) where
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  inv := inv G (f' · · ·)
  mul_inv_cancel := fun _ ↦ DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dite_eq_left rfl
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

end

end DirectLimit

end Field
