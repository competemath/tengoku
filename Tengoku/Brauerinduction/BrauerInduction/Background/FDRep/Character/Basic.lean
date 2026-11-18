import Tengoku.Seed.RepresentationTheory.Character
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Biproducts
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Res
import Tengoku.Brauerinduction.BrauerInduction.Background.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characters of finite-dimensional representations

This file defines the character of an object of `FDRep k G` and proves its
basic formal properties: invariance under isomorphism and conjugacy, behaviour
under standard constructions, restriction, quotients, and finite biproducts.
-/

universe u v w

namespace FDRep

open CategoryTheory

section Constructions.Monoid

variable {k : Type u} [Field k]
variable {G : Type v} [Monoid G]

/-- Isomorphic representations have the same character.
@isnad1 id=eq.0h5v.s6.c70b7b91300b from=translated src=- shape=e0ef4aa8 vocab=080ee30c
-/
lemma char_eq_of_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character :=
  char_iso i

/-- Transporting a representation along a multiplicative equivalence transports its character.
@isnad1 id=eq.0h5v.s7.547595eacc20 from=translated src=- shape=7f5a6369 vocab=b5cd74f3
-/
lemma char_transport
    {G₁ : Type v} {G₂ : Type w}
    [Monoid G₁] [Monoid G₂]
    (e : G₁ ≃* G₂) (V : FDRep k G₁) :
    (FDRep.transport e V).character =
      V.character ∘ e.symm := by
  ext g
  rfl

/-- Pointwise form of `FDRep.char_transport`.
@isnad1 id=eq.0h6v.s7.6becef80d3f4 from=translated src=- shape=df6fe198 vocab=f6ae492d
-/
@[simp]
lemma char_transport_apply
    {G₁ : Type v} {G₂ : Type w} [Monoid G₁] [Monoid G₂]
    (e : G₁ ≃* G₂) (V : FDRep k G₁) (g : G₂) :
    (FDRep.transport e V).character g =
      V.character (e.symm g) := by
  rfl

/--
@isnad1 id=eq.0h2v.s5.448d438f817d from=translated src=- shape=4c5bd749 vocab=09c0fd1a
-/
@[simp]
lemma char_trivial
    (k : Type u) [Field k]
    (G : Type v) [Monoid G] :
    (FDRep.trivial k G).character = 1 := by
  ext g
  change LinearMap.trace k k (1 : k →ₗ[k] k) = (1 : k)
  simp only [LinearMap.trace_one, Module.finrank_self, Nat.cast_one]

end Constructions.Monoid

section Constructions.Group

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-- The character of the dual representation is `χ(g⁻¹)`.
@isnad1 id=eq.0h4v.s6.d8a4f5a61724 from=translated src=- shape=a30f1a1d vocab=d6a13eef
-/
@[simp]
lemma char_dual_apply
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    (V : FDRep k G) (g : G) :
    V.dual.character g = V.character g⁻¹ := by
  dsimp [dual]
  change LinearMap.trace k _ (Module.Dual.transpose (V.ρ g⁻¹)) = _
  exact LinearMap.trace_transpose' (V.ρ g⁻¹)

/--
The character of the internal Hom representation is
`χ_[V,W](g) = χ_V(g⁻¹) * χ_W(g)`.
@isnad1 id=eq.0h5v.s6.df83a07003e0 from=translated src=- shape=093201e7 vocab=f7d6ae28
-/
@[simp]
lemma char_linHom_apply
    (V W : FDRep k G) (g : G) :
    (linHom V W).character g = V.character g⁻¹ * W.character g :=
      char_linHom V W g

/-- Characters are invariant under conjugation by `x⁻¹` on the left.
@isnad1 id=eq.0h5v.s6.f77390f15b92 from=translated src=- shape=7847d8dc vocab=3afec171
-/
@[simp]
lemma char_inv_conj (V : FDRep k G) (g x : G) :
    V.character (x⁻¹ * g * x) = V.character g := by
  rw [char_mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Characters are constant on conjugacy classes.
@isnad1 id=eq.1h5v.s5.acdc9de0b168 from=translated src=- shape=70fdeb21 vocab=b9c618c3
-/
lemma char_eq_of_isConj
    (V : FDRep k G) {x y : G} (h : IsConj x y) :
    V.character x = V.character y := by
  rw [isConj_iff] at h
  obtain ⟨z, hz⟩ := h
  rw [← hz, char_conj]

/--
The character of a representation lifted to a quotient agrees with the original
character on representatives.
@isnad1 id=eq.1h5v.s12.12945f78ac0a from=translated src=- shape=5b513ebb vocab=2cff15ad
-/
@[simp]
lemma char_lift
    (ρ : FDRep k G)
    (K : Subgroup G) [K.Normal]
    (hK : ∀ x ∈ K, ρ.ρ x = 1)
    (g : G) :
    (FDRep.lift ρ K hK).character (QuotientGroup.mk' K g) =
      ρ.character g := by
  simp only [lift, QuotientGroup.mk'_apply]
  rfl

/-- Restriction does not change character value
@isnad1 id=eq.0h5v.s7.d370fc81ebbf from=translated src=- shape=5070fa80 vocab=193afb99
-/
@[simp]
lemma char_res_apply
    (ρ : FDRep k G) (I : Subgroup G) (y : I) :
    (FDRep.res ρ I).character y = ρ.character (y : G) := by
  rfl

/-- Function-level form of `FDRep.char_res_apply`.
@isnad1 id=eq.0h4v.s7.d89ac2fe0597 from=translated src=- shape=5212a275 vocab=b1b974ab
-/
lemma char_res
    (ρ : FDRep k G) (I : Subgroup G) :
    (FDRep.res ρ I).character = ρ.character ∘ Subtype.val := by
  ext y
  simp

end Constructions.Group

section Biproducts

variable {k : Type u} [Field k]
variable {G : Type v} [Monoid G]

/-- The character of a zero representation is zero.
@isnad1 id=eq.1h3v.s6.c30c4bd5cb1d from=translated src=- shape=25c9631b vocab=ec009de3
-/
lemma char_eq_zero_of_IsZero {V : FDRep k G} (hV : Limits.IsZero V) :
    V.character = 0 := by
  ext g
  haveI : Subsingleton V := FDRep.subsingleton_of_IsZero hV
  have hρ : V.ρ g = 0 := by
    ext x
    apply Subsingleton.elim
  dsimp [FDRep.character]
  simp only [hρ, map_zero]

/-- The character of the concrete product representation is the sum of the characters.
@isnad1 id=eq.0h4v.s6.a4b18d871e4b from=translated src=- shape=a6817985 vocab=c94a7923
-/
@[simp]
lemma char_prod
    (V W : FDRep k G) :
    (V.prod W).character = V.character + W.character := by
  ext g
  dsimp [FDRep.character, FDRep.prod]
  exact LinearMap.trace_prodMap' (V.ρ g) (W.ρ g)

/-- The character of a binary biproduct is the sum of the characters.
@isnad1 id=eq.0h4v.s7.97b55e16596f from=translated src=- shape=18a3aa7c vocab=d847a851
-/
@[simp]
lemma char_biprod (V W : FDRep k G) :
    (V ⊞ W).character = V.character + W.character :=  by
  have i : (V ⊞ W) ≅ (FDRep.prod V W) := biprodIsoProd V W
  calc
    (V ⊞ W).character
        = (FDRep.prod V W).character := by exact char_eq_of_iso i
      _ = V.character + W.character := char_prod (k:=k) V W
/--
The character of a biproduct indexed by `Option ι` splits into the distinguished
summand and the remaining finite biproduct.
@isnad1 id=eq.0h5v.s8.eda1dc4d819d from=translated src=- shape=c5bbd720 vocab=60f5cae5
-/
lemma char_biproduct_option {ι : Type*} [Finite ι]
    (S : FDRep k G) (K : ι → FDRep k G) :
    (Limits.biproduct (Option.rec S K)).character
      = S.character + (Limits.biproduct K).character := by
  let e := (biproductOptionIso (ι := ι) S K)
  calc
    (Limits.biproduct (Option.rec S K)).character
        = (S ⊞ Limits.biproduct K).character := by
            simpa using (char_eq_of_iso e.symm)
    _   = S.character + (Limits.biproduct K).character := by
            simp only [char_biprod]

/-- The character of a finite biproduct is the sum of the characters of its components.
@isnad1 id=eq.0h4v.s7.3fa01e3772f8 from=translated src=- shape=f6f38945 vocab=a14cb699
-/
lemma char_biproduct {ι : Type} [Fintype ι] (f : ι → FDRep k G) :
    (Limits.biproduct f).character = ∑ i, (f i).character := by
  haveI : Limits.HasFiniteBiproducts (FDRep k G) := inferInstance
  revert f
  refine Fintype.induction_empty_option
    (P := fun (α : Type) _ => ∀ g : α → FDRep k G,
      (Limits.biproduct g).character = ∑ i, (g i).character)
    ?_ ?_ ?_ ι
  · intro α β _ e hα g
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let i : Limits.biproduct (g ∘ e) ≅ Limits.biproduct g :=
      Limits.biproduct.reindex e g
    rw [← char_eq_of_iso i]
    rw [hα (g ∘ e)]
    rw [Fintype.sum_equiv e _ (fun y => (g y).character)]
    simp only [Function.comp_apply, implies_true]
  · intro g
    rw [Fintype.sum_empty]
    exact char_eq_zero_of_IsZero (IsZero_biproduct_empty g)
  · intro α _ hα g
    have h_split :
        (Limits.biproduct g).character =
          (Limits.biproduct (Option.rec (g Option.none) (g ∘ Option.some))).character := by
      congr
      ext x
      cases x <;> rfl
    rw [h_split]
    rw [char_biproduct_option]
    rw [Fintype.sum_option]
    rw [hα (g ∘ Option.some)]
    rfl

end Biproducts

end FDRep
