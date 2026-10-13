/-
Copyright (c) 2025 Madison Crim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madison Crim
-/
module

public import Tengoku

/-!
# Is Direct Limit

Material destined for Mathlib.
-/

@[expose] public section

variable {ι : Type*} [Preorder ι] {M : ι → Type*} {P : Type*}
  (f : (i j : ι) → (h : i ≤ j) → M i → M j) (g : ∀ i, M i → P)

/--
`IsDirectLimit f g` states that `P` is the direct limit of the system `(M i, f i j hij)`.
It requires:
* `surj`: says every element of `P` comes from some `M i` via the canonical map `g i`.
* `inj`: says that if two elements of (possibly different) modules `M i` and `M j` map
  to the same element of `P`, then they become equal after being mapped into a common
  later module `M k`.
* `compatibility`: ensures that the maps `g i` and `f i j hij` are compatible with one another.
-/
class IsDirectLimit [DirectedSystem M f] : Prop where
  surj : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m
  inj :  ∀ i j, ∀ mi : M i, ∀ mj : M j, g i mi = g j mj → ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
      f i k hik mi = f j k hjk mj
  compatibility : ∀ i j hij x, g j (f i j hij x) = g i x

variable [DirectedSystem M f] [IsDirectLimit f g]

namespace IsDirectLimit

/--
@isnad1 id=eq.1h8v.s6.d8f866374ccd from=translated src=- shape=27557d07 vocab=b940f25f
-/
theorem compatibility' {i j hij} (x : M i) : g j (f i j hij x) = g i x :=
  IsDirectLimit.compatibility i j hij x

/--
@isnad1 id=ex.1h9v.s7.10ccfef5e95e from=translated src=- shape=b291c915 vocab=b940f25f
-/
theorem is_injective {i j} {mi : M i} {mj : M j} (h : g i mi = g j mj) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), f i k hik mi = f j k hjk mj :=
  IsDirectLimit.inj i j mi mj h

include f in
/--
@isnad1 id=ex.0h6v.s6.547eca748e84 from=translated src=- shape=9ba0208a vocab=b940f25f
-/
theorem is_surjective : ∀ m : P, ∃ i, ∃ mi : M i, g i mi = m :=
  IsDirectLimit.surj f

/--
Given an element `p : P` in the direct limit, `preimageIndex f g p` returns an index in `ι` such
that `p` is in the image of the map `g (preimageIndex f g p) : M (preimageIndex f g p) →ₗ[R] P`.
-/
noncomputable def preimageIndex (p : P) : ι := (is_surjective f g p).choose

/--
Given an element `p : P` in the direct limit, `preimage f g p` returns an element of
`M (preimageIndex f g p)` that maps to `p` under `g (preimageIndex f g p)`.
-/
noncomputable def preimage (p : P) : M (preimageIndex f g p) :=
  (is_surjective f g p).choose_spec.choose

/--
@isnad1 id=eq.0h6v.s6.8e0284a2a515 from=translated src=- shape=81bcbf98 vocab=80909a0c
-/
theorem image_preimage (p : P) :
    g (preimageIndex f g p) (preimage f g p) = p :=
  (is_surjective f g p).choose_spec.choose_spec

variable {P₁ P₂ : Type*} (g₁ : ∀ i, M i → P₁) (g₂ : ∀ i, M i → P₂)

/--
Construct a map `P₁ → P₂` from a direct limit by sending each element to its preimage
in some component `M i` and applying `g₂ i`. Used to define morphisms out of direct limits.
-/
noncomputable def lift [IsDirectLimit f g₁] (p : P₁) : P₂ :=
  g₂ (preimageIndex f g₁ p) (preimage f g₁ p)

/--
@isnad1 id=eq.1h9v.s6.8616d486fc93 from=translated src=- shape=64e6016d vocab=2158b259
-/
@[simp]
theorem lift_of [IsDirectLimit f g₁] (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (lift f g₁ g₂) (g₁ i x) = g₂ i x := by
  dsimp [lift]
  have ⟨k, hpk, hik, h_eq⟩ := is_injective f g₁ (image_preimage f g₁ (g₁ i x))
  rw [← Hg i k hik x, ← Hg (preimageIndex f g₁ (g₁ i x)) k hpk, h_eq]

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def Equiv [h₁ : IsDirectLimit f g₁] [h₂ : IsDirectLimit f g₂] :
    P₁ ≃ P₂ where
  toFun := lift f g₁ g₂
  invFun := lift f g₂ g₁
  left_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₁.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]
  right_inv x := by
    obtain ⟨i, mi, hmi⟩ := h₂.surj x
    rw [← hmi]
    simp only [compatibility', implies_true, lift_of]

/--
@isnad1 id=eq.0h9v.s6.9b0872f74e24 from=translated src=- shape=1ca80b19 vocab=bebdecd4
-/
@[simp]
lemma Equiv_apply (i : ι) (x : M i) [IsDirectLimit f g₁] [IsDirectLimit f g₂] :
  Equiv f g₁ g₂ (g₁ i x) = g₂ i x := by
  simp [Equiv, Equiv.coe_fn_mk, compatibility', implies_true, lift_of]

/--
@isnad1 id=eq.0h9v.s6.38aee2f6b34e from=translated src=- shape=98b62234 vocab=6189a7dc
-/
@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) [IsDirectLimit f g₁]
  [IsDirectLimit f g₂] : (Equiv f g₁ g₂).symm (g₂ i x) = g₁ i x := by
  simp [Equiv, compatibility', implies_true, lift_of]

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid P] [Module R P] (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  [DirectedSystem M (f · · ·)] [IsDirectLimit (fun ⦃i j⦄ h => f i j h) g] [IsDirected ι (· ≤ ·)]

variable [AddCommMonoid P₁] [Module R P₁] [AddCommMonoid P₂] [Module R P₂]
  (g₁ : ∀ i, M i →ₗ[R] P₁) (g₂ : ∀ i, M i →ₗ[R] P₂) [h₁ : IsDirectLimit (f · · ·) (g₁ · ·)]

omit [IsDirected ι (· ≤ ·)] in
/--
@isnad1 id=eq.1h9v.s9.c67acb1cc904 from=translated src=- shape=529acd3c vocab=32b5068e
-/
theorem compatibility_module {i j hij} (x : M i) : g₁ j (f i j hij x) = g₁ i x :=
  compatibility' (f · · ·) (g₁ · ·) x

/--
The universal property of the direct limit: define a linear map from the direct limit
by giving a compatible family of linear maps from the components.
Each element of the limit is sent according to its representative in some component.
-/
noncomputable def lift
    (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) : P₁ →ₗ[R] P₂ where
  toFun := IsDirectLimit.lift (f · · ·) (g₁ · ·) (g₂ · · )
  map_add' x y := by
    obtain ⟨k, hxk, hyk⟩ :=
      IsDirected.directed (r := (· ≤ ·)) (preimageIndex (f · · ·) (g₁ · ·) x)
      (preimageIndex (f · · ·) (g₁ · ·) y)
    obtain ⟨k', hxyk', hkk'⟩ := IsDirected.directed (r := (· ≤ ·))
      (preimageIndex (f · · ·) (g₁ · ·) (x+y)) k
    have sum_eq : g₁ k' (f (preimageIndex (f · · ·) (g₁ · ·) x) k' (le_trans hxk hkk')
      (preimage (f · · ·) (g₁ · ·) x) + f (preimageIndex (f · · ·) (g₁ · ·) y) k'
      (le_trans hyk hkk') (preimage (f · · ·) (g₁ · ·) y)) =
        g₁ (preimageIndex (f · · ·) (g₁ · ·) (x+y)) (preimage (f · · ·) (g₁ · ·) (x+y)) := by
      simp only [LinearMap.map_add, image_preimage]
      repeat rw [compatibility' (f · · ·) (g₁ · ·),
        image_preimage (f := (f · · ·)) (g := (g₁ · ·))]
    obtain ⟨k'', hk'k'', hxyk'', h'''⟩ := is_injective (f · · ·) (g₁ · ·) sum_eq
    simpa [Hg] using! congr_arg (g₂ k'') h'''.symm
  map_smul' r x := by
    have smul_eq : g₁ (preimageIndex (f · · ·) (g₁ · ·) (r • x)) (preimage (f · · ·) (g₁ · ·)
      (r • x)) = g₁ (preimageIndex (f · · ·) (g₁ · ·) x) (r • preimage (f · · ·) (g₁ · ·) x) := by
      simp only [image_preimage, map_smul]
    obtain ⟨k, hixk, hirxk, h_smul⟩ := is_injective (f · · ·) (g₁ · ·) smul_eq
    simpa [Hg] using! congr_arg (g₂ k) h_smul

/--
@isnad1 id=eq.1h10v.s9.eeecb72c834a from=translated src=- shape=f5918591 vocab=ac5c046f
-/
@[simp]
theorem lift_of (Hg : ∀ i j hij x, g₂ j (f i j hij x) = g₂ i x) {i} (x) :
    (Module.lift f g₁ g₂ Hg) (g₁ i x) = g₂ i x := by
  dsimp [lift, IsDirectLimit.lift_of]
  exact IsDirectLimit.lift_of (f · · ·) (g₁ · ·) (g₂ · ·) Hg x

/--
@isnad1 id=eq.0h9v.s9.b35427769091 from=translated src=- shape=57031771 vocab=81df449b
-/
theorem lift_unique (F : P₁ →ₗ[R] P₂) (x) : F x = (Module.lift f g₁ (fun i ↦ F.comp <| g₁ i)
    (fun i j hij x ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact LinearMap.congr_arg (IsDirectLimit.compatibility (f := (f · · ·))
      (g := (g₁ · ·)) i j hij x))) x := by
  simp only [lift, IsDirectLimit.lift,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, image_preimage]

variable [h₂ : IsDirectLimit (f · · ·) (g₂ · ·)]

/-- Any two direct limits of the same directed system are isomorphic. -/
noncomputable def linearEquiv : P₁ ≃ₗ[R] P₂ :=
  { IsDirectLimit.Equiv (f · · ·) (g₁ · ·) (g₂ · ·) with
    map_add' := (lift f g₁ g₂ h₂.compatibility).map_add'
    map_smul' := (lift f g₁ g₂ h₂.compatibility).map_smul'}

/--
@isnad1 id=eq.0h10v.s9.dd197404066a from=translated src=- shape=d17ac29a vocab=a7bace73
-/
@[simp]
lemma linearEquiv_apply (i : ι) (x : M i) :
  linearEquiv f g₁ g₂ (g₁ i x) = g₂ i x :=
  IsDirectLimit.Equiv_apply (f · · ·) (g₁ · ·) (g₂ · ·) i x

/--
@isnad1 id=eq.0h10v.s9.b48d7582db8f from=translated src=- shape=af27c17c vocab=e6db6886
-/
@[simp]
lemma linearEquiv_symm_apply (i : ι) (x : M i) :
  (linearEquiv f g₁ g₂).symm (g₂ i x) = g₁ i x :=
  IsDirectLimit.linearEquiv_symm_apply (f · · ·) (g₁ · ·) (g₂ · ·) i x

end Module

end IsDirectLimit
