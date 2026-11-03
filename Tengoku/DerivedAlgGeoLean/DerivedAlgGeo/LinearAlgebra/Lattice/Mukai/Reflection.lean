/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.BilinearForm.Reflection
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reflection in a spherical class

For a vector `s` of a Mukai extension with `⟪s, s⟫ = -2`, the map

```
ρ_s(v) = v + ⟪v, s⟫ • s
```

is the reflection in the hyperplane `s^⊥`. The `-2` is what makes the usual
formula `v - 2⟪v,s⟫/⟪s,s⟫ · s` integral: the denominator cancels the `2`, so no
division is needed and the reflection is defined on the lattice rather than on
its rationalisation. This is the only place `IsSpherical` is used below, and it
is used exactly once, in `reflect_reflect`.

**This is not the spherical twist.** On a K3 surface, the twist `T_E` of
Seidel–Thomas acts on the Mukai lattice as `ρ_{v(E)}`, and that statement is the
eventual reason this file exists. But `T_E` is an autoequivalence of
`Dᵇ(Coh X)`, its construction needs an evaluation triangle and a functorial
cone, and none of that is available here or asserted here. `reflect` is a map
of a lattice built from a bilinear form, and every theorem below is a theorem
about **an arbitrary symmetric bilinear `ℤ`-lattice**, true whether or not any
surface exists — the same discipline `Mukai/Basic.lean` states in its own
docstring.

Every argument below is bilinearity, symmetry, or the single hypothesis
`⟪s,s⟫ = -2`, and none of it is about this carrier. It is therefore proved
once, over an arbitrary form, in `BilinearForm/Reflection.lean`, and this file
specialises it at `pairingBilin b`. There is one reflection, not two, and the
record of which hypothesis does what lives with the general statement.

What stays here is the part that is genuinely about the Mukai extension:
`IsSpherical` as the name for `⟪s,s⟫ = -2`, and the preservation of the
distinguished classes `Mukai/Basic.lean` defines.

## Main results

* `reflectHom` — `ρ_s` as a `ℤ`-linear endomorphism, for arbitrary `s`.
* `reflect_reflect` — `ρ_s` is an involution when `s` is spherical.
* `pairing_reflect_reflect` — `ρ_s` preserves the pairing (symmetric `b`).
* `reflectEquiv` — the resulting `ℤ`-linear automorphism.
* `reflectIsometry` — the same map as an isometry of `pairingBilin`.
* `reflect_self` — `ρ_s s = -s`, and `reflect_of_pairing_eq_zero` — `ρ_s`
  fixes `s^⊥` pointwise. Together these say `ρ_s` is a *reflection* rather
  than merely an involutive isometry.
* `IsSpherical.reflect`, `IsIsotropic.reflect`, `expectedDim_reflect` — the
  distinguished classes of `Mukai/Basic.lean` are preserved.
-/

namespace Mukai

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-! ### The map

`Mukai.reflect` is `BilinearForm.reflect` at `pairingBilin b`. The name is kept
because four `SphericalTwist` modules spell it, and because "reflection in a
spherical class" is the application's word for it. -/

/-- Reflection in `s`: `ρ_s(v) = v + ⟪v, s⟫ • s`, specialising
`BilinearForm.reflect` to the Mukai pairing.-/
def reflect (s v : MukaiLattice N) : MukaiLattice N :=
  BilinearForm.reflect (pairingBilin b) s v

/-- Not `@[simp]`: unfolding `reflect` everywhere would put `reflect_zero`,
`reflect_self` and `reflect_neg_left` out of simp-normal form. Rewrite with it
explicitly.
@isnad1 id=eq.0h4v.s7.3303ee8878d2 from=translated src=- shape=f2469ce1 vocab=d2cc9021
-/
theorem reflect_apply (s v : MukaiLattice N) :
    reflect b s v = v + pairing b v s • s :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.f62188ce7c43 from=translated src=- shape=879031a3 vocab=09242cd3
-/
@[simp]
theorem reflect_zero (s : MukaiLattice N) : reflect b s 0 = 0 :=
  BilinearForm.reflect_zero _ s

/--
@isnad1 id=eq.0h5v.s7.b49a4ff0793b from=translated src=- shape=09163ddb vocab=02a7d280
-/
theorem reflect_add (s v w : MukaiLattice N) :
    reflect b s (v + w) = reflect b s v + reflect b s w :=
  BilinearForm.reflect_add _ s v w

/--
@isnad1 id=eq.0h5v.s7.ffca989d6318 from=translated src=- shape=c429a81f vocab=b40ad064
-/
theorem reflect_smul (a : ℤ) (s v : MukaiLattice N) :
    reflect b s (a • v) = a • reflect b s v :=
  BilinearForm.reflect_smul _ a s v

/--
@isnad1 id=eq.0h4v.s7.e96945d6f163 from=translated src=- shape=e6712a30 vocab=49f06e4b
-/
theorem reflect_neg (s v : MukaiLattice N) :
    reflect b s (-v) = -reflect b s v :=
  BilinearForm.reflect_neg _ s v

/-- `ρ_s` as a `ℤ`-linear endomorphism of the Mukai extension.

No hypothesis on `s`: additivity is bilinearity of `pairing`, nothing more.-/
def reflectHom (s : MukaiLattice N) : MukaiLattice N →ₗ[ℤ] MukaiLattice N :=
  BilinearForm.reflectHom (pairingBilin b) s

/--
@isnad1 id=eq.0h4v.s8.d3476bdf6576 from=translated src=- shape=cdaba1aa vocab=48cd924d
-/
@[simp]
theorem reflectHom_apply (s v : MukaiLattice N) :
    reflectHom b s v = reflect b s v :=
  rfl

/-! ### The pairing against `s`

`IsSpherical b s` is by definition `selfPairing b s = -2`, and
`pairingBilin b s s` reduces to `selfPairing b s`, so a sphericity hypothesis is
accepted directly wherever the general theory asks for `B s s = -2`. -/

/-- Reflecting reverses the pairing against `s` itself. This is where
`⟪s, s⟫ = -2` is spent.
@isnad1 id=eq.1h4v.s7.29dfaf433500 from=translated src=- shape=bcc9e393 vocab=f2669d4e
-/
theorem pairing_reflect_right (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = -pairing b v s :=
  BilinearForm.apply_reflect_right (pairingBilin b) s hs v

/-! ### Involutivity -/

/-- **`ρ_s` is an involution** when `s` is spherical.
@isnad1 id=eq.1h4v.s7.eee6c8d099ad from=translated src=- shape=01b5dbdd vocab=9ad5db01
-/
theorem reflect_reflect (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflect b s (reflect b s v) = v :=
  BilinearForm.reflect_reflect (pairingBilin b) s hs v

/--
@isnad1 id=involuti.1h3v.s7.105c5fcd5e07 from=translated src=- shape=cd5ce7d8 vocab=9b7b45ae
-/
theorem reflect_involutive (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Involutive (reflect b s) :=
  reflect_reflect b s hs

/--
@isnad1 id=bijectiv.1h3v.s7.0c2d51582176 from=translated src=- shape=5f6ffc46 vocab=8f074c81
-/
theorem reflect_bijective (s : MukaiLattice N) (hs : IsSpherical b s) :
    Function.Bijective (reflect b s) :=
  (reflect_involutive b s hs).bijective

/-- `ρ_s` as a `ℤ`-linear automorphism, with itself as inverse.-/
def reflectEquiv (s : MukaiLattice N) (hs : IsSpherical b s) :
    MukaiLattice N ≃ₗ[ℤ] MukaiLattice N :=
  BilinearForm.reflectEquiv (pairingBilin b) s hs

/--
@isnad1 id=eq.1h4v.s8.6f3986adccdd from=translated src=- shape=13399eb1 vocab=5624f37c
-/
@[simp]
theorem reflectEquiv_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    reflectEquiv b s hs v = reflect b s v :=
  rfl

/--
@isnad1 id=eq.1h4v.s8.03eb8a587eac from=translated src=- shape=4361aa63 vocab=f2664707
-/
@[simp]
theorem reflectEquiv_symm_apply (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    (reflectEquiv b s hs).symm v = reflect b s v :=
  rfl

/-! ### The reflection property

`reflect_self` and `reflect_of_pairing_eq_zero` are what distinguish a
reflection from an arbitrary involutive isometry: the `-1` eigenspace is
spanned by `s` and the `+1` eigenspace contains `s^⊥`. -/

/-- `ρ_s s = -s`. Needs sphericity but not symmetry.
@isnad1 id=eq.1h3v.s7.17018b59c41d from=translated src=- shape=a0811c73 vocab=78634eff
-/
@[simp]
theorem reflect_self (s : MukaiLattice N) (hs : IsSpherical b s) :
    reflect b s s = -s :=
  BilinearForm.reflect_self (pairingBilin b) s hs

/-- `ρ_s` fixes `s^⊥` pointwise. No hypothesis on `s` at all.
@isnad1 id=eq.1h4v.s7.d2d99d31c911 from=translated src=- shape=b045c2fa vocab=ce31b652
-/
theorem reflect_of_pairing_eq_zero {s v : MukaiLattice N}
    (h : pairing b v s = 0) :
    reflect b s v = v :=
  BilinearForm.reflect_of_apply_eq_zero (pairingBilin b) h

/-- The reflected vector lies in `s^⊥` exactly when the original one does.
@isnad1 id=iff.1h4v.s7.26f9ae3241d6 from=translated src=- shape=935de459 vocab=f167c613
-/
theorem pairing_reflect_eq_zero_iff (s : MukaiLattice N) (hs : IsSpherical b s)
    (v : MukaiLattice N) :
    pairing b (reflect b s v) s = 0 ↔ pairing b v s = 0 :=
  BilinearForm.apply_reflect_eq_zero_iff (pairingBilin b) s hs v

/-! ### Isometry

The first statements in this file to need symmetry of `b`. -/

/-- **`ρ_s` preserves the Mukai pairing.**
@isnad1 id=eq.2h5v.s9.3569bfd6fb33 from=translated src=- shape=bd3fb5aa vocab=35b91598
-/
theorem pairing_reflect_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v w : MukaiLattice N) :
    pairing b (reflect b s v) (reflect b s w) = pairing b v w :=
  BilinearForm.apply_reflect_reflect (pairingBilin b)
    (fun x y => pairing_comm b hb x y) s hs v w

/-- `ρ_s` preserves `⟪v, v⟫`.
@isnad1 id=eq.2h4v.s9.6a4b2af7c9a2 from=translated src=- shape=cb8ec819 vocab=536f1ca3
-/
theorem selfPairing_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    selfPairing b (reflect b s v) = selfPairing b v := by
  simp only [selfPairing_eq_pairing]
  exact pairing_reflect_reflect b hb s hs v v

/-- `ρ_s` as an isometry of the bundled Mukai form.-/
def reflectIsometry (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) :
    pairingBilin b →bᵢ pairingBilin b :=
  BilinearForm.reflectIsometry (pairingBilin b)
    (fun x y => pairing_comm b hb x y) s hs

/--
@isnad1 id=eq.2h4v.s9.e9d482a9d0e4 from=translated src=- shape=363b1cb4 vocab=a803d6d8
-/
@[simp]
theorem reflectIsometry_apply (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    reflectIsometry b hb s hs v = reflect b s v :=
  rfl

/-! ### The distinguished classes are preserved

This is the part that is genuinely about the Mukai extension rather than about
an arbitrary form: `Mukai/Basic.lean` names these conditions and downstream
code rewrites with them rather than unfolding to `selfPairing`. -/

/--
@isnad1 id=isspheri.3h4v.s9.76c4d65b1e10 from=translated src=- shape=bce15b41 vocab=0203713b
-/
theorem IsSpherical.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsSpherical b v) :
    IsSpherical b (Mukai.reflect b s v) := by
  rw [isSpherical_iff, selfPairing_reflect b hb s hs]
  exact hv

/--
@isnad1 id=isisotro.3h4v.s9.b4df83878fcd from=translated src=- shape=f54a2184 vocab=ba9b1fd2
-/
theorem IsIsotropic.reflect (hb : ∀ x y : N, b x y = b y x)
    {s : MukaiLattice N} (hs : IsSpherical b s) {v : MukaiLattice N}
    (hv : IsIsotropic b v) :
    IsIsotropic b (Mukai.reflect b s v) := by
  rw [isIsotropic_iff, selfPairing_reflect b hb s hs]
  exact hv

/--
@isnad1 id=eq.2h4v.s9.1216d0202385 from=translated src=- shape=3a003e04 vocab=3e8b7a4b
-/
theorem expectedDim_reflect (hb : ∀ x y : N, b x y = b y x)
    (s : MukaiLattice N) (hs : IsSpherical b s) (v : MukaiLattice N) :
    expectedDim b (reflect b s v) = expectedDim b v := by
  rw [expectedDim, expectedDim, selfPairing_reflect b hb s hs]

/-! ### Reflection in `-s`

`IsSpherical.neg` says `-s` is spherical whenever `s` is, so both reflections
exist; they are the same map, because the sign enters the formula twice. -/

/--
@isnad1 id=eq.0h4v.s7.50f4579455b2 from=translated src=- shape=b1208151 vocab=49f06e4b
-/
@[simp]
theorem reflect_neg_left (s v : MukaiLattice N) :
    reflect b (-s) v = reflect b s v :=
  BilinearForm.reflect_neg_left (pairingBilin b) s v

end Mukai
