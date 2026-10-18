/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.NumberTheory.Cyclotomic.CyclotomicCharacter
import Tengoku.Seed.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cyclotomic character of `Gal(F/S)`

Let `F / S` be a field extension and `G = F ≃ₐ[S] F` its group of `S`-algebra automorphisms. Every
`σ ∈ G` permutes the `n`-th roots of unity of `F`, and since `μ_n(F)` is cyclic that permutation is
`ζ ↦ ζ ^ j` for an integer `j = j(σ)` well defined modulo `n`. The resulting homomorphisms

* `galoisModularCyclotomicChar S F hn : G →* (ZMod n)ˣ`  (`χ_n`, one `n` at a time), and
* `galoisCyclotomicChar S F p : G →* ℤ_[p]ˣ`  (`χ_p`, the `p`-adic character assembling the levels
  `n = p ^ k`)

are the **cyclotomic characters** of `F / S`. Both are Mathlib's `modularCyclotomicCharacter` and
`cyclotomicCharacter`, which are stated for `RingAut F`, restricted along the tautological action of
`G` on `F`; this file is the restriction, its specification, and the two facts about it that the
rest of the development needs.

## Why this file exists

`EllipticCurves.TateModule.Determinant` defines the determinant character of the `2`-adic Galois
representation,

`galoisDetTwo : (F ≃ₐ[S] F) →* ℤ_[2]ˣ`,

and its docstring — together with those of `EllipticCurves.TateModule.Image`,
`EllipticCurves.TateModule.ImageProfinite`, `EllipticCurves.TateModule.MatrixContinuity`,
`EllipticCurves.TateModule.MatrixRep` and `EllipticCurves.TateModule.Profinite` — names the
identification of that character with the cyclotomic character as the goal the Weil-pairing work is
for. Until now that identification could not even be *written down*, since no cyclotomic character
existed in this development.

With `galoisCyclotomicChar S F 2 : (F ≃ₐ[S] F) →* ℤ_[2]ˣ` the two characters have the same type, so

```
galoisDetTwo = galoisCyclotomicChar S F 2
```

is a well-formed proposition. It is **not proved here**, and nothing in this file brings it closer
to being proved: it needs the Weil pairing on `E[2 ^ k]` — the rung-5 divisor identity
`div g_S = [n]∗(S)` (`#418`, gated on `#421`/`#422`), the alternating property (`#465`
deliverable 2), and non-degeneracy — which is **not** Ward-gated; see
`EllipticCurves.FunctionField.WeilPairing`'s scope section (`#769`). Bilinearity in the divisor
slot is no longer on that list: it is merged, with antisymmetry, as
`EllipticCurves.FunctionField.WeilPairingAntisymmetric` (`#723`) on `[Field F]` and
`[W.IsElliptic]` alone, and all it wants beyond those is the production of
`g_{S ⊕ S'} = g_S · g_{S'} · w` — ⚠️ **rung 5 only, never rung 4**, and produced in
`EllipticCurves.FunctionField.WeilPairingProductRelation` (`#845`). What this file supplies is the
right-hand side, and the translation of the Weil-pairing equivariance into the form that
computation consumes (`EllipticCurves.FunctionField.WeilPairingCyclotomic`).

## The specification

Both characters are pinned down by how they act on roots of unity:

* `galoisModularCyclotomicChar_spec` : `σ t = t ^ (χ_n σ).val` for every `t ∈ μ_n(F)`;
* `galoisCyclotomicChar_spec` : `σ t = t ^ ((χ_p σ).val.toZModPow k).val` for every `t` with
  `t ^ p ^ k = 1`;

and `galoisModularCyclotomicChar_unique` says the first property determines `χ_n σ`.

`galoisCyclotomicChar_toZModPow` is the compatibility between the two: the `p ^ k`-th level of
`χ_p` is `χ_{p ^ k}`. This is what makes `χ_p` a character *of the inverse system* `μ_{p^k}(F)`, and
therefore the right object to compare with `det ρ_{E,p}`, which is defined through the same inverse
system.

## Hypotheses, and that they are met

`χ_n` needs `hn : Nat.card μ_n(F) = n` — that `F` really contains `n` `n`-th roots of unity — and
the specification of `χ_p` needs `HasEnoughRootsOfUnity F (p ^ i)` for every `i`. Both hold in the
setting the Tate module is built over: `galoisModularCyclotomicChar_hypothesis_of_isSepClosed` and
`hasEnoughRootsOfUnity_pow_of_isSepClosed` record that a separably closed `F` with `(p : F) ≠ 0`
supplies both — the second because Mathlib already makes it an instance, so typeclass search finds
it and a consumer discharges nothing by hand.

## Main definitions

* `galoisRingAut` : the tautological `(F ≃ₐ[S] F) →* RingAut F`.
* `galoisModularCyclotomicChar` : `χ_n : (F ≃ₐ[S] F) →* (ZMod n)ˣ`.
* `galoisCyclotomicChar` : `χ_p : (F ≃ₐ[S] F) →* ℤ_[p]ˣ`.

## Main statements

* `galoisModularCyclotomicChar_spec`, `galoisModularCyclotomicChar_unique`.
* `restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar` : the Galois action on `μ_n(F)` *is*
  raising to the power `χ_n(σ)`. This is the bridge to the Weil-pairing equivariance statements,
  which are phrased through `restrictRootsOfUnity`.
* `galoisModularCyclotomicChar_eq_one_iff` : `χ_n σ = 1` if and only if `σ` fixes every `n`-th root
  of unity — the character is a genuine invariant of `σ`, not bookkeeping.
* `galoisCyclotomicChar_spec`, `galoisCyclotomicChar_toZModPow`.
* `galoisCyclotomicChar_continuous` : `χ_p` is continuous for the Krull topology on `F ≃ₐ[S] F`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.7, III.8.1(d) and III.8.3.
-/

/-! ### The tautological action of `Gal(F/S)` on `F` -/

/-- **The tautological homomorphism `Gal(F/S) →* RingAut F`.** An `S`-algebra automorphism of `F`
is in particular a ring automorphism, multiplicatively in `σ`.

Mathlib's cyclotomic characters are homomorphisms out of `RingAut F = F ≃+* F`; composing with this
map is what turns them into characters of `F ≃ₐ[S] F`. It is definitionally the identity on the
underlying function (`galoisRingAut_apply`), so every Mathlib lemma about
`modularCyclotomicCharacter` or `cyclotomicCharacter` applies at `galoisRingAut S F σ` with no
bridging rewrite.

Marked `noncomputable`: the definition is computable, but compiling it costs about seventy seconds
of build time for code no one runs. -/
noncomputable def galoisRingAut (S F : Type*) [Field S] [Field F] [Algebra S F] :
    (F ≃ₐ[S] F) →* RingAut F :=
  MulSemiringAction.toRingAut (F ≃ₐ[S] F) F

@[simp] lemma galoisRingAut_apply {S F : Type*} [Field S] [Field F] [Algebra S F]
    (σ : F ≃ₐ[S] F) (x : F) : galoisRingAut S F σ x = σ x := rfl

variable {S F : Type*} [Field S] [Field F] [Algebra S F]

/-! ### The modular cyclotomic character `χ_n` -/

/-- **The mod-`n` cyclotomic character** `χ_n : Gal(F/S) →* (ℤ/nℤ)ˣ`, characterised by
`σ ζ = ζ ^ χ_n(σ)` for every `n`-th root of unity `ζ` of `F`.

The hypothesis `hn` says that `F` contains exactly `n` `n`-th roots of unity, so that the exponent
is well defined modulo `n` rather than modulo the size of `μ_n(F)`. -/
noncomputable def galoisModularCyclotomicChar (S F : Type*) [Field S] [Field F] [Algebra S F]
    {n : ℕ} [NeZero n] (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) :
    (F ≃ₐ[S] F) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter F hn).comp (galoisRingAut S F)

/-- **The defining property of `χ_n`:** `σ` raises every `n`-th root of unity to the power
`χ_n(σ)`. -/
theorem galoisModularCyclotomicChar_spec {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (σ : F ≃ₐ[S] F) {t : Fˣ}
    (ht : t ∈ rootsOfUnity n F) :
    σ (t : F) = (t : F) ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val :=
  modularCyclotomicCharacter.spec F hn (galoisRingAut S F σ) ht

/-- **`χ_n(σ)` is the only exponent with that property.** -/
theorem galoisModularCyclotomicChar_unique {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (σ : F ≃ₐ[S] F) {c : ZMod n}
    (hc : ∀ t ∈ rootsOfUnity n F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F) ^ c.val) :
    c = galoisModularCyclotomicChar S F hn σ :=
  modularCyclotomicCharacter.unique F hn (galoisRingAut S F σ) hc

/-- **The Galois action on `μ_n(F)` is raising to the power `χ_n(σ)`.**

`restrictRootsOfUnity` is how the Galois action on the value group of the Weil pairing is spelled in
`EllipticCurves.FunctionField.WeilPairingGaloisMu` and
`EllipticCurves.FunctionField.WeilPairingGaloisDivisor`; this identifies it with an explicit power.
It is the step that turns "`e_n` is Galois-equivariant" into the classical
`e_n(σS, σT) = e_n(S, T) ^ χ_n(σ)` (Silverman AEC III.8.1(d)), carried out in
`EllipticCurves.FunctionField.WeilPairingCyclotomic`. -/
theorem restrictRootsOfUnity_eq_pow_galoisModularCyclotomicChar {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (σ : F ≃ₐ[S] F) (ζ : rootsOfUnity n F) :
    restrictRootsOfUnity (σ.toRingEquiv.toRingHom) n ζ
      = ζ ^ ((galoisModularCyclotomicChar S F hn σ : ZMod n)).val := by
  ext
  push_cast
  rw [restrictRootsOfUnity_coe_apply]
  exact galoisModularCyclotomicChar_spec hn σ ζ.2

/-! ### The character is trivial exactly on the elements acting trivially -/

/-- Raising an `n`-th root of unity to the power `(1 : ZMod n).val` does nothing.

Not a `simp` triviality: `(1 : ZMod n).val` is `1` only when `1 < n`, and is `0` at `n = 1`. The
degenerate case works because `μ_1(F)` is trivial, so `t = 1` there. -/
lemma pow_val_one_of_mem_rootsOfUnity {n : ℕ} [NeZero n] {t : Fˣ} (ht : t ∈ rootsOfUnity n F) :
    ((t : F)) ^ ((1 : ZMod n)).val = (t : F) := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) with h1 | h1
  · have htone : t = 1 := by
      have h := (mem_rootsOfUnity n t).mp ht
      rwa [← h1, pow_one] at h
    rw [htone]
    simp
  · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]

/-- **`χ_n(σ) = 1` if and only if `σ` fixes every `n`-th root of unity.**

The character is therefore a genuine invariant of `σ`, and not bookkeeping that could be trivial for
every `σ` — it detects exactly the elements of `Gal(F/S)` acting trivially on `μ_n(F)`. This holds
for every extension `F / S` and every `n`, so no concrete field is needed to see it. -/
theorem galoisModularCyclotomicChar_eq_one_iff {n : ℕ} [NeZero n]
    (hn : Nat.card { x // x ∈ rootsOfUnity n F } = n) (σ : F ≃ₐ[S] F) :
    galoisModularCyclotomicChar S F hn σ = 1
      ↔ ∀ t ∈ rootsOfUnity n F, σ ((t : Fˣ) : F) = ((t : Fˣ) : F) := by
  constructor
  · intro h t ht
    have hval : ((galoisModularCyclotomicChar S F hn σ : (ZMod n)ˣ) : ZMod n) = 1 := by
      rw [h, Units.val_one]
    rw [galoisModularCyclotomicChar_spec hn σ ht, hval, pow_val_one_of_mem_rootsOfUnity ht]
  · intro h
    refine Units.ext ?_
    refine (galoisModularCyclotomicChar_unique hn σ (c := 1) fun t ht => ?_).symm
    rw [h t ht, pow_val_one_of_mem_rootsOfUnity ht]

/-! ### The `p`-adic cyclotomic character `χ_p` -/

/-- **The `p`-adic cyclotomic character** `χ_p : Gal(F/S) →* ℤ_[p]ˣ`, assembling the mod-`p ^ k`
characters over all `k` (`galoisCyclotomicChar_toZModPow`).

This is the character `det ρ_{E,p}` is expected to equal: `galoisDetTwo` of
`EllipticCurves.TateModule.Determinant` has type `(F ≃ₐ[S] F) →* ℤ_[2]ˣ`, exactly the type of
`galoisCyclotomicChar S F 2`. As Mathlib defines it, `χ_p` is the trivial character when `F` fails
to contain enough roots of unity, so the statements below carry
`[∀ i, HasEnoughRootsOfUnity F (p ^ i)]`. -/
noncomputable def galoisCyclotomicChar (S F : Type*) [Field S] [Field F] [Algebra S F]
    (p : ℕ) [Fact p.Prime] : (F ≃ₐ[S] F) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter F p).comp (galoisRingAut S F)

/-- **The defining property of `χ_p`:** modulo `p ^ k`, it raises `p ^ k`-th roots of unity to their
`σ`-images. -/
theorem galoisCyclotomicChar_spec (p : ℕ) [Fact p.Prime] [∀ i, HasEnoughRootsOfUnity F (p ^ i)]
    (σ : F ≃ₐ[S] F) {k : ℕ} (t : F) (ht : t ^ p ^ k = 1) :
    σ t = t ^ ((galoisCyclotomicChar S F p σ).val.toZModPow k).val :=
  cyclotomicCharacter.spec p (galoisRingAut S F σ) t ht

/-- **`χ_p` refines to `χ_{p ^ k}` at every level.** This is the compatibility that makes `χ_p` a
character of the inverse system `μ_{p ^ k}(F)`, hence the right object to compare with the
determinant of the `p`-adic representation, which is built from the same system. -/
theorem galoisCyclotomicChar_toZModPow (p : ℕ) [Fact p.Prime]
    [∀ i, HasEnoughRootsOfUnity F (p ^ i)] (σ : F ≃ₐ[S] F) (k : ℕ) :
    (galoisCyclotomicChar S F p σ).val.toZModPow k
      = (galoisModularCyclotomicChar S F
          (HasEnoughRootsOfUnity.natCard_rootsOfUnity F (p ^ k)) σ).val :=
  cyclotomicCharacter.toZModPow p (galoisRingAut S F σ)

/-- **`χ_p` is continuous** for the Krull topology on `Gal(F/S)` and the `p`-adic topology on
`ℤ_[p]ˣ`.

Recorded here because the target `det ρ_{E,2} = χ_2` should be an equality of *continuous*
characters: the continuity of `ρ_{E,2}` is itself a theorem of this development
(`EllipticCurves.TateModule.Continuity`, `EllipticCurves.TateModule.MatrixContinuity`), and it would
be odd to compare it with a character not known to be continuous. Unlike the statements above this
needs no roots-of-unity hypothesis — in the degenerate case `χ_p` is constant. -/
theorem galoisCyclotomicChar_continuous (p : ℕ) [Fact p.Prime] :
    Continuous (galoisCyclotomicChar S F p) :=
  cyclotomicCharacter.continuous p S F

/-! ### The hypotheses are met in the setting of the Tate module -/

/-- Over a separably closed field of characteristic not dividing `p`, every `p ^ i` has its full
complement of roots of unity. This is the standing setting of `EllipticCurves.TateModule`, so the
`[∀ i, HasEnoughRootsOfUnity F (p ^ i)]` hypothesis above is not a burden on the consumer.

Recorded as a theorem rather than an instance: `IsSepClosed.hasEnoughRootsOfUnity_pow` already
supplies it to typeclass search, and a second copy would only add a redundant node. The point of
stating it is that the fact be greppable from this file. -/
theorem hasEnoughRootsOfUnity_pow_of_isSepClosed [IsSepClosed F] (p i : ℕ)
    [NeZero ((p : ℕ) : F)] : HasEnoughRootsOfUnity F (p ^ i) :=
  inferInstance

/-- Likewise the counting hypothesis `hn` of `galoisModularCyclotomicChar` is available over a
separably closed field of characteristic not dividing `n`. -/
theorem galoisModularCyclotomicChar_hypothesis_of_isSepClosed [IsSepClosed F] (n : ℕ)
    [NeZero ((n : ℕ) : F)] : Nat.card { x // x ∈ rootsOfUnity n F } = n :=
  haveI : NeZero n := .of_neZero_natCast F
  HasEnoughRootsOfUnity.natCard_rootsOfUnity F n
