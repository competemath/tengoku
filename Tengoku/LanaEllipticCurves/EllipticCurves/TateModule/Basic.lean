/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.NumberTheory.Padics.RingHoms
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `ℓ`-adic Tate module `T_ℓ E` of a Weierstrass curve

For a Weierstrass curve `W` over a field `F` and a prime `ℓ`, the *`ℓ`-adic Tate module* is the
inverse limit
$$ T_\ell E \;=\; \varprojlim_k E[\ell^k] $$
of the `ℓ`-power torsion subgroups `E[ℓ^k]` along the multiplication-by-`ℓ` transition maps
`E[ℓ^{k+1}] → E[ℓ^k]` (Silverman, *The Arithmetic of Elliptic Curves*, III.7).

This file constructs `T_ℓ E` concretely as the additive subgroup of *compatible families*
`f : ℕ → W.Point` with `f k ∈ E[ℓ^k]` and `ℓ • f (k + 1) = f k` for every `k`, records its
projection maps to the finite levels `E[ℓ^k]`, and equips it with its natural `ℤ_ℓ`-module
structure: a `ℓ`-adic integer `a ∈ ℤ_ℓ` acts on level `k` through its residue
`PadicInt.toZModPow k a ∈ ZMod (ℓ^k)`, using that `E[ℓ^k]` is a `ZMod (ℓ^k)`-module. The families
being killed by `ℓ^k` at level `k` is exactly what makes this action well-defined and independent of
the level, via `AddSubgroup.torsionBy.mod_self_nsmul'`.

## Main definitions

* `WeierstrassCurve.Affine.tateModule W ℓ` : the Tate module `T_ℓ E`, as an
  `AddSubgroup (ℕ → W.Point)`.
* `WeierstrassCurve.Affine.tateModule.proj k` : the projection `T_ℓ E →+ E[ℓ^k]`.
* the `Module ℤ_[ℓ] (W.tateModule ℓ)` instance.

## Main statements

* `WeierstrassCurve.Affine.tateModule.ext` : two elements of `T_ℓ E` agree iff all their
  projections agree.
* `WeierstrassCurve.Affine.tateModule.smul_proj` : the `ℓ`-adic action of `a` on the level-`k`
  projection is scalar multiplication by `PadicInt.toZModPow k a`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### The Tate module as an inverse limit of `ℓ`-power torsion -/

variable (W : Affine F) (ℓ : ℕ)

/-- The defining predicate of the Tate module: a family `f : ℕ → W.Point` is a *compatible family*
if `f k` is `ℓ^k`-torsion and `ℓ • f (k + 1) = f k` for every `k`. -/
def IsCompatibleFamily (f : ℕ → W.Point) : Prop :=
  (∀ k, f k ∈ W.torsion (ℓ ^ k)) ∧ ∀ k, ℓ • f (k + 1) = f k

/-- The `ℓ`-adic Tate module `T_ℓ E = lim_k E[ℓ^k]` of a Weierstrass curve `W`, realised concretely
as the additive subgroup of compatible families in `ℕ → W.Point`. -/
def tateModule : AddSubgroup (ℕ → W.Point) where
  carrier := {f | IsCompatibleFamily W ℓ f}
  zero_mem' := ⟨fun k => (W.torsion (ℓ ^ k)).zero_mem, fun k => by simp⟩
  add_mem' {f g} hf hg :=
    ⟨fun k => (W.torsion (ℓ ^ k)).add_mem (hf.1 k) (hg.1 k), fun k => by
      simp only [Pi.add_apply, smul_add, hf.2 k, hg.2 k]⟩
  neg_mem' {f} hf :=
    ⟨fun k => (W.torsion (ℓ ^ k)).neg_mem (hf.1 k), fun k => by
      simp only [Pi.neg_apply, smul_neg, hf.2 k]⟩

namespace tateModule

variable {W ℓ}

@[simp]
lemma mem_iff {f : ℕ → W.Point} : f ∈ W.tateModule ℓ ↔ IsCompatibleFamily W ℓ f := Iff.rfl

/-- The level-`k` value of an element of the Tate module lies in `E[ℓ^k]`. -/
lemma coe_mem_torsion (f : W.tateModule ℓ) (k : ℕ) : (f : ℕ → W.Point) k ∈ W.torsion (ℓ ^ k) :=
  f.2.1 k

/-- Compatibility of the level values: `ℓ • f (k + 1) = f k`. -/
lemma smul_coe_succ (f : W.tateModule ℓ) (k : ℕ) :
    ℓ • (f : ℕ → W.Point) (k + 1) = (f : ℕ → W.Point) k :=
  f.2.2 k

@[ext]
lemma ext {f g : W.tateModule ℓ} (h : ∀ k, (f : ℕ → W.Point) k = (g : ℕ → W.Point) k) : f = g :=
  Subtype.ext (funext h)

/-- The projection `T_ℓ E →+ E[ℓ^k]` onto the level-`k` torsion. -/
@[simps]
def proj (k : ℕ) : W.tateModule ℓ →+ W.torsion (ℓ ^ k) where
  toFun f := ⟨(f : ℕ → W.Point) k, f.2.1 k⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projections are compatible with the multiplication-by-`ℓ` transition maps:
`ℓ • proj (k + 1) f = proj k f` at the level of `W.Point`. -/
lemma smul_proj_succ (f : W.tateModule ℓ) (k : ℕ) :
    ℓ • ((proj (k + 1) f : W.Point)) = (proj k f : W.Point) :=
  f.2.2 k

/-! ### The `ℤ_ℓ`-module structure -/

section PadicModule

open PadicInt

variable [hℓ : Fact ℓ.Prime]

private lemma pow_neZero (k : ℕ) : NeZero (ℓ ^ k) := ⟨(pow_pos hℓ.out.pos k).ne'⟩

omit hℓ in
/-- Two natural numbers that are congruent modulo `ℓ^k` act identically on `ℓ^k`-torsion, since the
`nsmul`-action on `E[ℓ^k]` factors through the residue modulo `ℓ^k`. -/
private lemma nsmul_torsion_congr {k : ℕ} {x : W.Point} (hx : x ∈ W.torsion (ℓ ^ k))
    {s t : ℕ} (h : s ≡ t [MOD ℓ ^ k]) : s • x = t • x := by
  rw [AddSubgroup.torsionBy.mod_self_nsmul' s hx, AddSubgroup.torsionBy.mod_self_nsmul' t hx, h]

omit hℓ in
/-- A cast reformulation of `nsmul_torsion_congr`: if two natural numbers become equal in
`ZMod (ℓ^k)`, they act identically on `ℓ^k`-torsion. -/
private lemma nsmul_torsion_eq_of_cast {k : ℕ} {x : W.Point} (hx : x ∈ W.torsion (ℓ ^ k))
    {s t : ℕ} (h : (s : ZMod (ℓ ^ k)) = (t : ZMod (ℓ ^ k))) : s • x = t • x :=
  nsmul_torsion_congr hx ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)

/-- The residues of a `ℓ`-adic integer at successive levels are congruent modulo `ℓ^k`. -/
private lemma toZModPow_val_modEq (a : ℤ_[ℓ]) (k : ℕ) :
    (toZModPow (k + 1) a).val ≡ (toZModPow k a).val [MOD ℓ ^ k] := by
  haveI := pow_neZero (ℓ := ℓ) k
  haveI := pow_neZero (ℓ := ℓ) (k + 1)
  refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
  rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, cast_toZModPow k (k + 1) (Nat.le_succ k)]

/-- Scalar multiplication of the Tate module by a `ℓ`-adic integer: a `ℓ`-adic integer `a` acts on
level `k` through its residue `toZModPow k a ∈ ZMod (ℓ^k)`, i.e. by `nsmul` with
`(toZModPow k a).val`. -/
noncomputable instance : SMul ℤ_[ℓ] (W.tateModule ℓ) where
  smul a f := ⟨fun k => (toZModPow k a).val • (f : ℕ → W.Point) k, by
    refine ⟨fun k => (W.torsion (ℓ ^ k)).nsmul_mem (f.2.1 k) _, fun k => ?_⟩
    calc ℓ • ((toZModPow (k + 1) a).val • (f : ℕ → W.Point) (k + 1))
        = (toZModPow (k + 1) a).val • (ℓ • (f : ℕ → W.Point) (k + 1)) := by rw [smul_comm]
      _ = (toZModPow (k + 1) a).val • (f : ℕ → W.Point) k := by rw [f.2.2 k]
      _ = (toZModPow k a).val • (f : ℕ → W.Point) k :=
          nsmul_torsion_congr (f.2.1 k) (toZModPow_val_modEq a k)⟩

@[simp]
lemma smul_coe (a : ℤ_[ℓ]) (f : W.tateModule ℓ) (k : ℕ) :
    ((a • f : W.tateModule ℓ) : ℕ → W.Point) k = (toZModPow k a).val • (f : ℕ → W.Point) k :=
  rfl

/-- The `ℤ_ℓ`-action on the level-`k` projection is scalar multiplication by `toZModPow k a`. -/
lemma smul_proj (a : ℤ_[ℓ]) (f : W.tateModule ℓ) (k : ℕ) :
    ((proj k (a • f) : W.Point)) = (toZModPow k a).val • (proj k f : W.Point) :=
  rfl

noncomputable instance : Module ℤ_[ℓ] (W.tateModule ℓ) where
  one_smul f := by
    ext k
    haveI := pow_neZero (ℓ := ℓ) k
    rw [smul_coe]
    refine (nsmul_torsion_eq_of_cast (f.2.1 k) (t := 1) ?_).trans (one_nsmul _)
    simp [ZMod.natCast_val]
  mul_smul a b f := by
    ext k
    haveI := pow_neZero (ℓ := ℓ) k
    simp only [smul_coe, smul_smul]
    refine nsmul_torsion_eq_of_cast (f.2.1 k) ?_
    push_cast [ZMod.natCast_val, ZMod.cast_id, map_mul]
    ring
  smul_zero a := by ext k; simp
  smul_add a f g := by
    ext k
    simp only [smul_coe, AddSubgroup.coe_add, Pi.add_apply, smul_add]
  add_smul a b f := by
    ext k
    haveI := pow_neZero (ℓ := ℓ) k
    simp only [smul_coe, AddSubgroup.coe_add, Pi.add_apply, ← add_nsmul]
    refine nsmul_torsion_eq_of_cast (f.2.1 k) ?_
    push_cast [ZMod.natCast_val, ZMod.cast_id, map_add]
    ring
  zero_smul f := by
    ext k
    simp

end PadicModule

end tateModule

end WeierstrassCurve.Affine
