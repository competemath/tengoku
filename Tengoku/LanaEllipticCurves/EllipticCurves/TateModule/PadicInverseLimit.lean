/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.NumberTheory.Padics.RingHoms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ring of `ℓ`-adic integers as the inverse limit `lim_k ZMod (ℓ^k)`

For a prime `p`, the ring `ℤ_[p]` of `p`-adic integers is the inverse limit
$$ \mathbb{Z}_p \;=\; \varprojlim_k \mathbb{Z}/p^k\mathbb{Z} $$
of the finite quotients along the reduction maps `ZMod (p^{k+1}) → ZMod (p^k)`. Mathlib's
`Mathlib.NumberTheory.Padics.RingHoms` provides the reduction maps `PadicInt.toZModPow` and the
universal property of `ℤ_[p]` as a projective limit (`PadicInt.lift` / `PadicInt.lift_spec` /
`PadicInt.lift_unique`, `PadicInt.ext_of_toZModPow`), but no explicit packaging of the limit
identification as an equivalence. This file supplies exactly that.

We realise the inverse limit concretely as the subring `PadicInt.compatSeq p` of the product ring
`∀ k, ZMod (p^k)` consisting of the *compatible sequences* `s` with
`ZMod.castHom … (s (k+1)) = s k` for all `k`, and prove the ring isomorphism

  `PadicInt.compatSeqEquiv : ℤ_[p] ≃+* PadicInt.compatSeq p`

whose forward map is `z ↦ (k ↦ PadicInt.toZModPow k z)` and whose inverse is
`PadicInt.lift` of the projection maps.

## Motivation — the Tate module `T_ℓ E`

This is the abstract inverse-limit identification that the freeness/rank statement of the Tate
module `T_ℓ E = lim_k E[ℓ^k]` consumes (Silverman, *The Arithmetic of Elliptic Curves*, III.7,
Remark 7.1.2): once the compatible levelwise isomorphisms `E[ℓ^k] ≅ (ZMod (ℓ^k))²` are available
(from the `n`-torsion structure theorem), transporting them through `compatSeqEquiv` levelwise
identifies `T_ℓ E` with `ℤ_[ℓ]²`.

## Main definitions

* `PadicInt.compatSeq p` : the subring of `∀ k, ZMod (p^k)` of compatible sequences.
* `PadicInt.compatSeq.proj k` : the projection ring hom `compatSeq p →+* ZMod (p^k)`.
* `PadicInt.toCompatSeq` : the forward ring hom `ℤ_[p] →+* compatSeq p`, `z ↦ (k ↦ toZModPow k z)`.
* `PadicInt.compatSeqEquiv` : the ring isomorphism `ℤ_[p] ≃+* compatSeq p`.

## Main statements

* `PadicInt.compatSeq.cast_apply` : the general compatibility `castHom (s n) = s m` for `m ≤ n`.
* `PadicInt.toZModPow_ofCompatSeq` : `toZModPow n (compatSeqEquiv.symm s) = s n`.
* `PadicInt.coe_compatSeqEquiv_apply` : `(compatSeqEquiv z) n = toZModPow n z`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

namespace PadicInt

variable (p : ℕ)

/-- The reduction ring hom `ZMod (p^n) →+* ZMod (p^m)` for `m ≤ n`. -/
private abbrev red {m n : ℕ} (h : m ≤ n) : ZMod (p ^ n) →+* ZMod (p ^ m) :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))

/-- The subring of `∀ k, ZMod (p^k)` of *compatible sequences*: those `s` for which the reduction
`ZMod (p^{k+1}) → ZMod (p^k)` sends `s (k+1)` to `s k`, for every `k`. This is the concrete
realisation of the inverse limit `lim_k ZMod (p^k)`. -/
def compatSeq : Subring (∀ k : ℕ, ZMod (p ^ k)) where
  carrier := {s | ∀ k, red p k.le_succ (s (k + 1)) = s k}
  mul_mem' {s t} hs ht k := by simp only [Pi.mul_apply, map_mul, hs k, ht k]
  one_mem' k := by simp only [Pi.one_apply, map_one]
  add_mem' {s t} hs ht k := by simp only [Pi.add_apply, map_add, hs k, ht k]
  zero_mem' k := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {s} hs k := by simp only [Pi.neg_apply, map_neg, hs k]

variable {p}

@[simp]
lemma mem_compatSeq_iff {s : ∀ k, ZMod (p ^ k)} :
    s ∈ compatSeq p ↔ ∀ k, red p k.le_succ (s (k + 1)) = s k := Iff.rfl

/-- Any two ring homomorphisms out of `ZMod (p^n)` agree, since `1` generates `ZMod (p^n)`. -/
private lemma red_comp_red {m n l : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ l) :
    (red p h₁).comp (red p h₂) = red p (h₁.trans h₂) :=
  RingHom.ext_zmod _ _

/-- General compatibility of a compatible sequence: the reduction `ZMod (p^n) → ZMod (p^m)` sends
`s n` to `s m` whenever `m ≤ n` (not just for `n = m + 1`). -/
lemma compatSeq.cast_apply {s : ∀ k, ZMod (p ^ k)} (hs : s ∈ compatSeq p) {m n : ℕ} (h : m ≤ n) :
    red p h (s n) = s m := by
  induction n, h using Nat.le_induction with
  | base =>
    have : red p (le_refl m) = RingHom.id (ZMod (p ^ m)) := RingHom.ext_zmod _ _
    rw [this, RingHom.id_apply]
  | succ n hmn ih =>
    have hstep : red p n.le_succ (s (n + 1)) = s n := (mem_compatSeq_iff.mp hs) n
    calc red p (hmn.trans n.le_succ) (s (n + 1))
        = (red p hmn).comp (red p n.le_succ) (s (n + 1)) := by rw [red_comp_red]
      _ = red p hmn (s n) := by rw [RingHom.comp_apply, hstep]
      _ = s m := ih

namespace compatSeq

variable (p) in
/-- The projection `compatSeq p →+* ZMod (p^k)` reading off the `k`-th coordinate. -/
def proj (k : ℕ) : compatSeq p →+* ZMod (p ^ k) :=
  (Pi.evalRingHom (fun k => ZMod (p ^ k)) k).comp (compatSeq p).subtype

@[simp]
lemma proj_apply (k : ℕ) (s : compatSeq p) : proj p k s = (s : ∀ k, ZMod (p ^ k)) k := rfl

/-- The projections form a compatible family for `PadicInt.lift`: reducing the `n`-th projection to
level `m` gives the `m`-th projection, for `m ≤ n`. -/
lemma red_comp_proj {m n : ℕ} (h : m ≤ n) : (red p h).comp (proj p n) = proj p m := by
  ext s
  simpa [proj, proj_apply] using compatSeq.cast_apply s.2 h

end compatSeq

variable [Fact p.Prime]

variable (p) in
/-- The forward ring hom `ℤ_[p] →+* compatSeq p`, sending `z` to the compatible sequence of its
reductions `k ↦ toZModPow k z`. -/
noncomputable def toCompatSeq : ℤ_[p] →+* compatSeq p where
  toFun z := ⟨fun k => toZModPow k z, fun k => by
    have := zmod_cast_comp_toZModPow (p := p) k (k + 1) k.le_succ
    exact RingHom.congr_fun this z⟩
  map_one' := Subtype.ext (funext fun k => by simp)
  map_mul' x y := Subtype.ext (funext fun k => by simp)
  map_zero' := Subtype.ext (funext fun k => by simp)
  map_add' x y := Subtype.ext (funext fun k => by simp)

@[simp]
lemma coe_toCompatSeq_apply (z : ℤ_[p]) (k : ℕ) :
    ((toCompatSeq p z : ∀ k, ZMod (p ^ k)) k) = toZModPow k z := rfl

/-- The inverse ring hom `compatSeq p →+* ℤ_[p]`, obtained from the universal property of `ℤ_[p]`
as the projective limit applied to the projection family. -/
noncomputable def ofCompatSeq : compatSeq p →+* ℤ_[p] :=
  lift (f := compatSeq.proj p) fun _ _ h => compatSeq.red_comp_proj h

@[simp]
lemma toZModPow_ofCompatSeq (n : ℕ) (s : compatSeq p) :
    toZModPow n (ofCompatSeq s) = (s : ∀ k, ZMod (p ^ k)) n := by
  have := lift_spec (f := compatSeq.proj p) (fun _ _ h => compatSeq.red_comp_proj h) n
  simpa [ofCompatSeq] using RingHom.congr_fun this s

/-- `ℤ_[p]` is the inverse limit `lim_k ZMod (p^k)`: the ring isomorphism between `ℤ_[p]` and the
subring of compatible sequences, with forward map `z ↦ (k ↦ toZModPow k z)` and inverse
`PadicInt.lift` of the projections. -/
noncomputable def compatSeqEquiv : ℤ_[p] ≃+* compatSeq p where
  toFun := toCompatSeq p
  invFun := ofCompatSeq
  left_inv z := by
    apply ext_of_toZModPow.mp
    intro n
    simp
  right_inv s := by
    apply Subtype.ext
    funext n
    simp
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
lemma coe_compatSeqEquiv_apply (z : ℤ_[p]) (n : ℕ) :
    ((compatSeqEquiv z : ∀ k, ZMod (p ^ k)) n) = toZModPow n z := rfl

@[simp]
lemma compatSeqEquiv_symm_apply (s : compatSeq p) : compatSeqEquiv.symm s = ofCompatSeq s := rfl

end PadicInt
