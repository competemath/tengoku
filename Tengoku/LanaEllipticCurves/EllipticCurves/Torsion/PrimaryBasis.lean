/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.Torsion.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Compatible bases for the `ℓ`-primary tower, for a general `ℓ`

For an elliptic curve `W` over a field, a *coherent system of generating pairs* for the `ℓ`-primary
tower is a pair of families `P Q : ℕ → W.Point` with

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (ℓ ^ k)
∀ k, ℓ • P (k + 1) = P k        ∀ k, ℓ • Q (k + 1) = Q k
```

Coherence — the second line — is what an inverse-limit argument needs and what a levelwise
structure theorem does not give: `E[ℓ^k] ≃+ (ZMod (ℓ^k))²` holds at each level *independently*, and
a family of unrelated isomorphisms says nothing about `T_ℓ E = lim_k E[ℓ^k]`.

This file builds such a system from two inputs and nothing else:

* **surjectivity of `[ℓ]` on `E(F̄)`**, taken as the hypothesis
  `hℓ : Function.Surjective fun P : W.Point => ℓ • P`, and
* **a generating pair of `E[ℓ]`** to start the recursion.

Both inputs are prime-specific and neither is proved here. `EllipticCurves.Torsion.TwoPrimaryBasis`
supplies them at `ℓ = 2` and `EllipticCurves.Torsion.ThreePrimaryBasis` at `ℓ = 3`; those two files
contain no argument, only the two inputs and a specialisation of every statement below.

⚠️ **Taking `[ℓ]`-surjectivity as an explicit hypothesis is this development's established idiom**
for exactly this situation: `EllipticCurves.TateModule.LevelStructure.proj_surjective` is stated
that way, with `proj_two_surjective` its one-line `ℓ = 2` instance.

## The mechanism

* **Lifting.** A preimage of an element of `E[ℓ^k]` under `[ℓ]` lies in `E[ℓ^{k+1}]` for free:
  `ℓ ^ (k + 1) • x = ℓ ^ k • (ℓ • x) = 0` (`exists_nsmul_eq_of_mem_torsion`).

* **Arbitrary lifts of a generating pair generate — as soon as `k ≥ 1`.** If
  `closure {P, Q} = E[ℓ^k]` and `ℓ • P' = P`, `ℓ • Q' = Q` with `P', Q' ∈ E[ℓ^{k+1}]`, put
  `H := closure {P', Q'}`. Then `E[ℓ^k] = closure {ℓ • P', ℓ • Q'} ≤ H`. Given `x ∈ E[ℓ^{k+1}]` we
  have `ℓ • x ∈ E[ℓ^k]`, so `ℓ • x = m • (ℓ • P') + n • (ℓ • Q') = ℓ • h` for
  `h := m • P' + n • Q'` in `H`; hence `x - h ∈ E[ℓ] ≤ E[ℓ^k] ≤ H` and `x ∈ H`
  (`closure_pair_eq_torsion_succ`).

  **`k ≥ 1` is essential** and enters at exactly one point: `E[ℓ] ≤ E[ℓ^k]`. At `k = 0` the
  statement is genuinely false — `P = Q = 0` generate `E[1] = ⊥`, but two lifts in `E[ℓ]` need not
  generate `E[ℓ]` (take them equal). So the recursion is started at `k = 1` from a chosen
  generating pair of `E[ℓ]`, and level `0` is filled in with `P 0 = Q 0 = 0`.

**No element orders, cardinalities, determinants or primality assumptions appear anywhere in the
inductive step**; the chain of containments `E[ℓ] ≤ E[ℓ^k] ≤ H` does all the work, and `ℓ` is an
arbitrary natural number throughout this section.

## The levelwise isomorphism, in explicit form

`AddCommGroup.equiv_zmod_sq_of_two_gen` concludes `Nonempty (A ≃+ ZMod n × ZMod n)` and so discards
the map. Inverse-limit arguments need the map itself, and in particular need its **injectivity**, so
this file also builds

```
torsionPairEquivOfCard : ZMod n × ZMod n ≃+ W.torsion n
  (a, b) ↦ a.val • P + b.val • Q
```

from a generating pair of `E[n]`. Surjectivity is `AddSubgroup.mem_closure_pair` plus reduction of
the integer coefficients mod `n`; injectivity is then free from a **cardinality hypothesis**
`Nat.card (W.torsion n) = n * n`, which is where — and only where — the counting theorems of the
`ℓ`-primary towers are consumed. ⚠️ Note that this half of the file is stated for an arbitrary
modulus `n`, not for a prime power: nothing in it inspects the shape of `n`.

## Main statements

* `WeierstrassCurve.Affine.exists_nsmul_eq_of_mem_torsion`: lifting along `[ℓ]` in the tower.
* `WeierstrassCurve.Affine.closure_pair_eq_torsion_succ`: lifts of a generating pair generate.
* `WeierstrassCurve.Affine.exists_closure_pair_eq_torsion_of_addEquiv`: a generating pair of `E[n]`
  out of any isomorphism `E[n] ≃+ (ZMod n)²`.
* `WeierstrassCurve.Affine.exists_compatible_basis_of_surjective`: the coherent system.
* `WeierstrassCurve.Affine.torsionPairEquivOfCard`: the explicit `(ℤ/nℤ)² ≃+ E[n]`.
* `WeierstrassCurve.Affine.zmod_pair_eq_zero_iff_of_card`: uniqueness of the coefficients.
* `WeierstrassCurve.Affine.ne_zero_and_ne_of_closure_pair_of_card`: a generating pair is
  non-degenerate.

## Provenance

The contents of this file were extracted from `EllipticCurves.Torsion.TwoPrimaryBasis`, whose own
module docstring stated that its proofs work "verbatim for any prime `ℓ` whose `[ℓ]`-surjectivity is
established, with `2` replaced by `ℓ`". Making that sentence true of the *statements* rather than
only of the *proofs* is what this file does; it is what lets `Torsion/ThreePrimaryBasis.lean` be a
list of instantiations rather than a second copy of a 446-line argument.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

open scoped AddSubgroup

/-! ### Coefficients modulo `n` acting on `n`-torsion elements of an abelian group

The six declarations of this section mention no curve; they are statements about an arbitrary
additive commutative group and their natural home is Mathlib. They are placed at the root namespace
for that reason, following the placement discipline that
`EllipticCurves.TateModule.DeterminantMod` states for `AddEquiv.toZModLinearEquiv` and
`EllipticCurves.Torsion.ThreePrimary` for `Nat.exists_eq_two_pow_mul_three_pow`. -/

section Generic

variable {A : Type*} [AddCommGroup A]

/-- Natural numbers with the same residue mod `n` act identically on an element killed by `n`. -/
theorem nsmul_congr_of_natCast_eq {n : ℕ} {g : A} (hg : n • g = 0) {s t : ℕ}
    (h : (s : ZMod n) = (t : ZMod n)) : s • g = t • g := by
  rw [nsmul_eq_mod_nsmul s hg, nsmul_eq_mod_nsmul t hg,
    (ZMod.natCast_eq_natCast_iff' s t n).mp h]

/-- An integer acts on an element killed by `n` through the canonical representative of its residue
class in `ZMod n`. -/
theorem zsmul_eq_val_nsmul {n : ℕ} [NeZero n] {g : A} (hg : n • g = 0) (m : ℤ) :
    m • g = ((m : ZMod n)).val • g := by
  obtain ⟨c, hc⟩ : (n : ℤ) ∣ m - (((m : ZMod n)).val : ℤ) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id]
    ring
  have hm : m = c * (n : ℤ) + (((m : ZMod n)).val : ℤ) := by linarith [hc]
  conv_lhs => rw [hm]
  rw [add_zsmul, mul_zsmul, natCast_zsmul, hg, smul_zero, zero_add, natCast_zsmul]

/-- The additive homomorphism `(ZMod n)² →+ A` attached to a pair of elements of `A` killed by `n`,
namely `(a, b) ↦ a.val • g₁ + b.val • g₂`. -/
def zmodPairHom {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0) :
    ZMod n × ZMod n →+ A where
  toFun ab := ab.1.val • g₁ + ab.2.val • g₂
  map_zero' := by simp
  map_add' ab cd := by
    have e₁ : ((ab.1 + cd.1).val : ZMod n) = ((ab.1.val + cd.1.val : ℕ) : ZMod n) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rfl
    have e₂ : ((ab.2 + cd.2).val : ZMod n) = ((ab.2.val + cd.2.val : ℕ) : ZMod n) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      rfl
    rw [Prod.fst_add, Prod.snd_add, nsmul_congr_of_natCast_eq h₁ e₁,
      nsmul_congr_of_natCast_eq h₂ e₂, add_nsmul, add_nsmul]
    abel

@[simp]
theorem zmodPairHom_apply {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0)
    (ab : ZMod n × ZMod n) : zmodPairHom h₁ h₂ ab = ab.1.val • g₁ + ab.2.val • g₂ := rfl

/-- The `ZMod n`-coefficient map onto a pair of generators is surjective onto the subgroup they
generate. -/
theorem zmodPairHom_surjOn {n : ℕ} [NeZero n] {g₁ g₂ : A} (h₁ : n • g₁ = 0) (h₂ : n • g₂ = 0)
    {x : A} (hx : x ∈ AddSubgroup.closure ({g₁, g₂} : Set A)) :
    ∃ ab : ZMod n × ZMod n, zmodPairHom h₁ h₂ ab = x := by
  obtain ⟨m, l, hml⟩ := AddSubgroup.mem_closure_pair.mp hx
  exact ⟨((m : ZMod n), (l : ZMod n)), by
    rw [zmodPairHom_apply, ← zsmul_eq_val_nsmul h₁ m, ← zsmul_eq_val_nsmul h₂ l, hml]⟩

/-- In `ZMod n × ZMod n` the two standard vectors generate. -/
theorem closure_pair_zmod_prod (n : ℕ) [NeZero n] :
    AddSubgroup.closure ({((1 : ZMod n), (0 : ZMod n)), ((0 : ZMod n), (1 : ZMod n))} :
      Set (ZMod n × ZMod n)) = ⊤ := by
  have h1 : ((1 : ZMod n), (0 : ZMod n)) ∈ ({((1 : ZMod n), (0 : ZMod n)),
      ((0 : ZMod n), (1 : ZMod n))} : Set (ZMod n × ZMod n)) := Set.mem_insert _ _
  have h2 : ((0 : ZMod n), (1 : ZMod n)) ∈ ({((1 : ZMod n), (0 : ZMod n)),
      ((0 : ZMod n), (1 : ZMod n))} : Set (ZMod n × ZMod n)) := Set.mem_insert_of_mem _ rfl
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have hab : ((a, b) : ZMod n × ZMod n)
      = a.val • ((1 : ZMod n), (0 : ZMod n)) + b.val • ((0 : ZMod n), (1 : ZMod n)) := by
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_zero, add_zero, zero_add,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one, ZMod.natCast_rightInverse a,
      ZMod.natCast_rightInverse b]
  rw [hab]
  exact add_mem
    (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure h1) _)
    (AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure h2) _)

end Generic

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F}

/-! ### Membership in the subgroup generated by a pair -/

theorem mem_closure_fst (P Q : W.Point) :
    P ∈ AddSubgroup.closure ({P, Q} : Set W.Point) :=
  AddSubgroup.subset_closure (Set.mem_insert _ _)

theorem mem_closure_snd (P Q : W.Point) :
    Q ∈ AddSubgroup.closure ({P, Q} : Set W.Point) :=
  AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- The first member of a generating pair of `E[n]` is killed by `n`. -/
theorem nsmul_fst_of_closure {n : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    n • P = 0 :=
  mem_torsion_iff.mp (by rw [← hgen]; exact mem_closure_fst P Q)

/-- The second member of a generating pair of `E[n]` is killed by `n`. -/
theorem nsmul_snd_of_closure {n : ℕ} {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    n • Q = 0 :=
  mem_torsion_iff.mp (by rw [← hgen]; exact mem_closure_snd P Q)

/-! ### Lifting along multiplication by `ℓ` inside the tower -/

/-- **Lifting inside the `ℓ`-primary tower.** If `[ℓ]` is surjective on `E(F̄)` then every element
of `E[ℓ^k]` is `ℓ` times an element of `E[ℓ^{k+1}]`: a preimage exists by hypothesis, and it
automatically lands one level up, `ℓ ^ (k + 1) • x = ℓ ^ k • (ℓ • x) = 0`. -/
theorem exists_nsmul_eq_of_mem_torsion {ℓ : ℕ}
    (hℓ : Function.Surjective fun P : W.Point => ℓ • P) {k : ℕ} {y : W.Point}
    (hy : y ∈ W.torsion (ℓ ^ k)) : ∃ x ∈ W.torsion (ℓ ^ (k + 1)), ℓ • x = y := by
  obtain ⟨x, hx⟩ := hℓ y
  have hx' : ℓ • x = y := hx
  refine ⟨x, ?_, hx'⟩
  rw [mem_torsion_iff, pow_succ, mul_smul, hx']
  exact hy

/-! ### Lifts of a generating pair generate one level up -/

/-- **The inductive step.** If `P`, `Q` generate `E[ℓ^k]` with `k ≥ 1`, then *any* lifts `P'`, `Q'`
of them along multiplication by `ℓ` generate `E[ℓ^{k+1}]`.

The proof uses no element orders, no cardinalities, no determinants and no assumption on `ℓ`
whatsoever — `ℓ` is an arbitrary natural number. Writing `H := closure {P', Q'}`, the containment
`E[ℓ^k] = closure {ℓ • P', ℓ • Q'} ≤ H` is immediate; for `x ∈ E[ℓ^{k+1}]` the element `ℓ • x` lies
in `E[ℓ^k]`, hence is `ℓ • h` for some `h ∈ H`, and then `x - h ∈ E[ℓ] ≤ E[ℓ^k] ≤ H`.

The hypothesis `1 ≤ k` enters at exactly one place, the containment `E[ℓ] ≤ E[ℓ^k]`, and it cannot
be dropped: at `k = 0` the pair `P = Q = 0` generates `E[1] = ⊥`, but two equal lifts in `E[ℓ]`
generate a cyclic group, not `E[ℓ]`. -/
theorem closure_pair_eq_torsion_succ {ℓ k : ℕ} (hk : 1 ≤ k) {P Q P' Q' : W.Point}
    (hP' : P' ∈ W.torsion (ℓ ^ (k + 1))) (hQ' : Q' ∈ W.torsion (ℓ ^ (k + 1)))
    (hP : ℓ • P' = P) (hQ : ℓ • Q' = Q)
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion (ℓ ^ k)) :
    AddSubgroup.closure ({P', Q'} : Set W.Point) = W.torsion (ℓ ^ (k + 1)) := by
  set H := AddSubgroup.closure ({P', Q'} : Set W.Point) with hH
  have hP'H : P' ∈ H := AddSubgroup.subset_closure (Set.mem_insert _ _)
  have hQ'H : Q' ∈ H := AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  -- `E[ℓ^k] ≤ H`, because `E[ℓ^k]` is generated by `ℓ • P'` and `ℓ • Q'`.
  have hle : W.torsion (ℓ ^ k) ≤ H := by
    rw [← hgen, AddSubgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hP ▸ AddSubgroup.nsmul_mem _ hP'H ℓ
    · exact hQ ▸ AddSubgroup.nsmul_mem _ hQ'H ℓ
  refine le_antisymm ?_ fun x hx => ?_
  · rw [AddSubgroup.closure_le]
    rintro x (rfl | rfl) <;> assumption
  · -- `ℓ • x` lies in `E[ℓ^k]`, hence is an integer combination of `ℓ • P'` and `ℓ • Q'`.
    have hlx : ℓ • x ∈ W.torsion (ℓ ^ k) := by
      rw [mem_torsion_iff, ← mul_smul, ← pow_succ]
      exact hx
    rw [← hgen] at hlx
    obtain ⟨m, l, hml⟩ := AddSubgroup.mem_closure_pair.mp hlx
    have hhH : m • P' + l • Q' ∈ H :=
      AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hP'H m) (AddSubgroup.zsmul_mem _ hQ'H l)
    -- The difference is killed by `ℓ`, hence lies in `E[ℓ] ≤ E[ℓ^k] ≤ H`.
    have hdiff : x - (m • P' + l • Q') ∈ W.torsion ℓ := by
      rw [mem_torsion_iff, smul_sub, sub_eq_zero, smul_add, smul_comm ℓ m, smul_comm ℓ l, hP, hQ,
        hml]
    have : x - (m • P' + l • Q') ∈ H :=
      hle (torsion_mono (dvd_pow_self ℓ (by omega)) hdiff)
    simpa using AddSubgroup.add_mem _ this hhH

/-! ### The base of the tower: a generating pair for `E[n]` -/

/-- **A generating pair of `E[n]` out of an isomorphism `E[n] ≃+ (ZMod n)²`**: transport the two
standard vectors, which generate by `closure_pair_zmod_prod`.

This is the step that starts the recursion of `exists_compatible_basis_of_surjective`, applied at
`n = ℓ`, and it is the only place where a structure theorem for `E[ℓ]` is used. -/
theorem exists_closure_pair_eq_torsion_of_addEquiv {n : ℕ} [NeZero n]
    (e : W.torsion n ≃+ ZMod n × ZMod n) :
    ∃ P Q : W.Point, P ∈ W.torsion n ∧ Q ∈ W.torsion n ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n := by
  refine ⟨(e.symm (1, 0) : W.Point), (e.symm (0, 1) : W.Point),
    (e.symm (1, 0)).2, (e.symm (0, 1)).2, ?_⟩
  have htop : AddSubgroup.closure ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion n)) = ⊤ := by
    have himg : (e.symm.toAddMonoidHom) ''
        ({((1 : ZMod n), (0 : ZMod n)), ((0 : ZMod n), (1 : ZMod n))} : Set (ZMod n × ZMod n))
        = ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion n)) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [← himg, ← AddMonoidHom.map_closure, closure_pair_zmod_prod n,
      AddSubgroup.map_top_of_surjective _ e.symm.surjective]
  have hsub : AddSubgroup.map (W.torsion n).subtype
      (AddSubgroup.closure ({e.symm (1, 0), e.symm (0, 1)} : Set (W.torsion n)))
      = AddSubgroup.closure ({(e.symm (1, 0) : W.Point), (e.symm (0, 1) : W.Point)} :
        Set W.Point) := by
    rw [AddMonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [← hsub, htop, ← AddMonoidHom.range_eq_map, AddSubgroup.range_subtype]

/-! ### The coherent system -/

/-- **Compatible bases for the `ℓ`-primary tower.** Given surjectivity of `[ℓ]` on `E(F̄)` and a
generating pair of `E[ℓ]`, there is a system of generating pairs of the groups `E[ℓ^k]`, coherent
for the transition maps `x ↦ ℓ • x` of the tower:

```
∀ k, AddSubgroup.closure {P k, Q k} = W.torsion (ℓ ^ k)
∀ k, ℓ • P (k + 1) = P k        ∀ k, ℓ • Q (k + 1) = Q k
```

The recursion starts at level `1` from the given generating pair of `E[ℓ]` and climbs by
`closure_pair_eq_torsion_succ`; level `0` is filled in with `P 0 = Q 0 = 0`, which generates
`E[1] = ⊥`, and the compatibility `ℓ • P 1 = P 0` holds because `P 1` is `ℓ`-torsion. The family is
*chosen*, so the statement is existential; every consumer only ever needs one such system. -/
theorem exists_compatible_basis_of_surjective {ℓ : ℕ}
    (hℓ : Function.Surjective fun P : W.Point => ℓ • P)
    (hbase : ∃ P Q : W.Point, P ∈ W.torsion ℓ ∧ Q ∈ W.torsion ℓ ∧
      AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion ℓ) :
    ∃ P Q : ℕ → W.Point,
      (∀ k, AddSubgroup.closure ({P k, Q k} : Set W.Point) = W.torsion (ℓ ^ k)) ∧
      (∀ k, ℓ • P (k + 1) = P k) ∧ (∀ k, ℓ • Q (k + 1) = Q k) := by
  classical
  obtain ⟨g₁, g₂, hg₁, hg₂, hg⟩ := hbase
  -- One step of the recursion, made total by a junk value off the invariant.
  have key : ∀ (k : ℕ) (pq : W.Point × W.Point), ∃ pq' : W.Point × W.Point,
      AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) = W.torsion (ℓ ^ k) →
        AddSubgroup.closure ({pq'.1, pq'.2} : Set W.Point) = W.torsion (ℓ ^ (k + 1)) ∧
          ℓ • pq'.1 = pq.1 ∧ ℓ • pq'.2 = pq.2 := by
    intro k pq
    by_cases hpq : AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) = W.torsion (ℓ ^ k)
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- Level `0`: `E[ℓ^0] = E[1] = ⊥`, so the pair is `(0, 0)` and any pair in `E[ℓ]` lifts it.
        have hmem₁ : pq.1 ∈ AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) :=
          AddSubgroup.subset_closure (Set.mem_insert _ _)
        have hmem₂ : pq.2 ∈ AddSubgroup.closure ({pq.1, pq.2} : Set W.Point) :=
          AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        rw [hpq, pow_zero, torsion_one, AddSubgroup.mem_bot] at hmem₁ hmem₂
        refine ⟨(g₁, g₂), fun _ => ⟨by simpa using hg, ?_, ?_⟩⟩
        · rw [hmem₁]; exact mem_torsion_iff.mp hg₁
        · rw [hmem₂]; exact mem_torsion_iff.mp hg₂
      · -- Level `k ≥ 1`: lift both generators and apply the inductive step.
        have hp : pq.1 ∈ W.torsion (ℓ ^ k) :=
          hpq ▸ AddSubgroup.subset_closure (Set.mem_insert _ _)
        have hq : pq.2 ∈ W.torsion (ℓ ^ k) :=
          hpq ▸ AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        obtain ⟨p', hp'mem, hp'⟩ := exists_nsmul_eq_of_mem_torsion hℓ hp
        obtain ⟨q', hq'mem, hq'⟩ := exists_nsmul_eq_of_mem_torsion hℓ hq
        exact ⟨(p', q'), fun _ =>
          ⟨closure_pair_eq_torsion_succ hk hp'mem hq'mem hp' hq' hpq, hp', hq'⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hpq⟩
  choose nxt hnxt using key
  obtain ⟨b, hb0, hbs⟩ : ∃ b : ℕ → W.Point × W.Point,
      b 0 = (0, 0) ∧ ∀ k, b (k + 1) = nxt k (b k) :=
    ⟨fun k => Nat.rec ((0 : W.Point), (0 : W.Point)) nxt k, rfl, fun _ => rfl⟩
  have hgen : ∀ k, AddSubgroup.closure ({(b k).1, (b k).2} : Set W.Point) = W.torsion (ℓ ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [hb0, pow_zero, torsion_one]
      simp
    | succ k ih => rw [hbs]; exact (hnxt k (b k) ih).1
  refine ⟨fun k => (b k).1, fun k => (b k).2, hgen, fun k => ?_, fun k => ?_⟩
  · change ℓ • (b (k + 1)).1 = (b k).1
    rw [hbs]
    exact (hnxt k (b k) (hgen k)).2.1
  · change ℓ • (b (k + 1)).2 = (b k).2
    rw [hbs]
    exact (hnxt k (b k) (hgen k)).2.2

/-! ### The explicit isomorphism `(ℤ/nℤ)² ≃+ E[n]` -/

/-- The additive homomorphism `(ℤ/nℤ)² →+ E[n]`, `(a, b) ↦ a.val • P + b.val • Q`, attached to a
pair of generators of `E[n]`. -/
noncomputable def torsionPairHom {n : ℕ} [NeZero n] {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    ZMod n × ZMod n →+ W.torsion n :=
  (zmodPairHom (nsmul_fst_of_closure hgen) (nsmul_snd_of_closure hgen)).codRestrict
    (W.torsion n) fun ab => by
      rw [← hgen]
      exact AddSubgroup.add_mem _
        (AddSubgroup.nsmul_mem _ (mem_closure_fst P Q) _)
        (AddSubgroup.nsmul_mem _ (mem_closure_snd P Q) _)

@[simp]
lemma torsionPairHom_apply_coe {n : ℕ} [NeZero n] {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    (ab : ZMod n × ZMod n) :
    ((torsionPairHom hgen ab : W.torsion n) : W.Point) = ab.1.val • P + ab.2.val • Q := rfl

/-- **Every element of `E[n]` is a `ZMod n`-combination of a generating pair.** This is
`AddSubgroup.mem_closure_pair` together with the reduction of the integer coefficients modulo `n`,
which is legitimate because `P` and `Q` are killed by `n`. -/
theorem exists_zmod_pair_eq {n : ℕ} [NeZero n] {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    {x : W.Point} (hx : x ∈ W.torsion n) :
    ∃ a b : ZMod n, a.val • P + b.val • Q = x := by
  obtain ⟨ab, hab⟩ := zmodPairHom_surjOn (nsmul_fst_of_closure hgen) (nsmul_snd_of_closure hgen)
    (by rw [hgen]; exact hx)
  exact ⟨ab.1, ab.2, hab⟩

/-- `torsionPairHom` is bijective as soon as `#E[n] = n²`: it is surjective by
`exists_zmod_pair_eq`, and both sides then have `n²` elements.

⚠️ This is the **only** statement in this file that consumes a cardinality, and therefore the only
one whose `ℓ = 2` and `ℓ = 3` instances need the counting theorems `card_torsion_two_pow` and
`card_torsion_three_pow`. Everything above it is pure subgroup theory.

⚠️ **It used to carry `[Finite ↥(W.torsion n)]` as well, and that hypothesis was dead** — the
instance occurred in neither the remainder of the type nor the proof term, measured on the
elaborated environment at `2e44940` (`#1272`).  The reason is that
`Nat.bijective_iff_surjective_and_card` needs the **domain** finite, and the domain here is
`ZMod n × ZMod n`, which `[NeZero n]` already makes finite; the finiteness of `E[n]` was never
used.  ⚠️ Downstream this is not free bookkeeping:
`EllipticCurves.TateModule.PrimaryFree.padicPairHom_surjective` threaded a `∀ k, Finite (E[ℓ^k])`
hypothesis solely to feed this instance, and that hypothesis went with it — see that file's
retired paragraphs. -/
theorem torsionPairHom_bijective_of_card {n : ℕ} [NeZero n]
    (hcard : Nat.card (W.torsion n) = n * n) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    Function.Bijective (torsionPairHom hgen) := by
  refine (Nat.bijective_iff_surjective_and_card _).mpr ⟨fun x => ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := exists_zmod_pair_eq hgen x.2
    exact ⟨(a, b), Subtype.ext hab⟩
  · rw [Nat.card_prod, Nat.card_zmod, hcard]

/-- **The explicit structure isomorphism `(ℤ/nℤ)² ≃+ E[n]`** attached to a generating pair of
`E[n]`, when `#E[n] = n²`.

`AddCommGroup.equiv_zmod_sq_of_two_gen` concludes only `Nonempty`; inverse-limit arguments need the
map itself, and in particular its injectivity, which is what this bundles. -/
noncomputable def torsionPairEquivOfCard {n : ℕ} [NeZero n]
    (hcard : Nat.card (W.torsion n) = n * n) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    ZMod n × ZMod n ≃+ W.torsion n :=
  AddEquiv.ofBijective _ (torsionPairHom_bijective_of_card hcard hgen)

@[simp]
lemma torsionPairEquivOfCard_apply_coe {n : ℕ} [NeZero n]
    (hcard : Nat.card (W.torsion n) = n * n) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    (ab : ZMod n × ZMod n) :
    ((torsionPairEquivOfCard hcard hgen ab : W.torsion n) : W.Point)
      = ab.1.val • P + ab.2.val • Q := rfl

/-- **Uniqueness of the coefficients**: a `ZMod n`-combination of a generating pair vanishes only
for zero coefficients. This is the half that `AddCommGroup.equiv_zmod_sq_of_two_gen` discards, and
it is what identifies the inverse limit of a tower. -/
theorem zmod_pair_eq_zero_iff_of_card {n : ℕ} [NeZero n]
    (hcard : Nat.card (W.torsion n) = n * n) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n)
    {a b : ZMod n} : a.val • P + b.val • Q = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have : torsionPairHom hgen (a, b) = torsionPairHom hgen (0, 0) := by
      refine Subtype.ext ?_
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, h]
      simp
    exact Prod.mk.injEq .. ▸ (Prod.ext_iff.mp
      ((torsionPairHom_bijective_of_card hcard hgen).1 this))
  · rintro ⟨rfl, rfl⟩
    simp

/-- **A generating pair of `E[n]` with `1 < n` is non-degenerate**: both members are nonzero and
they are distinct. This is the qualitative content of the injectivity half, and it is what rules out
the degenerate systems that the existential statements would otherwise permit — for instance a
"basis" with `P = Q`, which is exactly the configuration that makes the inductive step
`closure_pair_eq_torsion_succ` fail at `k = 0`. -/
theorem ne_zero_and_ne_of_closure_pair_of_card {n : ℕ} [NeZero n]
    (hcard : Nat.card (W.torsion n) = n * n) (hn : 1 < n) {P Q : W.Point}
    (hgen : AddSubgroup.closure ({P, Q} : Set W.Point) = W.torsion n) :
    P ≠ 0 ∧ Q ≠ 0 ∧ P ≠ Q := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have hval1 : ((1 : ZMod n)).val = 1 := ZMod.val_one _
  have hval0 : ((0 : ZMod n)).val = 0 := ZMod.val_zero
  have hne10 : (1 : ZMod n) ≠ 0 := one_ne_zero
  refine ⟨fun h => hne10 ?_, fun h => hne10 ?_, fun h => hne10 ?_⟩
  · exact ((zmod_pair_eq_zero_iff_of_card hcard hgen (a := 1) (b := 0)).mp
      (by rw [hval1, hval0, h]; simp)).1
  · exact ((zmod_pair_eq_zero_iff_of_card hcard hgen (a := 0) (b := 1)).mp
      (by rw [hval1, hval0, h]; simp)).2
  · have himg : torsionPairHom hgen (1, 0) = torsionPairHom hgen (0, 1) := by
      refine Subtype.ext ?_
      rw [torsionPairHom_apply_coe, torsionPairHom_apply_coe, hval1, hval0, h]
      simp
    exact congrArg Prod.fst ((torsionPairHom_bijective_of_card hcard hgen).1 himg)

end WeierstrassCurve.Affine
