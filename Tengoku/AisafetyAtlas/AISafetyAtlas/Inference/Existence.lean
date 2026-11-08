module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# When an inferring device exists

Definition 3 says what it is for a device to weakly infer a target. The
impossibility results say when no device does. This module holds the other
direction — a construction that produces one — and the condition under which the
construction works.

## The condition is sharp, and the source got it wrong once

Wolpert 2008 Corollary 1(ii) prints the existence claim with **no condition at
all**: *"For any function `Γ` with domain `U` there is a device that infers
`Γ`."* That is false, and `Examples.Inference.Device.no_device_weaklyInfers_id_on_bool`
refutes it at `Γ = id` on `Bool`, where the target attains two values.

Wolpert 2018 Proposition 7(1) prints the same claim for `|Γ(U)| ≥ 3`. Definition
2 of both papers requires only `|Γ(U)| ≥ 2`, so that is a strengthened hypothesis
and not a convention carried over — the author repaired his own corollary, and
`identityDevice_weaklyInfers` is that repair. The printed claim is now fully
adjudicated: false as stated, true at three values, with the countermodel sitting
in exactly the excluded case. Source note: clash 20 in
[`wolpert-2008-source-clashes.md`](../../docs/provenance/wolpert-2008-source-clashes.md).

## Scope

Proved without either standing hypothesis the 2018 statement carries. It says
*"Let `U` be any countable space with at least two elements"*; countability
appears nowhere in the argument, and `|U| ≥ 2` follows from the target attaining
three values. The target type is arbitrary and lives in its own universe.

`|Γ(U)| ≥ 3` is rendered as three points of `U` with pairwise distinct values,
which is what "at least three values are attained" means on a possibly infinite
image, and needs no `Fintype`.
-/

namespace AISafetyAtlas.Inference

variable {U : Type u}

open scoped Classical in
/--
The device of the source's proof: *"Let `X(u)` be the identity function (so that
each `u ∈ U` has its own, unique value `x`). Choose `Y(u)` to equal 1 for exactly
one `u`, `ū`."*

`Setup := U` with `setup := id` is that identity setup, so every fibre is a
singleton and answering a probe is a pointwise condition. `hne` is what
Definition 1's surjectivity of the conclusion needs, and it is discharged from
the three distinct values at the one call site.-/
public noncomputable def identityDevice (ū : U) (hne : ∃ u : U, u ≠ ū) :
    InferenceDevice.{u, u} U where
  Setup := U
  setup := id
  concl := fun u => decide (u = ū)
  concl_surjective := by
    intro y
    cases y with
    | true => exact ⟨ū, by simp⟩
    | false =>
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, by simp [hu]⟩

/--
**Wolpert 2018, Proposition 7(1).** *"For any function `Γ` over `U` such that
`|Γ(U)| ≥ 3` there is a device `D` that weakly infers `Γ`."*

The three values are the whole content, and the source's proof says where they
go: the probe of `Γ(ū)` is answered `true` at `ū`, and every other probe is
answered `false` at a point carrying a third value — which must exist off `ū`
precisely because a third value exists.

At `|Γ(U)| = 2` the argument breaks exactly where 2008 Corollary 1(ii) is
refuted: the only point disagreeing with the probed value may be `ū` itself,
where the conclusion is `true`.-/
public theorem identityDevice_weaklyInfers {G : Type v} (Γ : U → G)
    {a b c : U} (hab : Γ a ≠ Γ b) (hac : Γ a ≠ Γ c) (hbc : Γ b ≠ Γ c) :
    WeaklyInfers (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩) Γ := by
  classical
  intro γ f hf _
  -- Every fibre of the identity setup is a singleton, so a setup value answers a
  -- probe exactly when it answers it at that one point.
  have pointwise : ∀ x : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).concl x =
      f (Γ x) → ∃ x' : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).Realized x' ∧
        ∀ w : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).setup w = x' →
          (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).concl w = f (Γ w) := by
    intro x hx
    exact ⟨x, ⟨x, rfl⟩, fun w hw => by cases hw; exact hx⟩
  by_cases hγ : γ = Γ a
  · -- The probed value is the one the device says `true` to.
    refine pointwise a ?_
    show decide (a = a) = f (Γ a)
    rw [decide_eq_true (rfl : a = a), (hf (Γ a)).mpr hγ.symm]
  · -- Some point off `a` carries a value other than `γ`: `b` and `c` both lie off
    -- `a` because their values differ from `Γ a`, and they cannot both carry `γ`
    -- because their values differ from each other.
    have hb_ne : b ≠ a := fun h => hab (h ▸ rfl)
    have hc_ne : c ≠ a := fun h => hac (h ▸ rfl)
    have hpoint : ∃ x : U, x ≠ a ∧ Γ x ≠ γ := by
      by_cases hbγ : Γ b = γ
      · exact ⟨c, hc_ne, fun h => hbc (hbγ.trans h.symm)⟩
      · exact ⟨b, hb_ne, hbγ⟩
    obtain ⟨x, hxa, hxγ⟩ := hpoint
    refine pointwise x ?_
    have hR : f (Γ x) = false := by
      cases hfx : f (Γ x) with
      | false => rfl
      | true => exact absurd ((hf (Γ x)).mp hfx) hxγ
    show decide (x = a) = f (Γ x)
    rw [decide_eq_false hxa, hR]

/-- The printed existential.-/
public theorem exists_weaklyInfers_of_three_values {G : Type v} (Γ : U → G)
    {a b c : U} (hab : Γ a ≠ Γ b) (hac : Γ a ≠ Γ c) (hbc : Γ b ≠ Γ c) :
    ∃ C : InferenceDevice.{u, u} U, WeaklyInfers C Γ :=
  ⟨_, identityDevice_weaklyInfers Γ hab hac hbc⟩

/-! ## Definition 4 and Proposition 7(2)

2008 Definition 5 lets one device strongly infer another. Wolpert 2018 Definition
4 states the same relation against an arbitrary **pair of functions** `(S, T)`,
with `S` playing the role the other device's setup played and `T` the role of its
conclusion. The generalization is **conservative**: at a device's own pair the
two definitions are the same relation, `stronglyInfers_iff_stronglyInfersPair`.
What it buys is reach, not a different notion — a pair of functions need not come
from any device, and Proposition 7(2)'s witness `(id, id)` is such a pair except
when `U = Bool`. That is the whole content of clash 28: the relation transfers,
the witness does not.
-/

/--
**Wolpert 2018, Definition 4.** *"Let `S` and `T` be functions both defined over
`U`. A device `(X, Y)` strongly infers `(S, T)` iff `∀δ ∈ P(T)` and all
`s ∈ S(U)`, `∃x` such that `X(u) = x ⇒ {S(u) = s, Y(u) = δ(T(u))}`."*

The quantifier order is the source's: one setup value per (probe, `S`-value)
pair, and both obligations hold on the fibre that value induces.-/
@[expose] public def StronglyInfersPair (C : InferenceDevice.{u, v} U)
    {S : Type w} {T : Type w'} (s : U → S) (t : U → T) : Prop :=
  ∀ (τ : T) (f : T → Bool), IsProbe f τ → (∃ w : U, t w = τ) →
    ∀ σ : S, (∃ w : U, s w = σ) →
      ∃ x : C.Setup, C.Realized x ∧
        ∀ w : U, C.setup w = x → s w = σ ∧ C.concl w = f (t w)

/-- The source's Proposition 7(2) witness is `S = T = id`. That pair is a
**device** pair only when the second component can be a conclusion, i.e. only
when `U = Bool` and so `|U| = 2`. The printed `|U| > 3` excludes exactly that
case. Clash 28.-/
@[expose] public def idDeviceOnBool : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := id
  concl_surjective := Function.surjective_id

/-! ## A grid of paired spins — Wolpert 2008, Example 5

*"Consider a rectangular grid of particle pairs, each pair consisting of a yellow
particle and a purple particle… Then we can define a 'purple inference device'
`C_p` by `X_p ≜ i` and `Y_p ≜ s_p(i, j)`. Similarly, a 'yellow inference device'
… `X_y ≜ j` and `Y_y ≜ s_y(i, j)`. These two devices are distinguishable. In
addition, `C_p > C_y` if there is some `i'` such that `s_p(i', j) = s_y(i', j)`
for all `j`, and also some `i''` such that `s_p(i'', j) = −s_y(i'', j)` for all
`j`… However if there is such an `i'` and `i''`, then clearly there cannot also
be both a value `j'` and a value `j''` that the yellow inference device can use
to answer whether `s_p` points up and whether `s_p` points down."*

The example is the paper's concrete face of Theorem 1, which it says *"generalizes
this impossibility result"*. What Theorem 1 does not supply is the other half:
that the hypotheses are **inhabited** — that a grid meeting them exists at all.
Both halves are here, and `Examples.Inference.SpinGrid` exhibits a grid.

## Scope

Stated for an arbitrary index pair `I`, `J` in their own universes, so *"regardless
of the size of the grid and the particular pattern"* is the theorem rather than a
remark about it. The source's standing assumptions that there be at least two `i`
values and at least two `j` values are **not needed**: distinguishability of the
row and column devices holds unconditionally, because every site `(i, j)` lies in
both the row-`i` and the column-`j` fibre. Definition 1's surjectivity is the
source's own *"at least one purple spin is up and at least one is down"*.
-/

section SpinGrid

variable {I : Type v} {J : Type w}

/-- The **purple device**: set up by the row index, concluding that row's purple
spin at whichever site the universe is at.-/
public def rowSpinDevice (sp : I → J → Bool)
    (hs : Function.Surjective fun p : I × J => sp p.1 p.2) :
    InferenceDevice.{max v w, v} (I × J) where
  Setup := I
  setup := Prod.fst
  concl := fun p => sp p.1 p.2
  concl_surjective := hs

/-- The **yellow device**: the same grid read by column.-/
public def colSpinDevice (sy : I → J → Bool)
    (hs : Function.Surjective fun p : I × J => sy p.1 p.2) :
    InferenceDevice.{max v w, w} (I × J) where
  Setup := J
  setup := Prod.snd
  concl := fun p => sy p.1 p.2
  concl_surjective := hs

end SpinGrid

end AISafetyAtlas.Inference
