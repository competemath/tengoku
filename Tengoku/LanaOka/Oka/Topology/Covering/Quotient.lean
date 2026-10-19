/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
module

public import Tengoku.Seed.Topology.Algebra.ConstMulAction
public import Tengoku.Seed.Topology.Covering.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The quotient of a covering map by a finite group acting over the base

Material for `Mathlib/Topology/Covering/Quotient.lean`; see `README.md` on the mirror tree.
**That file exists at the pinned Mathlib revision**, so the mirror path names a target to add to
and not a proposed new one, and `scripts/import_cost.py` prices the two imports above at **0**
modules against that target's closure of **1033** — both are already in it. **That measurement is
what chose the path**: the same two imports cost **68** against
`Mathlib/Topology/Covering/Basic.lean`, whose closure of **812** does not contain
`Mathlib/Topology/Algebra/ConstMulAction.lean`, and a continuous group action cannot be spoken of
without it. Nothing declared in this repository occurs below, and every statement here would make
sense to a reader who had never heard of Oka's theorem.

Let `p : E → X` be a covering map with finite fibres and let a finite group `G` act on `E` by
homeomorphisms **over `X`**. Then the induced map on the orbit space is again a covering map with
finite fibres. **The action is not assumed free**, and there is no separation axiom and no
hypothesis of any kind on `X`.

## What Mathlib has under this path, and why it is not this

`Mathlib/Topology/Covering/Quotient.lean` is about the **other** map — the quotient map
`E → E ⧸ G` — and the structure it is built around asks the action to be **free**, the blocks that
do not use that structure asking proper discontinuity and concluding on the free locus instead.
`IsQuotientCoveringMap f G` has a `disjoint`
field saying that every point has a neighbourhood whose translates by the group elements are
pairwise disjoint, `IsQuotientCoveringMap.isCancelSMul` is that file reading the freeness back off
that field, and `IsQuotientCoveringMap.isCoveringMap` concludes that `f` itself is a covering map.
Those three are one block of that file and not its remainder, and its own title says how much
wider the subject is: *Covering maps to quotients by free and properly discontinuous group
actions*. At the `v4.32.0` this repository pins — `lake-manifest.json`, rev `81a5d257` — it carries
**34 source declarations**, in six blocks: **4** the structure and its additive twin and the two
lemmas translating between them; **5** general lemmas about `IsQuotientCoveringMap`, the
`isCancelSMul` above one of them; **11** the deck action on a fibre, of which
`IsQuotientCoveringMap.mulActionFiber_isPretransitive`,
`IsQuotientCoveringMap.toPermFiber_injective` and `IsQuotientCoveringMap.exists_toPermFiber_eq`
are three; **6** under `Topology.IsQuotientMap` on the properly discontinuous route, which the next
paragraph is about; **5** on a topological group by a discrete subgroup; and **3** conclusions, the
`isCoveringMap` above one of them.

**What rules all six blocks out is one reading and not six.** In every one of the 34 the group acts
on the **source** of the map under discussion and that map's fibres are its orbits, so the quotient
is the map's **target**. The map this file is about has the quotient as its **source**: `p` is
already a covering map, `G` acts on `E` over `X`, and what descends is `E ⧸ G → X`.
**Nothing below assumes freeness, and nothing below is about `E → E ⧸ G`.**

**The nearest statement of that file to the hypotheses here is still about the other map, and
asks two things not assumed here.** `isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul`
gives that `E → E ⧸ G` is a covering map **on the image of the free locus**
`{e | MulAction.stabilizer G e = ⊥}`, and a finite action does supply its
`ProperlyDiscontinuousSMul` hypothesis, by `Finite.to_properlyDiscontinuousSMul`. But it also asks
`[LocallyCompactSpace E]` and `[T2Space E]`, neither of which is available here, and its
conclusion is about the quotient map away from the fixed points rather than about the descent.

## The mathematics, which is one shrinking step and then bookkeeping

Over an evenly covered `U ∋ x` the total space is `U × I` with `I` the fibre, discrete and here
finite. An element `g` of `G` acts over `X`, so it carries `(v, i)` to `(v, τ g (v, i))` for a
map `τ g` into `I`, continuous and therefore **locally constant in `v`**, `I` being discrete.
Intersecting the neighbourhoods on which the finitely many functions `τ g (·, i)` are constant —
finitely many because `G` is finite and the fibre is finite, **and this is the only place either
finiteness is used** — gives a smaller `V ∋ x` on which the action is by a single permutation
`act g` of `I`. Then `p ⁻¹' V` is `V × I` equivariantly, the orbit space over `V` is
`V × (I / act)`, and `I / act` is finite and discrete.

`IsEvenlyCovered.exists_smul_parametrisation` is that shrinking step and
`IsEvenlyCovered.of_smul_parametrisation` is the descent it feeds; the second **uses no finiteness
of `G` and none of the fibre**, which is why the two are separate statements rather than one
proof.

## The descended map is a hypothesis and not a construction

Every statement about the orbit space below takes the descended map `q` as a variable together
with `∀ e, q (Quotient.mk _ e) = p e`, rather than building it. Any such `q` is `Quotient.lift p`
at the proof that `p` is constant on orbits, since `Quotient.mk _` is surjective, so nothing is
lost; what is gained is that no definition is introduced for a term `Quotient.lift` already
names, and that a caller who has a descended map in hand for another reason can use these
directly. **That `p` is constant on orbits is a consequence of that hypothesis and not a further
one**, and `IsCoveringMap.of_comp_quotientMk` derives it rather than asking for it.

## Main results

- `IsCoveringMap.of_comp_quotientMk`: **the descent of a covering map with finite fibres to the
  orbit space of a finite group acting continuously over the base is a covering map**.
- `MulAction.finite_fiber_of_comp_quotientMk`: its fibres are finite, for any group.
- `IsEvenlyCovered.exists_smul_parametrisation`: the shrinking step — an evenly covered point of
  a finite fibre has an evenly covered neighbourhood on which a finite group acting over the base
  permutes the sheets by a single permutation of the fibre.
- `IsEvenlyCovered.of_smul_parametrisation`: given such a neighbourhood, the orbit space is
  evenly covered there.

## What is not here

* **Nothing about the quotient map `E → E ⧸ G`**, which is the subject of the Mathlib file this
  one is material for. Whether it is a covering map is not decided here in either direction.
* **No freeness, and no `IsQuotientCoveringMap`.** That structure is not mentioned below and
  nothing here bears on it.
* **No topology is put on `G`.** It is an abstract group acting continuously by
  `ContinuousConstSMul`, which is a statement about each `g` separately.
* **Nothing about an infinite group.** `Finite G` is a hypothesis of the shrinking step and of
  the main result, and the module docstring says where it is used; nothing below says the
  conclusion fails without it.
* **Nothing about the orbit space as a topological space in its own right** — not that it is
  Hausdorff, not that it is locally compact, not that the quotient map is closed. Only the
  evenly-covered property of the descended map is proved.
* **Nothing about a fundamental group, a deck transformation group or a Galois correspondence.**
-/

@[expose] public section

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
variable {G : Type*} [Group G] [MulAction G E]

omit [TopologicalSpace E] [TopologicalSpace X] in
/-- **A descent of a map with finite fibres to an orbit space has finite fibres.** The fibre of
`q` over `x` is the image of the fibre of `p` under the quotient map, so no finiteness of the
group and no topology are used. -/
theorem MulAction.finite_fiber_of_comp_quotientMk
    {q : Quotient (MulAction.orbitRel G E) → X} (hq : ∀ e, q (Quotient.mk _ e) = p e)
    (hfin : ∀ x, (p ⁻¹' {x}).Finite) (x : X) : (q ⁻¹' {x}).Finite := by
  refine Set.Finite.subset ((hfin x).image (Quotient.mk (MulAction.orbitRel G E))) ?_
  intro c hc
  obtain ⟨e, rfl⟩ := Quotient.exists_rep c
  exact ⟨e, by rw [Set.mem_preimage, Set.mem_singleton_iff, ← hq]; exact hc, rfl⟩

variable [ContinuousConstSMul G E]

/-- **A finite group acting over the base permutes the sheets by a single permutation, after
shrinking the base.** If `x` is evenly covered by `p` with finite fibre `I` and a finite group `G`
acts continuously on the total space over `X`, then `x` has an open neighbourhood `V` and a
parametrisation `s : V × I → E` of `p ⁻¹' V` — an open embedding onto it, over `V` — together
with an action `act` of `G` on `I` for which `g • s (v, i) = s (v, act g i)`.

**Both finiteness hypotheses are spent in one place.** Each `g` carries `(v, i)` to
`(v, τ g (v, i))` with `τ g` continuous into the discrete `I`, hence locally constant in `v`;
`V` is the intersection over `g` and `i` of the neighbourhoods of `x` on which `τ g (·, i)` is
constant, and that intersection is open because there are finitely many of them.

`act` is returned with its two action laws rather than as a `MulAction` instance, so that a
caller may install whichever setoid or instance it needs; the laws are read off the equivariance
at `x` itself, which lies in `V`. -/
theorem IsEvenlyCovered.exists_smul_parametrisation [Finite G]
    {I : Type*} [TopologicalSpace I] [Finite I] {x : X}
    (hev : IsEvenlyCovered p x I) (hover : ∀ (g : G) (e : E), p (g • e) = p e) :
    ∃ (V : Set X) (act : G → I → I) (s : V × I → E),
      IsOpen V ∧ x ∈ V ∧ IsOpenEmbedding s ∧ Set.range s = p ⁻¹' V ∧
      (∀ z, p (s z) = (z.1 : X)) ∧ (∀ (g : G) (z : V × I), g • s z = s (z.1, act g z.2)) ∧
      act 1 = id ∧ ∀ g h : G, act (g * h) = act g ∘ act h := by
  obtain ⟨hI, U, hxU, hU, hpU, H, hH⟩ := hev
  haveI := hI
  -- the parametrisation of `p ⁻¹' U` that being evenly covered supplies
  set t : U × I → E := fun vi => (H.symm vi : E) with ht
  have hpt : ∀ vi, p (t vi) = (vi.1 : X) := by
    intro vi
    change p (H.symm vi : E) = _
    rw [← hH (H.symm vi), Homeomorph.apply_symm_apply]
  have hct : Continuous t := by fun_prop
  have hmem : ∀ (g : G) (vi : U × I), g • t vi ∈ p ⁻¹' U := by
    intro g vi; simp only [Set.mem_preimage, hover g, hpt]; exact vi.1.2
  -- the sheet an element of the group sends a sheet to, as a function of the base point
  set β : G → U × I → I := fun g vi => (H ⟨g • t vi, hmem g vi⟩).2 with hβ
  have hcβ : ∀ g, Continuous (β g) := fun g =>
    Continuous.snd (H.continuous.comp (Continuous.subtype_mk (by fun_prop) _))
  set x₀ : U := ⟨x, hxU⟩ with hx₀
  -- the base points at which every one of the finitely many `β g (·, i)` agrees with its value
  -- at `x`; open because there are finitely many and `I` is discrete
  set V₀ : Set U := {v | ∀ (g : G) (i : I), β g (v, i) = β g (x₀, i)} with hV₀def
  have hV₀open : IsOpen V₀ := by
    have : V₀ = ⋂ (g : G), ⋂ (i : I), (fun v => β g (v, i)) ⁻¹' {β g (x₀, i)} := by
      ext v; simp [hV₀def]
    rw [this]
    exact isOpen_iInter_of_finite fun g => isOpen_iInter_of_finite fun i =>
      ((hcβ g).comp (continuous_id.prodMk continuous_const)).isOpen_preimage _ (isOpen_discrete _)
  have hx₀V₀ : x₀ ∈ V₀ := fun g i => rfl
  have key : ∀ v ∈ V₀, ∀ (g : G) (i : I), g • t (v, i) = t (v, β g (x₀, i)) := by
    intro v hv g i
    have h1 : H ⟨g • t (v, i), hmem g (v, i)⟩ = (v, β g (v, i)) := by
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      rw [hH ⟨g • t (v, i), hmem g (v, i)⟩]
      simp only [hover g, hpt]
    have h2 : (⟨g • t (v, i), hmem g (v, i)⟩ : p ⁻¹' U) = H.symm (v, β g (v, i)) := by
      rw [← h1]; simp
    calc g • t (v, i) = (H.symm (v, β g (v, i)) : E) := congrArg Subtype.val h2
      _ = t (v, β g (x₀, i)) := by rw [hv g i]
  have hti : Function.Injective t := fun a b hab => H.symm.injective (Subtype.ext hab)
  have hto : IsOpenMap t := hpU.isOpenMap_subtype_val.comp H.symm.isOpenMap
  set V : Set X := Subtype.val '' V₀ with hVdef
  have hVU : V ⊆ U := by rintro v ⟨w, -, rfl⟩; exact w.2
  have hVopen : IsOpen V := hU.isOpenMap_subtype_val V₀ hV₀open
  have hxV : x ∈ V := ⟨x₀, hx₀V₀, rfl⟩
  set ι : V → U := Set.inclusion hVU with hιdef
  have hιV₀ : ∀ u : U, (u : X) ∈ V → u ∈ V₀ := by
    rintro u ⟨w, hw, hwu⟩
    have : u = w := Subtype.ext hwu.symm
    rw [this]; exact hw
  set act : G → I → I := fun g i => β g (x₀, i) with hactdef
  set s : V × I → E := fun z => t (ι z.1, z.2) with hsdef
  refine ⟨V, act, s, hVopen, hxV, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
    · exact hct.comp ((continuous_inclusion hVU).prodMap continuous_id)
    · exact hti.comp ((Set.inclusion_injective hVU).prodMap Function.injective_id)
    · exact hto.comp ((hVopen.isOpenMap_inclusion hVU).prodMap IsOpenMap.id)
  · ext e
    simp only [Set.mem_range, Set.mem_preimage]
    constructor
    · rintro ⟨z, rfl⟩
      change p (t (ι z.1, z.2)) ∈ V
      rw [hpt (ι z.1, z.2)]
      exact z.1.2
    · intro he
      have heU : e ∈ p ⁻¹' U := hVU he
      set z := H ⟨e, heU⟩ with hz
      have h1 : (z.1 : X) = p e := hH ⟨e, heU⟩
      refine ⟨(⟨p e, he⟩, z.2), ?_⟩
      have h2 : ι ⟨p e, he⟩ = z.1 := Subtype.ext h1.symm
      have h3 : t (z.1, z.2) = e := by
        change (H.symm (z.1, z.2) : E) = e
        rw [Prod.mk.eta, hz, Homeomorph.symm_apply_apply]
      rw [hsdef]
      simpa only [h2] using h3
  · intro z; rw [hsdef]; exact hpt _
  · intro g z
    have := key (ι z.1) (hιV₀ (ι z.1) z.1.2) g z.2
    simpa [hsdef, hactdef] using this
  · funext i
    have h0 : (⟨(1 : G) • t (x₀, i), hmem 1 (x₀, i)⟩ : p ⁻¹' U) = H.symm (x₀, i) :=
      Subtype.ext (by simp [ht])
    simp only [hactdef, hβ, h0, Homeomorph.apply_symm_apply, id_eq]
  · intro g h
    funext i
    have h1 := key x₀ hx₀V₀ (g * h) i
    have h2 := key x₀ hx₀V₀ h i
    have h3 := key x₀ hx₀V₀ g (β h (x₀, i))
    rw [mul_smul, h2, h3] at h1
    have := hti h1.symm
    simpa [hactdef] using congrArg Prod.snd this

/-- **A base point parametrised equivariantly is evenly covered in the orbit space.** Given a
descent `q` of `p` to the orbit space and a parametrisation `s : V × I → E` of `p ⁻¹' V` on which
`G` acts through a single permutation `act g` of the discrete fibre `I`, the point `x ∈ V` is
evenly covered by `q`.

The fibre is `I` modulo the relation `act` generates, which is discrete because `I` is; the
homeomorphism onto `V ×` that quotient is the parametrisation followed by the quotient map, which
is continuous, bijective and open because `Prod.map id (Quotient.mk _)` is an open quotient map.

**No finiteness is used here, of the group or of the fibre.** Both are spent in
`IsEvenlyCovered.exists_smul_parametrisation`, which is what produces the hypotheses below. -/
theorem IsEvenlyCovered.of_smul_parametrisation
    {I : Type*} [TopologicalSpace I] [DiscreteTopology I] {x : X} {V : Set X}
    {act : G → I → I} {s : ↥V × I → E} {q : Quotient (MulAction.orbitRel G E) → X}
    (hq : ∀ e, q (Quotient.mk _ e) = p e) (hcp : Continuous p) (hVopen : IsOpen V) (hxV : x ∈ V)
    (hs : IsOpenEmbedding s) (hrange : Set.range s = p ⁻¹' V) (hps : ∀ z, p (s z) = (z.1 : X))
    (hequiv : ∀ (g : G) (z : ↥V × I), g • s z = s (z.1, act g z.2))
    (hact1 : act 1 = id) (hactmul : ∀ g h : G, act (g * h) = act g ∘ act h) :
    IsEvenlyCovered q x ↥(q ⁻¹' {x}) := by
  set π : E → Quotient (MulAction.orbitRel G E) := Quotient.mk _ with hπdef
  have hπsmul : ∀ (g : G) (e : E), π (g • e) = π e := fun g e =>
    Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)
  have hcomp : q ∘ (Quotient.mk (MulAction.orbitRel G E)) = p := funext hq
  have hcq : Continuous q := by
    rw [← MulAction.isOpenQuotientMap_quotientMk.continuous_comp_iff, hcomp]; exact hcp
  have hπopen : IsOpenMap π := isOpenMap_quotient_mk'_mul
  -- the relation `act` generates on the fibre, and the quotient of the fibre by it
  letI sI : Setoid I :=
    { r := fun i j => ∃ g : G, act g i = j
      iseqv :=
        { refl := fun i => ⟨1, by rw [hact1]; rfl⟩
          symm := fun {i j} ⟨g, hg⟩ => ⟨g⁻¹, by
            rw [← hg, ← Function.comp_apply (f := act g⁻¹), ← hactmul, inv_mul_cancel, hact1]; rfl⟩
          trans := fun {i j k} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by
            rw [hactmul]; simp only [Function.comp_apply, hg, hh]⟩ } }
  haveI : DiscreteTopology (Quotient sI) :=
    discreteTopology_iff_forall_isOpen.2 fun _ => isOpen_coinduced.2 (isOpen_discrete _)
  have hmkopen : IsOpenMap (Quotient.mk sI) := fun _ _ => isOpen_coinduced.2 (isOpen_discrete _)
  have hqV : IsOpen (q ⁻¹' V) := hcq.isOpen_preimage _ hVopen
  have hmem : ∀ z : ↥V × I, π (s z) ∈ q ⁻¹' V := by
    intro z; simp only [Set.mem_preimage, hq, hps]; exact z.1.2
  set Φ' : ↥V × I → ↥(q ⁻¹' V) := Set.codRestrict (fun z => π (s z)) _ hmem with hΦ'def
  have hwd : ∀ (v : ↥V) (i j : I), i ≈ j → Φ' (v, i) = Φ' (v, j) := by
    rintro v i j ⟨g, rfl⟩
    apply Subtype.ext
    change π (s (v, i)) = π (s (v, act g i))
    rw [← hequiv g (v, i), hπsmul]
  set Φ : ↥V × Quotient sI → ↥(q ⁻¹' V) :=
    fun z => Quotient.liftOn z.2 (fun i => Φ' (z.1, i)) (hwd z.1) with hΦdef
  have hΦcomp : Φ ∘ Prod.map id (Quotient.mk sI) = Φ' := rfl
  have hquot : IsOpenQuotientMap (Prod.map (id : ↥V → ↥V) (Quotient.mk sI)) :=
    ⟨Function.surjective_id.prodMap Quotient.mk_surjective,
      continuous_id.prodMap continuous_quot_mk, IsOpenMap.id.prodMap hmkopen⟩
  have hΦcont : Continuous Φ := by
    rw [← hquot.continuous_comp_iff, hΦcomp]
    exact Continuous.codRestrict (continuous_quot_mk.comp hs.continuous) hmem
  have hΦopen : IsOpenMap Φ := by
    rw [hquot.isOpenMap_iff, hΦcomp]
    exact IsOpenMap.codRestrict (hπopen.comp hs.isOpenMap) hmem
  have hΦinj : Function.Injective Φ := by
    rintro ⟨v, j₁⟩ ⟨w, j₂⟩ h
    induction j₁ using Quotient.inductionOn with | _ i₁ => ?_
    induction j₂ using Quotient.inductionOn with | _ i₂ => ?_
    have h' : π (s (v, i₁)) = π (s (w, i₂)) := congrArg Subtype.val h
    have hvw : v = w := by
      apply Subtype.ext
      have := congrArg q h'
      rwa [hq, hq, hps, hps] at this
    subst hvw
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h')
    have hg' : g • s (v, i₂) = s (v, i₁) := hg
    rw [hequiv g (v, i₂)] at hg'
    have h2 : act g i₂ = i₁ := congrArg Prod.snd (hs.injective hg')
    exact Prod.ext rfl (Quotient.sound (show i₂ ≈ i₁ from ⟨g, h2⟩)).symm
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨c, hc⟩
    obtain ⟨e, rfl⟩ := Quotient.exists_rep c
    have heV : e ∈ Set.range s := by
      rw [hrange, Set.mem_preimage, ← hq]; exact hc
    obtain ⟨z, rfl⟩ := heV
    exact ⟨(z.1, Quotient.mk sI z.2), Subtype.ext rfl⟩
  set homeo : ↥V × Quotient sI ≃ₜ ↥(q ⁻¹' V) :=
    (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).toHomeomorphOfContinuousOpen hΦcont hΦopen with hhomeo
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    ⟨inferInstance, V, hxV, hVopen, hqV, homeo.symm, ?_⟩
  intro c
  obtain ⟨z, rfl⟩ := homeo.surjective c
  rw [Homeomorph.symm_apply_apply]
  obtain ⟨v, j⟩ := z
  induction j using Quotient.inductionOn with | _ i => ?_
  change (v : X) = q (Φ (v, Quotient.mk sI i))
  rw [show Φ (v, Quotient.mk sI i) = Φ' (v, i) from rfl]
  change (v : X) = q (π (s (v, i)))
  rw [hq, hps]

/-- **The descent of a covering map with finite fibres to the orbit space of a finite group
acting over the base is a covering map.** The action is not assumed free, and nothing is assumed
of `X`.

The hypothesis `hq` says that `q` is a descent of `p`, and it already forces `p` to be constant
on orbits, so no such hypothesis is asked for separately.

`MulAction.finite_fiber_of_comp_quotientMk` says the fibres of `q` are again finite, so the
conclusion can be fed back into this statement. -/
theorem IsCoveringMap.of_comp_quotientMk [Finite G]
    {q : Quotient (MulAction.orbitRel G E) → X} (hq : ∀ e, q (Quotient.mk _ e) = p e)
    (hp : IsCoveringMap p) (hfin : ∀ x, (p ⁻¹' {x}).Finite) : IsCoveringMap q := by
  have hover : ∀ (g : G) (e : E), p (g • e) = p e := fun g e => by
    rw [← hq, ← hq]; exact congrArg q (Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩))
  intro x
  haveI : Finite ↥(p ⁻¹' {x}) := (hfin x).to_subtype
  haveI : DiscreteTopology ↥(p ⁻¹' {x}) := (hp x).1
  obtain ⟨V, act, s, hVopen, hxV, hs, hrange, hps, hequiv, hact1, hactmul⟩ :=
    (hp x).exists_smul_parametrisation hover
  exact IsEvenlyCovered.of_smul_parametrisation hq hp.continuous hVopen hxV hs hrange hps hequiv
    hact1 hactmul
