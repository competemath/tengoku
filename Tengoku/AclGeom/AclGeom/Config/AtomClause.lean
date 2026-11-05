/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.MeetEquations
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal
import Tengoku.AclGeom.AclGeom.Correspondence.Binomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The atom clause: no rank-one parameter captures a generic line

Clause (iv) of Ψ at the soundness witness: for every atom `A' ≤ A`, the
generic point `X` is not below `A' ∨ Y` — concretely, for `t ∈ racl{u, v}`
transcendental, the generic direction `w` is not algebraic over
`{t, uw + v}`.

The blueprint proves this by the minimal-parameter derivation calculation;
this file follows the elementary *specialization route* instead (design
note on the project tracker): exchange converts the hypothesis into
`uw + v ∈ racl_{K₀}{w}` over the closed base `K₀ = racl{t}`; a nonzero
two-variable relation `G` over `K₀` then vanishes identically under the
substitution `X₁ ↦ uT + v` because `w` is transcendental over
`racl{u, v}`; specializing `T` at two distinct points `ξ₁ ≠ ξ₂` of
`racl{t}` where the `Y`-collapse of `G` stays nonzero puts `uξᵢ + v`
into `racl{t}`, and
differencing recovers `u` and `v` there — contradicting the independence
of the coefficients, since `t` is interalgebraic with a rank-one closure.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** clause (iv) proved over any base field; the blueprint
derivation argument remains a separate obligation (#6).
-/

namespace AclGeom

noncomputable section

open IntermediateField

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section LineClause

/-- Elements outside a relative algebraic closure are transcendental over
it as a base field.
@isnad1 id=transcen.1h4v.s7.09a164f58a4b from=translated src=- shape=3b214718 vocab=41cf68ae
-/
theorem transcendental_racl_of_notMem {S : Set K} {z : K}
    (h : z ∉ racl k S) : Transcendental ↥(racl k S) z := by
  intro halg
  exact h (IsRAC.mem_of_isAlgebraic (isRAC_racl S) halg)

variable {u v w t : K}

/-- Exchange reduction for the atom clause: if the generic direction `w`
were algebraic over the atom parameter and the line value, the line value
would be algebraic over `{w, t}`.
@isnad1 id=mem.3h6v.s8.8ef7785f19c5 from=translated src=- shape=19175ea6 vocab=d6e1dea8
-/
theorem line_mem_of_mem (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (hmem : w ∈ racl k ({t, u * w + v} : Set K)) :
    u * w + v ∈ racl k ({w, t} : Set K) := by
  have hwt : w ∉ racl k ({t} : Set K) := fun h ↦
    hw (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) h)
  have hmem' : w ∈ racl k (insert (u * w + v) ({t} : Set K)) := by
    rwa [Set.pair_comm t (u * w + v)] at hmem
  exact racl_exchange hmem' hwt

/-- The line value is algebraic over the direction alone, once the atom
closure is promoted to the base field.
@isnad1 id=mem.1h6v.s9.0036a9d9fcee from=translated src=- shape=88b3fe94 vocab=84d14abb
-/
theorem line_mem_over_base (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
  have h1 : u * w + v ∈ racl ↥(racl k ({t} : Set K)) ({w, t} : Set K) :=
    racl_subset_racl_base (racl k ({t} : Set K)) ({w, t} : Set K) h
  have ht' : t ∈ racl ↥(racl k ({t} : Set K)) ({w} : Set K) := by
    have hmem : algebraMap ↥(racl k ({t} : Set K)) K
        ⟨t, subset_racl k _ rfl⟩ ∈
        racl ↥(racl k ({t} : Set K)) ({w} : Set K) :=
      IntermediateField.algebraMap_mem _ _
    simpa using hmem
  have h2 : ({w, t} : Set K) = insert t ({w} : Set K) :=
    Set.pair_comm w t
  rw [h2, racl_insert_of_mem ht'] at h1
  exact h1

/-- A nonzero two-variable relation over the atom base: the vanishing
ideal of `(w, uw+v)` over `racl{t}` contains a nonzero polynomial.
@isnad1 id=ex.1h6v.s11.27a495e5e5d3 from=translated src=- shape=2f1d2157 vocab=ac6409ab
-/
theorem exists_line_relation (h : u * w + v ∈ racl k ({w, t} : Set K)) :
    ∃ G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K)), G ≠ 0 ∧
      MvPolynomial.aeval ![w, u * w + v] G = 0 := by
  have hbot : idealOf ↥(racl k ({t} : Set K)) ![w, u * w + v] ≠ ⊥ :=
    idealOf_ne_bot_of_mem_racl _ (line_mem_over_base h)
  obtain ⟨G, hGmem, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact ⟨G, hG0, (mem_idealOf_iff _).1 hGmem⟩

section Collapse

/-- The one-variable collapse of a line configuration, generically:
substitute `X₀ ↦ T`, `X₁ ↦ u'T + v'`, mapping coefficients along `f`.
Stated over plain commutative rings to keep the kernel work trivial.-/
private noncomputable def lineCollapse {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (u' v' : S) :
    MvPolynomial (Fin 2) R →+* Polynomial S :=
  MvPolynomial.eval₂Hom ((Polynomial.C : S →+* Polynomial S).comp f)
    ![Polynomial.X, Polynomial.C u' * Polynomial.X + Polynomial.C v']

/-- Evaluating the collapse at a point recovers the direct two-variable
evaluation.-/
private theorem lineCollapse_square {R S A : Type*} [CommSemiring R]
    [CommSemiring S] [CommSemiring A] (f : R →+* S) (g : S →+* A)
    (u' v' : S) (z : A) :
    (Polynomial.eval₂RingHom g z).comp (lineCollapse f u' v') =
      MvPolynomial.eval₂Hom (g.comp f) ![z, g u' * z + g v'] := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp [lineCollapse]
  · fin_cases i
    · simp [lineCollapse]
    · simp [lineCollapse]

variable {u v w t : K}

/-- **The substitution collapse**: a relation over `racl{t}` that vanishes
at `(w, uw+v)` with `w` transcendental over `racl{u, v}` vanishes at every
specialization `(z, uz+v)` with `z ∈ K` — because the one-variable
substitution sends it to the zero polynomial.
@isnad1 id=eq.3h8v.s11.e3e5c6712fdd from=translated src=- shape=862a3619 vocab=ac6409ab
-/
theorem line_relation_specialize
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))}
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) (z : K) :
    MvPolynomial.aeval ![z, u * z + v] G = 0 := by
  classical
  have hle : racl k ({t} : Set K) ≤ racl k ({u, v} : Set K) :=
    racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht)
  have hu : u ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  have hv : v ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
  set f : ↥(racl k ({t} : Set K)) →+* ↥(racl k ({u, v} : Set K)) :=
    (IntermediateField.inclusion hle).toRingHom with hf
  set g : ↥(racl k ({u, v} : Set K)) →+* K :=
    algebraMap ↥(racl k ({u, v} : Set K)) K with hg
  -- The composite coefficient map is the canonical embedding.
  have hgf : g.comp f = algebraMap ↥(racl k ({t} : Set K)) K := by
    refine RingHom.ext fun r ↦ ?_
    simp only [hf, hg, RingHom.comp_apply]
    exact IntermediateField.coe_inclusion hle r
  have hgu : g ⟨u, hu⟩ = u := rfl
  have hgv : g ⟨v, hv⟩ = v := rfl
  -- The square, instantiated and rewritten to `aeval` form.
  have hsq : ∀ z : K,
      Polynomial.eval₂RingHom g z (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) =
      MvPolynomial.aeval ![z, u * z + v] G := by
    intro z
    have h1 := DFunLike.congr_fun
      (lineCollapse_square f g ⟨u, hu⟩ ⟨v, hv⟩ z) G
    simp only [RingHom.comp_apply] at h1
    rw [h1, hgf, hgu, hgv]
    rfl
  -- The collapsed polynomial vanishes at the transcendental `w`.
  have hPw : Polynomial.aeval w (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) = 0 := by
    have h2 : Polynomial.aeval w (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) =
        Polynomial.eval₂RingHom g w
          (lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G) := rfl
    rw [h2, hsq w, hG]
  have htr : Transcendental ↥(racl k ({u, v} : Set K)) w :=
    transcendental_racl_of_notMem hw
  have hzero : lineCollapse f ⟨u, hu⟩ ⟨v, hv⟩ G = 0 :=
    transcendental_iff.1 htr _ hPw
  -- Specialize the identity at `z`.
  rw [← hsq z, hzero, map_zero]

end Collapse

section Specialize

/-- Evaluating the nested presentation at a constant outer value and then
a point recovers the direct two-variable evaluation. Generic, to keep the
kernel work trivial.-/
private theorem nestEval_square {R A : Type*} [Field R] [CommRing A]
    (g : R →+* A) (c : R) (y : A) :
    (Polynomial.eval₂RingHom g y).comp
      ((Polynomial.evalRingHom (Polynomial.C c)).comp
        (nestEquiv R).toAlgHom.toRingHom) =
    MvPolynomial.eval₂Hom g ![g c, y] := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · have hC : (nestEquiv R).toAlgHom.toRingHom (MvPolynomial.C r) =
        Polynomial.C (Polynomial.C r) := nestEquiv_C r
    simp only [RingHom.comp_apply, hC, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      MvPolynomial.eval₂Hom_C]
  · fin_cases i
    · have hX : (nestEquiv R).toAlgHom.toRingHom
          (MvPolynomial.X ⟨0, by omega⟩) = Polynomial.X :=
        nestEquiv_X_zero (K := R)
      simp only [RingHom.comp_apply, hX, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, MvPolynomial.eval₂Hom_X']
      rfl
    · have hX : (nestEquiv R).toAlgHom.toRingHom
          (MvPolynomial.X ⟨1, by omega⟩) = Polynomial.C Polynomial.X :=
        nestEquiv_X_one (K := R)
      simp only [RingHom.comp_apply, hX, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, MvPolynomial.eval₂Hom_X']
      rfl

/-- A nonzero nested polynomial vanishes at only finitely many constant
outer values.-/
private theorem finite_bad_eval {R : Type*} [Field R]
    {P : Polynomial (Polynomial R)} (hP : P ≠ 0) :
    {c : R | Polynomial.eval (Polynomial.C c) P = 0}.Finite := by
  have hroots : {q : Polynomial R | Polynomial.IsRoot P q}.Finite :=
    Polynomial.finite_setOfPred_isRoot hP
  have hsub : {c : R | Polynomial.eval (Polynomial.C c) P = 0} ⊆
      Polynomial.C ⁻¹' {q : Polynomial R | Polynomial.IsRoot P q} :=
    fun c hc ↦ hc
  exact (hroots.preimage (Set.injOn_of_injective Polynomial.C_injective)).subset
    hsub

variable {u v w t : K}

/-- At a specialization point `ξ` of the atom closure where the
`Y`-collapse stays nonzero, the line value is algebraic over the atom
closure.
@isnad1 id=mem.4h8v.s13.fea36385e317 from=translated src=- shape=cb07cf7b vocab=52719500
-/
theorem line_value_mem
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))}
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) {ξ : ↥(racl k ({t} : Set K))}
    (hQ : Polynomial.eval (Polynomial.C ξ) (nestEquiv ↥(racl k ({t} : Set K)) G) ≠ 0) :
    u * (ξ : K) + v ∈ racl k ({t} : Set K) := by
  have hspec := line_relation_specialize hw ht hG (ξ : K)
  have hsq := DFunLike.congr_fun (nestEval_square
    (algebraMap ↥(racl k ({t} : Set K)) K) ξ (u * (ξ : K) + v)) G
  simp only [RingHom.comp_apply] at hsq
  have hzero : Polynomial.eval₂RingHom
      (algebraMap ↥(racl k ({t} : Set K)) K)
      (u * (ξ : K) + v)
      (Polynomial.eval (Polynomial.C ξ) (nestEquiv ↥(racl k ({t} : Set K)) G)) = 0 := by
    have h1 : Polynomial.eval₂RingHom
        (algebraMap ↥(racl k ({t} : Set K)) K)
        (u * (ξ : K) + v)
        (Polynomial.eval (Polynomial.C ξ) (nestEquiv ↥(racl k ({t} : Set K)) G)) =
        MvPolynomial.eval₂Hom
          (algebraMap ↥(racl k ({t} : Set K)) K)
          ![(ξ : K), u * (ξ : K) + v] G := hsq
    have h3 : MvPolynomial.eval₂Hom
        (algebraMap ↥(racl k ({t} : Set K)) K)
        ![(ξ : K), u * (ξ : K) + v] G =
        MvPolynomial.aeval ![(ξ : K), u * (ξ : K) + v] G := rfl
    rw [h1, h3, hspec]
  have halg : IsAlgebraic ↥(racl k ({t} : Set K)) (u * (ξ : K) + v) := ⟨_, hQ, hzero⟩
  exact IsRAC.mem_of_isAlgebraic (isRAC_racl _) halg

/-- The relative closure of a transcendental element is an infinite field.
@isnad1 id=infinite.1h3v.s6.a0b7217fc62e from=translated src=- shape=4b962bbb vocab=b2dc5b9b
-/
theorem infinite_racl_singleton (ht0 : t ∉ racl k (∅ : Set K)) :
    Infinite ↥(racl k ({t} : Set K)) := by
  have htr : Transcendental k t := fun h ↦ ht0 (mem_racl_empty_of_isAlgebraic h)
  set τ : ↥(racl k ({t} : Set K)) := ⟨t, subset_racl k _ rfl⟩
  refine Infinite.of_injective (fun p : Polynomial k ↦ Polynomial.aeval τ p) ?_
  intro p p' h
  apply transcendental_iff_injective.1 htr
  have h' := congrArg (fun x : ↥(racl k ({t} : Set K)) ↦ (x : K)) h
  change Polynomial.aeval (τ : K) p = Polynomial.aeval (τ : K) p'
  rw [IntermediateField.aeval_coe, IntermediateField.aeval_coe]
  exact h'

/-- Two distinct specializations with algebraic line values exist: the
collapse is nonzero at all but finitely many points of the atom closure,
which is an infinite field because it contains the transcendental `t`.
No hypothesis on the size of the base field is needed.
@isnad1 id=ex.5h7v.s11.ffa474a6a5d5 from=translated src=- shape=c03e015b vocab=29a3ea85
-/
theorem exists_two_specializations
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K)) (ht0 : t ∉ racl k (∅ : Set K))
    {G : MvPolynomial (Fin 2) ↥(racl k ({t} : Set K))} (hG0 : G ≠ 0)
    (hG : MvPolynomial.aeval ![w, u * w + v] G = 0) :
    ∃ ξ₁ ξ₂ : ↥(racl k ({t} : Set K)), ξ₁ ≠ ξ₂ ∧
      u * (ξ₁ : K) + v ∈ racl k ({t} : Set K) ∧
      u * (ξ₂ : K) + v ∈ racl k ({t} : Set K) := by
  classical
  have := infinite_racl_singleton ht0
  have hĜ0 : nestEquiv ↥(racl k ({t} : Set K)) G ≠ 0 := by
    intro h0
    exact hG0 ((nestEquiv _).injective (by rw [h0, map_zero]))
  have hgood : {ξ : ↥(racl k ({t} : Set K)) | Polynomial.eval (Polynomial.C ξ)
      (nestEquiv ↥(racl k ({t} : Set K)) G) = 0}ᶜ.Infinite :=
    Set.Finite.infinite_compl (finite_bad_eval hĜ0)
  obtain ⟨ξ₁, hξ₁, ξ₂, hξ₂, hne⟩ := hgood.nontrivial
  exact ⟨ξ₁, ξ₂, hne, line_value_mem hw ht hG hξ₁, line_value_mem hw ht hG hξ₂⟩

/-- **The atom clause, elementwise** (blueprint clause (iv), by the
specialization route): no transcendental parameter `t` algebraic over the
independent line coefficients `u, v` can make the generic direction `w`
algebraic over `{t, uw + v}`.
@isnad1 id=not.5h6v.s8.482c10bbd63f from=translated src=- shape=e824e68e vocab=3ebaf705
-/
theorem notMem_racl_line
    (hu0 : u ∉ racl k (∅ : Set K))
    (hvu : v ∉ racl k ({u} : Set K))
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (ht0 : t ∉ racl k (∅ : Set K)) :
    w ∉ racl k ({t, u * w + v} : Set K) := by
  intro hmem
  obtain ⟨G, hG0, hG⟩ := exists_line_relation (line_mem_of_mem hw ht hmem)
  obtain ⟨ξ₁, ξ₂, hne, h1, h2⟩ := exists_two_specializations hw ht ht0 hG0 hG
  -- Differencing the two values recovers `u`.
  have hξ : ((ξ₁ : K) - ξ₂) ∈ racl k ({t} : Set K) := sub_mem ξ₁.2 ξ₂.2
  have hξ0 : ((ξ₁ : K) - ξ₂) ≠ 0 := sub_ne_zero.2 (fun h ↦ hne (Subtype.ext h))
  have hu : u ∈ racl k ({t} : Set K) := by
    have hsub := sub_mem h1 h2
    rw [show u * (ξ₁ : K) + v - (u * (ξ₂ : K) + v) = u * ((ξ₁ : K) - ξ₂) by ring] at hsub
    have h := mul_mem hsub (inv_mem hξ)
    rwa [mul_assoc, mul_inv_cancel₀ hξ0, mul_one] at h
  -- Then the constant term recovers `v`.
  have hv : v ∈ racl k ({t} : Set K) := by
    have h := sub_mem h1 (mul_mem hu ξ₁.2)
    rwa [add_sub_cancel_left] at h
  -- Exchange the transcendental `u` against `t`.
  have hu' : u ∈ racl k (insert t (∅ : Set K)) := by
    simpa using hu
  have ht' := racl_exchange hu' hu0
  have ht'' : t ∈ racl k ({u} : Set K) := by
    simpa using ht'
  exact hvu (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht'') hv)

end Specialize

section Instances

variable {u v w t : K}

/-- The value form of the atom clause: the line value is not algebraic
over the parameter and the direction. One more exchange reduces it to
`notMem_racl_line`.
@isnad1 id=not.5h6v.s8.c65c8d932de5 from=translated src=- shape=f3ca43c0 vocab=3ebaf705
-/
theorem line_value_notMem
    (hu0 : u ∉ racl k (∅ : Set K))
    (hvu : v ∉ racl k ({u} : Set K))
    (hw : w ∉ racl k ({u, v} : Set K))
    (ht : t ∈ racl k ({u, v} : Set K))
    (ht0 : t ∉ racl k (∅ : Set K)) :
    u * w + v ∉ racl k ({t, w} : Set K) := by
  intro hmem
  have hune : u ≠ 0 := by
    intro h0
    rw [h0] at hu0
    exact hu0 (zero_mem _)
  have hval : u * w + v ∉ racl k ({t} : Set K) := by
    intro h
    have h2 : u * w + v ∈ racl k ({u, v} : Set K) :=
      racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) h
    have hu : u ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
    have hv : v ∈ racl k ({u, v} : Set K) := subset_racl k _ (by simp)
    have h3 := MulMemClass.mul_mem (inv_mem hu) (sub_mem h2 hv)
    rw [add_sub_cancel_right, inv_mul_cancel_left₀ hune] at h3
    exact hw h3
  have hmem' : u * w + v ∈ racl k (insert w ({t} : Set K)) := by
    rwa [Set.pair_comm t w] at hmem
  have h := racl_exchange hmem' hval
  have h' : w ∈ racl k ({t, u * w + v} : Set K) := by
    rwa [Set.pair_comm (u * w + v) t] at h
  exact notMem_racl_line hu0 hvu hw ht ht0 h'

end Instances

section QTable

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

include hind

/--
@isnad1 id=not.1h7v.s7.d956a80f2950 from=translated src=- shape=3160d180 vocab=f4889937
-/
theorem qtable_a_notMem_empty : a ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 0
    (isAlgebraic_of_mem_racl_empty h)

/--
@isnad1 id=not.1h7v.s7.933c0d93d323 from=translated src=- shape=343602b5 vocab=f4889937
-/
theorem qtable_c_notMem_empty : c ∉ racl k (∅ : Set K) := fun h ↦
  AlgebraicIndependent.transcendental hind 2
    (isAlgebraic_of_mem_racl_empty h)

/--
@isnad1 id=not.1h7v.s7.2107089c327e from=translated src=- shape=57474357 vocab=e2c4dba1
-/
theorem qtable_ac_notMem_empty : a * c ∉ racl k (∅ : Set K) := by
  intro h
  exact qtable_mul_ac_notMem_bot hind
    (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))

/--
@isnad1 id=not.1h7v.s7.5a8d7acb879f from=translated src=- shape=930eba77 vocab=4789c72c
-/
theorem qtable_d_notMem_c : d ∉ racl k ({c} : Set K) := by
  have h : AlgebraicIndependent k ![c, d] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 2) (j := 3) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair h

/-- `bc + d ∉ racl{ac}`: the closure of `ac` lies in `racl{a, c}`, and
membership there would recover `d` over `{a, b, c}`.
@isnad1 id=not.1h7v.s7.9ed5e3b63a8c from=translated src=- shape=9e98fad5 vocab=5c9d6583
-/
theorem qtable_bcd_notMem_ac : b * c + d ∉ racl k ({a * c} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c} : Set K) ≤ racl k ({a, b, c} : Set K) := by
    refine racl_le_of_subset_racl (Set.singleton_subset_iff.2 ?_)
    have ha : a ∈ racl k ({a, b, c} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, b, c} : Set K) := subset_racl k _ (by simp)
    exact MulMemClass.mul_mem ha hc
  have h2 := hsub hmem
  have hb : b ∈ racl k ({a, b, c} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, b, c} : Set K) := subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c} : Set K) := by
    have h3 := sub_mem h2 (MulMemClass.mul_mem hb hc)
    rwa [add_sub_cancel_left] at h3
  exact qtable_d_notMem_abc hind hd

/--
@isnad1 id=not.1h7v.s7.216e32d05fe6 from=translated src=- shape=fc0cb271 vocab=86440252
-/
theorem qtable_Y_notMem_cd : a * x + b ∉ racl k ({c, d} : Set K) := by
  intro hmem
  have hsub : racl k ({c, d} : Set K) ≤ racl k ({a, b, c, d} : Set K) := by
    refine racl_le_of_subset_racl ?_
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨subset_racl k _ (by simp), subset_racl k _ (by simp)⟩
  exact qtable_Y_notMem_abcd hind (hsub hmem)

/--
@isnad1 id=not.1h7v.s7.e7c89461c229 from=translated src=- shape=4bd8eb3f vocab=86440252
-/
theorem qtable_x_notMem_ac_bcd :
    x ∉ racl k ({a * c, b * c + d} : Set K) := by
  intro hmem
  have hsub : racl k ({a * c, b * c + d} : Set K) ≤
      racl k ({a, b, c, d} : Set K) := by
    refine racl_le_of_subset_racl ?_
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    have ha : a ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
    have hb : b ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
    have hc : c ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
    have hd : d ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
    exact ⟨MulMemClass.mul_mem ha hc,
      add_mem (MulMemClass.mul_mem hb hc) hd⟩
  exact qtable_x_notMem_abcd hind (hsub hmem)

omit hind in
/-- A point below a join of two principal closures has its representative
algebraic over the two generators.
@isnad1 id=mem.1h5v.s7.0b7bc031b03d from=translated src=- shape=886173af vocab=058fa960
-/
theorem point_rep_mem_of_le {p q : K} {P : Point k K}
    (h : P.1 ≤ ClosedIF.point k p ⊔ ClosedIF.point k q) :
    P.rep ∈ racl k ({p, q} : Set K) := by
  have h1 : ClosedIF.point k P.rep ≤
      ClosedIF.point k p ⊔ ClosedIF.point k q := by
    rw [Point.point_rep]
    exact h
  have h2 := ClosedIF.point_le_iff.1 h1
  rwa [ClosedIF.mem_sup_point_iff] at h2

omit hind in
/-- Point representatives are never algebraic over the base.
@isnad1 id=not.0h3v.s6.3c79db04e973 from=translated src=- shape=02ee2280 vocab=6d0a0397
-/
theorem point_rep_notMem_empty (P : Point k K) :
    P.rep ∉ racl k (∅ : Set K) := fun h ↦
  P.rep_notMem_bot (ClosedIF.mem_bot_iff.2 (isAlgebraic_of_mem_racl_empty h))

omit hind in
/-- Convert a lattice incidence into a membership over the representative
and a second generator.
@isnad1 id=mem.1h5v.s7.708b964cf150 from=translated src=- shape=6c039696 vocab=058fa960
-/
theorem mem_of_le_point_sup {z q : K} {P : Point k K}
    (h : ClosedIF.point k z ≤ P.1 ⊔ ClosedIF.point k q) :
    z ∈ racl k ({P.rep, q} : Set K) := by
  have h1 : ClosedIF.point k z ≤
      ClosedIF.point k P.rep ⊔ ClosedIF.point k q := by
    rwa [Point.point_rep]
  have h2 := ClosedIF.point_le_iff.1 h1
  rwa [ClosedIF.mem_sup_point_iff] at h2

/-- Clause (iv), first universal statement: no atom of `A` captures the
correspondence from `Y` to `X`.
@isnad1 id=not.2h8v.s9.45e59a685f74 from=translated src=- shape=da9635ae vocab=c8fb5628
-/
theorem qWitness_X_free :
    ∀ A' : Point k K, A'.1 ≤ (qWitness hind).A →
      ¬ (qWitness hind).X.1 ≤ A'.1 ⊔ (qWitness hind).Y.1 := by
  intro A' hA' hle
  have ht : A'.rep ∈ racl k ({a, b} : Set K) := point_rep_mem_of_le hA'
  have hx : x ∈ racl k ({A'.rep, a * x + b} : Set K) :=
    mem_of_le_point_sup hle
  exact notMem_racl_line (qtable_a_notMem_empty hind)
    (qtable_b_notMem_a hind) (qtable_x_notMem_ab hind) ht
    (point_rep_notMem_empty A') hx

/-- Clause (iv), second universal statement: no atom of `B` captures the
correspondence from `Y` to `Z`.
@isnad1 id=not.2h8v.s9.3f2085a67dbc from=translated src=- shape=da9635ae vocab=3efff11f
-/
theorem qWitness_Z_freeB :
    ∀ B' : Point k K, B'.1 ≤ (qWitness hind).B →
      ¬ (qWitness hind).Z.1 ≤ B'.1 ⊔ (qWitness hind).Y.1 := by
  intro B' hB' hle
  have ht : B'.rep ∈ racl k ({c, d} : Set K) := point_rep_mem_of_le hB'
  have hz : c * (a * x + b) + d ∈
      racl k ({B'.rep, a * x + b} : Set K) := mem_of_le_point_sup hle
  exact line_value_notMem (qtable_c_notMem_empty hind)
    (qtable_d_notMem_c hind) (qtable_Y_notMem_cd hind) ht
    (point_rep_notMem_empty B') hz

/-- Clause (iv), third universal statement: no atom of `C` captures the
correspondence from `X` to `Z`.
@isnad1 id=not.2h8v.s9.b15fe6496244 from=translated src=- shape=da9635ae vocab=b3312d58
-/
theorem qWitness_Z_freeC :
    ∀ C' : Point k K, C'.1 ≤ (qWitness hind).C →
      ¬ (qWitness hind).Z.1 ≤ C'.1 ⊔ (qWitness hind).X.1 := by
  intro C' hC' hle
  have ht : C'.rep ∈ racl k ({a * c, b * c + d} : Set K) :=
    point_rep_mem_of_le hC'
  have hz : c * (a * x + b) + d ∈
      racl k ({C'.rep, x} : Set K) := mem_of_le_point_sup hle
  have harith : c * (a * x + b) + d = a * c * x + (b * c + d) := by
    ring
  rw [harith] at hz
  exact line_value_notMem (qtable_ac_notMem_empty hind)
    (qtable_bcd_notMem_ac hind) (qtable_x_notMem_ac_bcd hind) ht
    (point_rep_notMem_empty C') hz

end QTable

end LineClause

end

end AclGeom
