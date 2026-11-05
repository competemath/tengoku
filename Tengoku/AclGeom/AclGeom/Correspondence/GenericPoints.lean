/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.FunctionField
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.RingTheory.AlgebraicIndependent.Adjoin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relocation of generic points

The embedding form of blueprint Lemma `generic-extension` (8.1(b)): inside an
algebraically closed ambient field, a finitely generated subextension can be
re-embedded over `k` with prescribed images for a transcendence basis. This
provides *independent generic points of a locus* — the engine of the
stabilizer argument in the curve-coset lemma — without any tensor-product
regularity.

* `adjoinTranscendentalAlgHom`: a purely transcendental subextension `k(t)`
  maps over `k` into the ambient field with prescribed algebraically
  independent images for `t`;
* `exists_extension_of_isAlgebraic`: a `k`-embedding of `E` into an
  algebraically closed ambient extends along any algebraic extension
  `E ≤ E'`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C2).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section Relocate

variable {ι : Type*} {t s : ι → Ω}

/-- Relocation of a purely transcendental subextension: the `k`-embedding of
`adjoin k (range t)` into `Ω` sending each `t i` to `s i`, for any two
algebraically independent families (blueprint Lemma 8.1(b), transcendental
part).-/
def adjoinTranscendentalAlgHom (ht : AlgebraicIndependent k t)
    (hs : AlgebraicIndependent k s) :
    ↥(adjoin k (Set.range t)) →ₐ[k] Ω :=
  ((adjoin k (Set.range s)).val.comp hs.aevalEquivField.toAlgHom).comp
    ht.aevalEquivField.symm.toAlgHom

/--
@isnad1 id=eq.2h6v.s9.d08da475f8de from=translated src=- shape=0974817c vocab=d2217d8b
-/
theorem adjoinTranscendentalAlgHom_apply (ht : AlgebraicIndependent k t)
    (hs : AlgebraicIndependent k s) (i : ι) :
    adjoinTranscendentalAlgHom ht hs ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ = s i := by
  have h1 : ht.aevalEquivField (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) (MvPolynomial.X i)) =
      ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ := by
    refine Subtype.ext ?_
    rw [ht.aevalEquivField_algebraMap_apply_coe]
    simp
  have h2 : ht.aevalEquivField.symm ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩ =
      algebraMap (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))
        (MvPolynomial.X i) := by
    rw [← h1, AlgEquiv.symm_apply_apply]
  have h3 : hs.aevalEquivField (algebraMap (MvPolynomial ι k)
      (FractionRing (MvPolynomial ι k)) (MvPolynomial.X i)) =
      ⟨s i, subset_adjoin k _ ⟨i, rfl⟩⟩ := by
    refine Subtype.ext ?_
    rw [hs.aevalEquivField_algebraMap_apply_coe]
    simp
  change (adjoin k (Set.range s)).val
    (hs.aevalEquivField (ht.aevalEquivField.symm
      ⟨t i, subset_adjoin k _ ⟨i, rfl⟩⟩)) = s i
  rw [h2, h3]
  rfl

end Relocate

section Extend

/-- A `k`-embedding of an intermediate field into an algebraically closed
ambient field extends along any algebraic extension of intermediate fields
(blueprint Lemma 8.1(b), algebraic part).
@isnad1 id=ex.1h5v.s11.5f32c7cba5a2 from=translated src=- shape=d70236a5 vocab=1004dcee
-/
theorem exists_extension_of_isAlgebraic [IsAlgClosed Ω]
    {E E' : IntermediateField k Ω} (hEE' : E ≤ E')
    [halg : Algebra.IsAlgebraic ↥E ↥(extendScalars hEE')]
    (φ : ↥E →ₐ[k] Ω) :
    ∃ ψ : ↥E' →ₐ[k] Ω, ∀ x : ↥E, ψ ⟨x.1, hEE' x.2⟩ = φ x := by
  -- View `Ω` as an `E`-algebra through `φ` and lift; repackage by hand to
  -- avoid an `SMul` diamond with the canonical action.
  letI : Algebra ↥E Ω := φ.toAlgebra
  let ψE : ↥(extendScalars hEE') →ₐ[↥E] Ω := IsAlgClosed.lift
  have hcomm : ∀ y : ↥E, ψE (algebraMap ↥E ↥(extendScalars hEE') y) = φ y :=
    fun y ↦ ψE.commutes y
  refine ⟨{ toRingHom := ψE.toRingHom, commutes' := fun c ↦ ?_ }, fun x ↦ ?_⟩
  · have h1 : (algebraMap k ↥E' c : ↥E') =
        algebraMap ↥E ↥(extendScalars hEE') (algebraMap k ↥E c) := rfl
    change ψE (algebraMap k ↥E' c) = algebraMap k Ω c
    rw [h1, hcomm, φ.commutes]
  · have hx : (⟨x.1, hEE' x.2⟩ : ↥(extendScalars hEE')) =
        algebraMap ↥E ↥(extendScalars hEE') x := rfl
    change ψE ⟨x.1, hEE' x.2⟩ = φ x
    rw [hx, hcomm]

end Extend

section Assemble

/-- Every value of the relocation embedding lies in `k(s)`.
@isnad1 id=mem.2h6v.s9.8761d0087ab3 from=translated src=- shape=688e82b5 vocab=c8afa98d
-/
theorem adjoinTranscendentalAlgHom_mem {ι : Type*} {t s : ι → Ω}
    (ht : AlgebraicIndependent k t) (hs : AlgebraicIndependent k s)
    (x : ↥(adjoin k (Set.range t))) :
    adjoinTranscendentalAlgHom ht hs x ∈ adjoin k (Set.range s) := by
  change (adjoin k (Set.range s)).val
    (hs.aevalEquivField (ht.aevalEquivField.symm x)) ∈ adjoin k (Set.range s)
  exact SetLike.coe_mem _

/-- Independent realization of a generic point (blueprint Lemma 8.1(b)):
given a tuple `a` with a transcendence basis `t` inside `k(a)`, and any other
algebraically independent tuple `s`, there is a tuple `b` with the same
vanishing ideal as `a` all of whose coordinates are algebraic over `k(s)`.
Choosing `s` algebraically independent over a prescribed field `E₀` makes
the new copy of the locus generically independent from `E₀`.
@isnad1 id=ex.4h7v.s10.695743eb98f3 from=translated src=- shape=e6c7bcfc vocab=c9f60378
-/
theorem exists_relocation [IsAlgClosed Ω] {n d : ℕ} {a : Fin n → Ω}
    {t : Fin d → Ω} (ht : AlgebraicIndependent k t)
    (hle : adjoin k (Set.range t) ≤ adjoin k (Set.range a))
    (halg : Algebra.IsAlgebraic ↥(adjoin k (Set.range t)) ↥(extendScalars hle))
    {s : Fin d → Ω} (hs : AlgebraicIndependent k s) :
    ∃ b : Fin n → Ω, idealOf k b = idealOf k a ∧
      ∀ j, IsAlgebraic ↥(adjoin k (Set.range s)) (b j) := by
  classical
  -- Relocate the transcendental part, then extend algebraically.
  obtain ⟨ψ, hψ⟩ := exists_extension_of_isAlgebraic (halg := halg) hle
    (adjoinTranscendentalAlgHom ht hs)
  set ta : Fin n → ↥(adjoin k (Set.range a)) :=
    fun j ↦ ⟨a j, subset_adjoin k _ ⟨j, rfl⟩⟩ with hta
  refine ⟨fun j ↦ ψ (ta j), ?_, ?_⟩
  · -- Same vanishing ideal: evaluation factors through the embedding.
    ext f
    rw [mem_idealOf_iff, mem_idealOf_iff]
    have h1 : MvPolynomial.aeval (fun j ↦ ψ (ta j)) f = ψ (MvPolynomial.aeval ta f) := by
      rw [MvPolynomial.comp_aeval_apply]
    have h2 : MvPolynomial.aeval a f =
        (adjoin k (Set.range a)).val (MvPolynomial.aeval ta f) := by
      rw [MvPolynomial.comp_aeval_apply]
      rfl
    rw [h1, h2]
    constructor
    · intro h
      have h4 : ψ (MvPolynomial.aeval ta f) = ψ 0 := by
        rw [map_zero]
        exact h
      rw [ψ.injective h4, map_zero]
    · intro h
      have h4 : (adjoin k (Set.range a)).val (MvPolynomial.aeval ta f) =
          (adjoin k (Set.range a)).val 0 := by
        rw [map_zero]
        exact h
      rw [(adjoin k (Set.range a)).val.injective h4, map_zero]
  · -- Coordinates are algebraic over `k(s)`.
    intro j
    -- `a j` is algebraic over `k(t)`.
    obtain ⟨p, hp0, hpz⟩ := (halg.isAlgebraic
      (⟨(ta j).1, (ta j).2⟩ : ↥(extendScalars hle)))
    -- Push the annihilating polynomial through the embedding.
    refine isAlgebraic_of_coeff_mem (p := p.map ((adjoinTranscendentalAlgHom ht hs) :
        ↥(adjoin k (Set.range t)) →+* Ω))
      ((Polynomial.map_ne_zero_iff (RingHom.injective _)).2 hp0) ?_ fun m ↦ ?_
    · -- Evaluation: `ψ` extends the relocation on `k(t)`.
      have hcomp : ((ψ : ↥(adjoin k (Set.range a)) →+* Ω).comp
          (algebraMap ↥(adjoin k (Set.range t)) ↥(extendScalars hle))) =
          ((adjoinTranscendentalAlgHom ht hs) : ↥(adjoin k (Set.range t)) →+* Ω) := by
        refine RingHom.ext fun y ↦ ?_
        exact hψ y
      rw [Polynomial.eval_map, ← hcomp]
      have h3 : ψ ((Polynomial.aeval (⟨(ta j).1, (ta j).2⟩ :
          ↥(extendScalars hle))) p) = 0 := by
        rw [hpz]
        exact map_zero ψ
      rw [← h3, Polynomial.aeval_def]
      exact (Polynomial.hom_eval₂ p
        (algebraMap ↥(adjoin k (Set.range t)) ↥(extendScalars hle))
        ψ.toRingHom ⟨(ta j).1, (ta j).2⟩).symm
    · rw [Polynomial.coeff_map]
      exact adjoinTranscendentalAlgHom_mem ht hs _

end Assemble

section Joint

open MvPolynomial

variable {m n : ℕ}

/-- Partial evaluation: substituting the first block of variables by a tuple
of an intermediate field turns a `k`-polynomial in `m + n` variables into an
`E`-polynomial in the last `n` variables.-/
noncomputable def partialAeval (E : IntermediateField k Ω) (c : Fin m → ↥E) :
    MvPolynomial (Fin m ⊕ Fin n) k →ₐ[k] MvPolynomial (Fin n) ↥E :=
  aeval (Sum.elim (fun i ↦ C (c i)) X)

/--
@isnad1 id=eq.0h8v.s11.3a193be2e199 from=translated src=- shape=6506f857 vocab=33054054
-/
theorem aeval_partialAeval (E : IntermediateField k Ω) (c : Fin m → ↥E)
    (w : Fin n → Ω) (f : MvPolynomial (Fin m ⊕ Fin n) k) :
    aeval w (partialAeval (Ω := Ω) E c f) =
      aeval (Sum.elim (fun i ↦ (c i : Ω)) w) f := by
  have h : ((aeval w : MvPolynomial (Fin n) ↥E →ₐ[↥E] Ω).restrictScalars k).comp
      (partialAeval (Ω := Ω) E c) = aeval (Sum.elim (fun i ↦ (c i : Ω)) w) := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases i with i | j
    · simp [partialAeval]
    · simp [partialAeval]
  exact congrArg (fun (g : MvPolynomial (Fin m ⊕ Fin n) k →ₐ[k] Ω) ↦ g f) h

/-- Packaging lemma for the algebraicity hypothesis of
`exists_joint_relocation`: if every generator in `T` is algebraic over
`adjoin F S`, then the extension `adjoin F T / adjoin F S` is algebraic.
@isnad1 id=isalgebr.2h4v.s10.580d7e4d9d87 from=translated src=- shape=cecb0680 vocab=ddbb325e
-/
theorem isAlgebraic_extendScalars_adjoin {F : Type*} [Field F] [Algebra F Ω]
    {S T : Set Ω} (hle : adjoin F S ≤ adjoin F T)
    (halg : ∀ x ∈ T, IsAlgebraic ↥(adjoin F S) x) :
    Algebra.IsAlgebraic ↥(adjoin F S) ↥(extendScalars hle) := by
  have key : extendScalars hle = adjoin ↥(adjoin F S) T := by
    refine restrictScalars_injective F ?_
    rw [adjoin_adjoin_left, extendScalars_restrictScalars, adjoin_union]
    exact (sup_eq_right.2 hle).symm
  rw [key]
  exact isAlgebraic_adjoin fun x hx ↦ (halg x hx).isIntegral

/-- Joint-relation relocation (step 1 of the fused curve-coset design):
relocating `c₂` over the base `k(c₁)` preserves every joint `k`-polynomial
relation with `c₁`, while making the new copy algebraic over prescribed
fresh elements.
@isnad1 id=ex.4h9v.s13.f8d3bec59a05 from=translated src=- shape=7da523a7 vocab=994417b5
-/
theorem exists_joint_relocation [IsAlgClosed Ω] {d : ℕ}
    (c₁ : Fin m → Ω) {c₂ : Fin n → Ω} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ↥(adjoin k (Set.range c₁)) t)
    (hle : adjoin ↥(adjoin k (Set.range c₁)) (Set.range t) ≤
      adjoin ↥(adjoin k (Set.range c₁)) (Set.range c₂))
    (halg : Algebra.IsAlgebraic
      ↥(adjoin ↥(adjoin k (Set.range c₁)) (Set.range t)) ↥(extendScalars hle))
    {s : Fin d → Ω}
    (hs : AlgebraicIndependent ↥(adjoin k (Set.range c₁)) s) :
    ∃ c₂' : Fin n → Ω,
      (∀ f : MvPolynomial (Fin m ⊕ Fin n) k,
        aeval (Sum.elim c₁ c₂') f = 0 ↔ aeval (Sum.elim c₁ c₂) f = 0) ∧
      ∀ j, IsAlgebraic
        ↥(adjoin ↥(adjoin k (Set.range c₁)) (Set.range s)) (c₂' j) := by
  set K₀ := adjoin k (Set.range c₁)
  obtain ⟨c₂', hideal, halg'⟩ := exists_relocation (k := ↥K₀) ht hle halg hs
  refine ⟨c₂', fun f ↦ ?_, halg'⟩
  set tc₁ : Fin m → ↥K₀ := fun i ↦ ⟨c₁ i, subset_adjoin k _ ⟨i, rfl⟩⟩ with htc₁
  have hval : ∀ i, ((tc₁ i : ↥K₀) : Ω) = c₁ i := fun i ↦ rfl
  have h1 : aeval (Sum.elim c₁ c₂') f =
      aeval c₂' (partialAeval (Ω := Ω) K₀ tc₁ f) := by
    rw [aeval_partialAeval]
  have h2 : aeval (Sum.elim c₁ c₂) f =
      aeval c₂ (partialAeval (Ω := Ω) K₀ tc₁ f) := by
    rw [aeval_partialAeval]
  rw [h1, h2, ← mem_idealOf_iff, ← mem_idealOf_iff, hideal]

end Joint

section SumLocus

open MvPolynomial

variable {n : ℕ}

/-- The sum substitution `X j ↦ X (inl j) + X (inr j)`.-/
noncomputable def addSubst :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n ⊕ Fin n) k :=
  aeval fun j ↦ X (Sum.inl j) + X (Sum.inr j)

/--
@isnad1 id=eq.0h6v.s9.95431630e418 from=translated src=- shape=03046eb2 vocab=95398fc8
-/
theorem aeval_addSubst (u v : Fin n → Ω) (h : MvPolynomial (Fin n) k) :
    aeval (Sum.elim u v) (addSubst (k := k) h) = aeval (u + v) h := by
  have hcomp : ((aeval (Sum.elim u v) : MvPolynomial (Fin n ⊕ Fin n) k →ₐ[k] Ω).comp
      (addSubst (k := k))) = aeval (u + v) := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    simp [addSubst]
  exact congrArg (fun (g : MvPolynomial (Fin n) k →ₐ[k] Ω) ↦ g h) hcomp

/-- Step 2a of the fused curve-coset design: a joint-relation-preserving
relocation of `c₂` preserves the vanishing ideal of the componentwise sum.
@isnad1 id=eq.1h6v.s9.7e3c1d5afbc8 from=translated src=- shape=23afb79b vocab=75d0b4b2
-/
theorem idealOf_add_eq_of_joint {c₁ c₂ c₂' : Fin n → Ω}
    (H : ∀ f : MvPolynomial (Fin n ⊕ Fin n) k,
      aeval (Sum.elim c₁ c₂') f = 0 ↔ aeval (Sum.elim c₁ c₂) f = 0) :
    idealOf k (c₁ + c₂') = idealOf k (c₁ + c₂) := by
  ext h
  rw [mem_idealOf_iff, mem_idealOf_iff, ← aeval_addSubst, ← aeval_addSubst]
  exact H (addSubst (k := k) h)

/-- The product substitution `X j ↦ X (inl j) * X (inr j)` — the
multiplicative analogue of `addSubst`.-/
noncomputable def mulSubst :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n ⊕ Fin n) k :=
  aeval fun j ↦ X (Sum.inl j) * X (Sum.inr j)

/--
@isnad1 id=eq.0h6v.s9.74fdfb8c36c0 from=translated src=- shape=03046eb2 vocab=8b2231a9
-/
theorem aeval_mulSubst (u v : Fin n → Ω) (h : MvPolynomial (Fin n) k) :
    aeval (Sum.elim u v) (mulSubst (k := k) h) = aeval (u * v) h := by
  have hcomp : ((aeval (Sum.elim u v) : MvPolynomial (Fin n ⊕ Fin n) k →ₐ[k] Ω).comp
      (mulSubst (k := k))) = aeval (u * v) := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    simp [mulSubst]
  exact congrArg (fun (g : MvPolynomial (Fin n) k →ₐ[k] Ω) ↦ g h) hcomp

/-- The multiplicative form of step 2a: a joint-relation-preserving
relocation preserves the vanishing ideal of the componentwise product.
@isnad1 id=eq.1h6v.s9.300f1e2f630b from=translated src=- shape=23afb79b vocab=4fa3dbef
-/
theorem idealOf_mul_eq_of_joint {c₁ c₂ c₂' : Fin n → Ω}
    (H : ∀ f : MvPolynomial (Fin n ⊕ Fin n) k,
      aeval (Sum.elim c₁ c₂') f = 0 ↔ aeval (Sum.elim c₁ c₂) f = 0) :
    idealOf k (c₁ * c₂') = idealOf k (c₁ * c₂) := by
  ext h
  rw [mem_idealOf_iff, mem_idealOf_iff, ← aeval_mulSubst, ← aeval_mulSubst]
  exact H (mulSubst (k := k) h)

/-- The difference substitution `X j ↦ X (inl j) - X (inr j)`.-/
noncomputable def subSubst :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n ⊕ Fin n) k :=
  aeval fun j ↦ X (Sum.inl j) - X (Sum.inr j)

/--
@isnad1 id=eq.0h6v.s9.ed4842616839 from=translated src=- shape=03046eb2 vocab=251928ba
-/
theorem aeval_subSubst (u v : Fin n → Ω) (h : MvPolynomial (Fin n) k) :
    aeval (Sum.elim u v) (subSubst (k := k) h) = aeval (u - v) h := by
  have hcomp : ((aeval (Sum.elim u v) : MvPolynomial (Fin n ⊕ Fin n) k →ₐ[k] Ω).comp
      (subSubst (k := k))) = aeval (u - v) := by
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    simp [subSubst]
  exact congrArg (fun (g : MvPolynomial (Fin n) k →ₐ[k] Ω) ↦ g h) hcomp

/-- A joint-relation-preserving relocation also preserves the vanishing
ideal of the componentwise difference (used for the translation element
`δ = c₂ - c₂'` of the curve-coset argument).
@isnad1 id=eq.1h6v.s9.6d7148f410e3 from=translated src=- shape=23afb79b vocab=c2c51b22
-/
theorem idealOf_sub_eq_of_joint {c₁ c₂ c₂' : Fin n → Ω}
    (H : ∀ f : MvPolynomial (Fin n ⊕ Fin n) k,
      aeval (Sum.elim c₁ c₂') f = 0 ↔ aeval (Sum.elim c₁ c₂) f = 0) :
    idealOf k (c₁ - c₂') = idealOf k (c₁ - c₂) := by
  ext h
  rw [mem_idealOf_iff, mem_idealOf_iff, ← aeval_subSubst, ← aeval_subSubst]
  exact H (subSubst (k := k) h)

end SumLocus

end

end AclGeom
