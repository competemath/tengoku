/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.GenericPoints
import Tengoku.AclGeom.AclGeom.Correspondence.CurveIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of translation invariance along the locus

Step 4d of the fused curve-coset chain: the exact translation identity
`F(X + δ₁, Y + δ₂) = F` at the *generic* point `δ` of the translation locus
descends to every point of the locus. The identity is equivalent to the
vanishing at `δ` of the finitely many universal coefficient polynomials of
`F(X + U, Y + V) − F(X, Y)`; genericity places them in the vanishing ideal
of `δ`, so they vanish at any point whose ideal contains it.

* `aevalSnd`: evaluation of the second variable block at constants;
* `coeffUV`: the universal coefficient polynomials, via `toUVPoly`;
* `translate_eq_of_idealOf_le`: the descent theorem.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M3a, checklist C6/C7).
-/

namespace AclGeom

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

section BlockEval

variable {K : Type*} [Field K] [Algebra k K]

/-- Evaluation of the second variable block at constants: `X (inl j) ↦ X j`,
`X (inr j) ↦ C (c j)`.-/
def aevalSnd (c : Fin 2 → K) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin 2) K :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (c j))

/-- The universal coefficient view: the second block becomes the coefficient
ring.-/
def toUVPoly :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) :=
  aeval (Sum.elim (fun j ↦ X j) fun j ↦ C (X j))

/-- `aevalSnd` factors through the universal coefficient view.
@isnad1 id=eq.0h4v.s11.31ec5815be81 from=translated src=- shape=599d0f27 vocab=3c5c5dee
-/
theorem aevalSnd_eq_map_toUVPoly (c : Fin 2 → K)
    (g : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aevalSnd (k := k) c g =
      MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K) (toUVPoly (k := k) g) := by
  have hcomp : (aevalSnd (k := k) c).toRingHom =
      ((MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K)).comp (toUVPoly (k := k)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalSnd, toUVPoly, MvPolynomial.algebraMap_eq]
    · rcases i with j | j
      · simp [aevalSnd, toUVPoly]
      · simp [aevalSnd, toUVPoly]
  exact congrArg (fun (f : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* _) ↦ f g) hcomp

/-- The coefficient bridge: coefficients of a block evaluation are the
evaluations of the universal coefficient polynomials.
@isnad1 id=eq.0h5v.s10.b1169518cc33 from=translated src=- shape=0941f827 vocab=80265446
-/
theorem coeff_aevalSnd (c : Fin 2 → K) (g : MvPolynomial (Fin 2 ⊕ Fin 2) k)
    (m : Fin 2 →₀ ℕ) :
    (aevalSnd (k := k) c g).coeff m =
      aeval c ((toUVPoly (k := k) g).coeff m) := by
  rw [aevalSnd_eq_map_toUVPoly, MvPolynomial.coeff_map]
  rfl

/-- Block evaluation of the sum substitution is the translation of the
extended polynomial.
@isnad1 id=eq.0h4v.s10.6cef0a97a115 from=translated src=- shape=6c4e2474 vocab=33314d58
-/
theorem aevalSnd_addSubst (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (addSubst (k := k) F) =
      translate c (MvPolynomial.map (algebraMap k K) F) := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (addSubst (k := k)).toRingHom) =
      ((translate c).toRingHom.comp
        (MvPolynomial.map (algebraMap k K) :
          MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, addSubst, translate, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd, addSubst, translate]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- Block evaluation of the first-block inclusion is coefficient
extension.
@isnad1 id=eq.0h4v.s10.496ba847feb7 from=translated src=- shape=57175c55 vocab=acfc6090
-/
theorem aevalSnd_rename_inl (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalSnd (k := k) c (rename Sum.inl F) =
      MvPolynomial.map (algebraMap k K) F := by
  have hcomp : ((aevalSnd (k := k) c).toRingHom.comp
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      (MvPolynomial.map (algebraMap k K) :
        MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalSnd, MvPolynomial.algebraMap_eq]
    · simp [aevalSnd]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

end BlockEval

section JointDetermination

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]

/-- Evaluation of the first variable block at constants:
`X (inl j) ↦ C (c j)`, `X (inr j) ↦ X j`.-/
def aevalFst (c : Fin 2 → K) :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin 2) K :=
  aeval (Sum.elim (fun j ↦ C (c j)) fun j ↦ X j)

/-- Composing first-block evaluation with a point evaluation recovers the
joint evaluation.
@isnad1 id=eq.0h6v.s10.6ac55ecd03df from=translated src=- shape=67f6bf79 vocab=70ad223e
-/
theorem aeval_aevalFst (c : Fin 2 → K) (v : Fin 2 → Ω)
    (f : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aeval v (aevalFst (k := k) c f) =
      aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) v) f := by
  have hcomp : ((aeval v : MvPolynomial (Fin 2) K →ₐ[K] Ω) :
      MvPolynomial (Fin 2) K →+* Ω).comp (aevalFst (k := k) c).toRingHom =
      ((aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) v) :
        MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k] Ω) :
        MvPolynomial (Fin 2 ⊕ Fin 2) k →+* Ω) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    · rcases i with j | j
      · simp [aevalFst]
      · simp [aevalFst]
  exact congrArg (fun (g : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* Ω) ↦ g f) hcomp

/-- **Joint-type determination, one direction**: if the vanishing ideal of
`q` over `K` is spanned by the extension of `G`, then any joint polynomial
vanishing at `(c, q)` vanishes at `(c, w)` for every zero `w` of `G` — the
first block evaluates into `K`, and the resulting relative polynomial is a
multiple of the extended generator.
@isnad1 id=eq.3h8v.s10.a83f2d7826cd from=translated src=- shape=e523be1f vocab=e01db131
-/
theorem joint_aeval_eq_zero {c : Fin 2 → K} {q : Fin 2 → Ω}
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    {w : Fin 2 → Ω} (hw : aeval w G = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q) f = 0) :
    aeval (Sum.elim (fun j ↦ algebraMap K Ω (c j)) w) f = 0 := by
  have hfK : aevalFst (k := k) c f ∈ idealOf K q := by
    rw [mem_idealOf_iff, aeval_aevalFst]
    exact hf
  rw [hspan, Ideal.mem_span_singleton'] at hfK
  obtain ⟨h, hh⟩ := hfK
  rw [← aeval_aevalFst, ← hh, map_mul]
  have hGw : aeval w (MvPolynomial.map (algebraMap k K) G) = (0 : Ω) := by
    rw [aeval_map_algebraMap]
    exact hw
  rw [hGw, mul_zero]

/-- First-block evaluation of the sum substitution is the translation of
the extended polynomial.
@isnad1 id=eq.0h4v.s10.89dbb7601f1a from=translated src=- shape=6c4e2474 vocab=474ffbf6
-/
theorem aevalFst_addSubst (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (addSubst (k := k) F) =
      translate c (MvPolynomial.map (algebraMap k K) F) := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (addSubst (k := k)).toRingHom) =
      ((translate c).toRingHom.comp
        (MvPolynomial.map (algebraMap k K) :
          MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, addSubst, translate, MvPolynomial.algebraMap_eq]
    · simp [aevalFst, addSubst, translate, add_comm]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- First-block evaluation of the first-block inclusion is the constant of
the evaluation.
@isnad1 id=eq.0h4v.s10.6e701efda697 from=translated src=- shape=ab1e10f7 vocab=ec593a7e
-/
theorem aevalFst_rename_inl (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (rename Sum.inl F) = C (aeval c F) := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      ((C : K →+* MvPolynomial (Fin 2) K).comp
        ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
          MvPolynomial (Fin 2) k →+* K)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq]
    · simp [aevalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- First-block evaluation of the second-block inclusion is coefficient
extension.
@isnad1 id=eq.0h4v.s10.1106155e316f from=translated src=- shape=57175c55 vocab=923194f3
-/
theorem aevalFst_rename_inr (c : Fin 2 → K) (F : MvPolynomial (Fin 2) k) :
    aevalFst (k := k) c (rename Sum.inr F) =
      MvPolynomial.map (algebraMap k K) F := by
  have hcomp : ((aevalFst (k := k) c).toRingHom.comp
      (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)).toRingHom) =
      (MvPolynomial.map (algebraMap k K) :
        MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) K) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [aevalFst, MvPolynomial.algebraMap_eq]
    · simp [aevalFst]
  exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* _) ↦ f F) hcomp

/-- Bridged form of `joint_aeval_eq_zero`: the first block is given as an
`Ω`-tuple together with the equation identifying it as the image of a
`K`-tuple. Keeping the concrete coercion inside a hypothesis avoids
elaborating evaluation maps at concrete intermediate fields.
@isnad1 id=eq.4h9v.s10.41ed47d84286 from=translated src=- shape=4d005aed vocab=e01db131
-/
theorem joint_aeval_eq_zero' {c : Fin 2 → K} {p q : Fin 2 → Ω}
    (hp : (fun j ↦ algebraMap K Ω (c j)) = p)
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    {w : Fin 2 → Ω} (hw : aeval w G = 0)
    {f : MvPolynomial (Fin 2 ⊕ Fin 2) k}
    (hf : aeval (Sum.elim p q) f = 0) :
    aeval (Sum.elim p w) f = 0 := by
  subst hp
  exact joint_aeval_eq_zero hspan hw hf

/-- **Joint-type determination**: two points of the same curve, each generic
over the field `K` generated by the first block, have the same joint
vanishing ideal with it.
@isnad1 id=eq.2h7v.s10.285fc4048d6c from=translated src=- shape=b58c3933 vocab=9627ed07
-/
theorem joint_idealOf_eq {c : Fin 2 → K} {q q' : Fin 2 → Ω}
    {G : MvPolynomial (Fin 2) k}
    (hspan : idealOf K q = Ideal.span {MvPolynomial.map (algebraMap k K) G})
    (hspan' : idealOf K q' =
      Ideal.span {MvPolynomial.map (algebraMap k K) G}) :
    idealOf k (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q) =
      idealOf k (Sum.elim (fun j ↦ algebraMap K Ω (c j)) q') := by
  have hzero : ∀ {r : Fin 2 → Ω}, idealOf K r =
      Ideal.span {MvPolynomial.map (algebraMap k K) G} → aeval r G = 0 := by
    intro r hr
    have hmem : MvPolynomial.map (algebraMap k K) G ∈ idealOf K r := by
      rw [hr]
      exact Ideal.subset_span rfl
    have h := (mem_idealOf_iff K).1 hmem
    rwa [aeval_map_algebraMap] at h
  refine idealOf_eq_of_aeval_iff k fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact joint_aeval_eq_zero hspan (hzero hspan') h
  · exact joint_aeval_eq_zero hspan' (hzero hspan) h

/-- Translation commutes with coefficient maps.
@isnad1 id=eq.0h5v.s10.d278679b6c30 from=translated src=- shape=06eedd26 vocab=58355c33
-/
theorem map_translate {L : Type*} [Field L] (f : K →+* L) (c : Fin 2 → K)
    (g : MvPolynomial (Fin 2) K) :
    MvPolynomial.map f (translate c g) =
      translate (fun j ↦ f (c j)) (MvPolynomial.map f g) := by
  have hcomp : ((MvPolynomial.map f).comp (translate c).toRingHom :
      MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) L) =
      ((translate fun j ↦ f (c j)).toRingHom.comp (MvPolynomial.map f)) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp [translate, MvPolynomial.algebraMap_eq]
    · simp [translate]
  exact congrArg (fun (F : MvPolynomial (Fin 2) K →+* _) ↦ F g) hcomp

/-- The universal coefficient view with the first block as coefficients.-/
def toVUPoly :
    MvPolynomial (Fin 2 ⊕ Fin 2) k →ₐ[k]
      MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) :=
  aeval (Sum.elim (fun j ↦ C (X j)) fun j ↦ X j)

/-- `aevalFst` factors through the first-block universal coefficient
view.
@isnad1 id=eq.0h4v.s11.49f4c4b865a0 from=translated src=- shape=599d0f27 vocab=aab15994
-/
theorem aevalFst_eq_map_toVUPoly (c : Fin 2 → K)
    (g : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    aevalFst (k := k) c g =
      MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K) (toVUPoly (k := k) g) := by
  have hcomp : (aevalFst (k := k) c).toRingHom =
      ((MvPolynomial.map ((aeval c : MvPolynomial (Fin 2) k →ₐ[k] K) :
        MvPolynomial (Fin 2) k →+* K)).comp (toVUPoly (k := k)).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [aevalFst, toVUPoly, MvPolynomial.algebraMap_eq]
    · rcases i with j | j
      · simp [aevalFst, toVUPoly]
      · simp [aevalFst, toVUPoly]
  exact congrArg (fun (f : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* _) ↦ f g) hcomp

/-- The coefficient bridge for the first block.
@isnad1 id=eq.0h5v.s10.0a5b74d7a0ba from=translated src=- shape=0941f827 vocab=c0baf8f7
-/
theorem coeff_aevalFst (c : Fin 2 → K) (g : MvPolynomial (Fin 2 ⊕ Fin 2) k)
    (m : Fin 2 →₀ ℕ) :
    (aevalFst (k := k) c g).coeff m =
      aeval c ((toVUPoly (k := k) g).coeff m) := by
  rw [aevalFst_eq_map_toVUPoly, MvPolynomial.coeff_map]
  rfl

/-- Reassembling a universal-coefficient polynomial into the joint ring.-/
noncomputable def fromVUPoly :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) →+*
      MvPolynomial (Fin 2 ⊕ Fin 2) k :=
  eval₂Hom (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2 ⊕ Fin 2) k).toRingHom
    fun j ↦ X (Sum.inr j)

/-- The universal coefficient view is a section of reassembly.
@isnad1 id=eq.0h2v.s10.a488ce766fc5 from=translated src=- shape=6287ae9a vocab=e6a2179d
-/
theorem fromVUPoly_toVUPoly (g : MvPolynomial (Fin 2 ⊕ Fin 2) k) :
    fromVUPoly (k := k) (toVUPoly (k := k) g) = g := by
  have hcomp : ((fromVUPoly (k := k)).comp (toVUPoly (k := k)).toRingHom) =
      RingHom.id (MvPolynomial (Fin 2 ⊕ Fin 2) k) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [fromVUPoly, toVUPoly, MvPolynomial.algebraMap_eq]
    · rcases i with j | j
      · simp [fromVUPoly, toVUPoly]
      · simp [fromVUPoly, toVUPoly]
  exact congrArg (fun (F : MvPolynomial (Fin 2 ⊕ Fin 2) k →+* _) ↦ F g) hcomp

/-- Membership in the span of a constant-coefficient polynomial is a
coefficientwise condition.
@isnad1 id=iff.0h3v.s9.b0af95e7b720 from=translated src=- shape=01259a24 vocab=e477e877
-/
theorem mem_span_C_iff {R : Type*} [CommRing R] {g : R}
    {p : MvPolynomial (Fin 2) R} :
    p ∈ Ideal.span {(C g : MvPolynomial (Fin 2) R)} ↔
      ∀ m, p.coeff m ∈ Ideal.span {g} := by
  constructor
  · intro hp m
    rw [Ideal.mem_span_singleton'] at hp
    obtain ⟨q, hq⟩ := hp
    rw [Ideal.mem_span_singleton]
    exact ⟨q.coeff m, by rw [← hq, mul_comm q (C g), coeff_C_mul]⟩
  · intro h
    classical
    choose r hr using fun m ↦ Ideal.mem_span_singleton.1 (h m)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ m ∈ p.support, monomial m (r m), ?_⟩
    rw [Finset.sum_mul]
    conv_rhs => rw [p.as_sum]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    rw [mul_comm, C_mul_monomial, ← hr m]

/-- Renaming along an injective map preserves the total degree.
@isnad1 id=eq.1h5v.s8.d23ea214a27b from=translated src=- shape=65d3e9ad vocab=7c0267b2
-/
theorem totalDegree_rename_of_injective {σ τ : Type*} [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f) (p : MvPolynomial σ k) :
    (rename f p).totalDegree = p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree,
    support_rename_of_injective hf, Finset.sup_image]
  refine Finset.sup_congr rfl fun m _ ↦ ?_
  exact Finsupp.sum_mapDomain_index (h := fun _ e ↦ e) (fun _ ↦ rfl)
    fun _ _ _ ↦ rfl

/-- The sum substitution does not raise the total degree.
@isnad1 id=le.0h2v.s9.1f4f67ca2cc1 from=translated src=- shape=e38b22ba vocab=c114df9d
-/
theorem totalDegree_addSubst_le (g : MvPolynomial (Fin 2) k) :
    (addSubst (k := k) g).totalDegree ≤ g.totalDegree := by
  classical
  rw [show addSubst (k := k) g =
    eval₂ (algebraMap k (MvPolynomial (Fin 2 ⊕ Fin 2) k))
      (fun j ↦ X (Sum.inl j) + X (Sum.inr j)) g from rfl, eval₂_eq]
  refine le_trans (totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun d hd ↦ ?_
  refine le_trans (totalDegree_mul _ _) ?_
  have hC : (algebraMap k (MvPolynomial (Fin 2 ⊕ Fin 2) k)
      (g.coeff d)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_eq, totalDegree_C]
  rw [hC, zero_add]
  refine le_trans (totalDegree_finsetProd _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i _ ↦ ?_)
    (by rw [← Finsupp.sum]; exact le_totalDegree hd)
  refine le_trans (totalDegree_pow _ _) ?_
  have hXX : (X (Sum.inl i) + X (Sum.inr i) :
      MvPolynomial (Fin 2 ⊕ Fin 2) k).totalDegree ≤ 1 :=
    le_trans (totalDegree_add _ _)
      (max_le (le_of_eq (totalDegree_X _)) (le_of_eq (totalDegree_X _)))
  calc d i * (X (Sum.inl i) + X (Sum.inr i) :
      MvPolynomial (Fin 2 ⊕ Fin 2) k).totalDegree
      ≤ d i * 1 := Nat.mul_le_mul_left _ hXX
    _ = d i := mul_one _

/-- Primality of the curve generator persists into the first block of the
joint ring.
@isnad1 id=prime.1h2v.s9.75a478ea787e from=translated src=- shape=3484874a vocab=128e2404
-/
theorem prime_rename_inl {G : MvPolynomial (Fin 2) k} (hG : Prime G) :
    Prime (rename (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) G) := by
  classical
  have heq : (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) =
      ((↑) : Set.range (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) → Fin 2 ⊕ Fin 2) ∘
        (Equiv.ofInjective _ Sum.inl_injective) := by
    funext j
    simp
  have h2 : Prime (rename (⇑(Equiv.ofInjective
      (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) Sum.inl_injective)) G) := by
    have h := (MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective
      (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) Sum.inl_injective))).2 hG
    simpa [renameEquiv] using h
  have h3 := (prime_rename_iff
    (Set.range (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2))).2 h2
  rwa [rename_rename, ← heq] at h3

/-- … and into the second block.
@isnad1 id=prime.1h2v.s9.4e20cd58f3e5 from=translated src=- shape=3484874a vocab=1e4ec644
-/
theorem prime_rename_inr {G : MvPolynomial (Fin 2) k} (hG : Prime G) :
    Prime (rename (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) G) := by
  classical
  have heq : (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) =
      ((↑) : Set.range (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) → Fin 2 ⊕ Fin 2) ∘
        (Equiv.ofInjective _ Sum.inr_injective) := by
    funext j
    simp
  have h2 : Prime (rename (⇑(Equiv.ofInjective
      (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) Sum.inr_injective)) G) := by
    have h := (MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective
      (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) Sum.inr_injective))).2 hG
    simpa [renameEquiv] using h
  have h3 := (prime_rename_iff
    (Set.range (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2))).2 h2
  rwa [rename_rename, ← heq] at h3

end JointDetermination

/-- **Properness of the stabilizer**: a translation vector fixing a prime
generator cannot be algebraically independent — otherwise evaluating the
identity at the origin makes the generator constant. Consequently the
translation locus of the curve-coset chain is at most one-dimensional.
@isnad1 id=false.3h4v.s10.90d90257bb4a from=translated src=- shape=d47f1bc8 vocab=04298b61
-/
theorem not_algebraicIndependent_of_translate_eq
    {K : Type*} [Field K] [Algebra k K]
    {c : Fin 2 → K} {F : MvPolynomial (Fin 2) k} (hFp : Prime F)
    (hid : translate c (MvPolynomial.map (algebraMap k K) F) =
      MvPolynomial.map (algebraMap k K) F)
    (hc : AlgebraicIndependent k c) : False := by
  classical
  have h0 := congrArg (aeval (fun _ : Fin 2 ↦ (0 : K))) hid
  rw [aeval_translate] at h0
  have hzero : (fun j ↦ (0 : K) + algebraMap K K (c j)) = c := by
    funext j
    simp
  rw [hzero] at h0
  -- Both sides through the coefficient extension.
  rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap] at h0
  -- The generator satisfies a relation at the independent point.
  have hsq : (aeval c) (C (aeval (fun _ : Fin 2 ↦ (0 : k)) F) :
      MvPolynomial (Fin 2) k) = aeval (fun _ : Fin 2 ↦ (0 : K)) F := by
    rw [aeval_C]
    have hcomp2 : ((algebraMap k K).comp
        ((aeval (fun _ : Fin 2 ↦ (0 : k))).toRingHom :
          MvPolynomial (Fin 2) k →+* k)) =
        ((aeval (fun _ : Fin 2 ↦ (0 : K))).toRingHom :
          MvPolynomial (Fin 2) k →+* K) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_) <;> simp
    exact congrArg (fun (f : MvPolynomial (Fin 2) k →+* K) ↦ f F) hcomp2
  have hmem : F - C (aeval (fun _ : Fin 2 ↦ (0 : k)) F) ∈ idealOf k c := by
    rw [mem_idealOf_iff, map_sub, hsq, h0, sub_self]
  rw [(idealOf_eq_bot_iff k).2 hc, Ideal.mem_bot, sub_eq_zero] at hmem
  -- A constant cannot be prime.
  rcases eq_or_ne (aeval (fun _ : Fin 2 ↦ (0 : k)) F) 0 with hc0 | hc0
  · rw [hc0, map_zero] at hmem
    exact hFp.ne_zero hmem
  · exact hFp.not_isUnit (hmem ▸ (isUnit_iff_ne_zero.2 hc0).map
      (C : k →+* MvPolynomial (Fin 2) k))

end

end AclGeom
