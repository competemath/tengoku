import Tengoku.ClosureResidueP3Lean.P3.Filtration
import Tengoku.Seed.Analysis.InnerProductSpace.Orthogonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators
open Matrix

namespace P3

section Stabilizer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Raw diagonal gradient on vertex coordinates:
`(∇d)_{ij} = d_i - d_j` on directed off-diagonal edges.-/
def gradientRaw : VertexSpace V →ₗ[ℂ] EdgeSpace V where
  toFun d :=
    WithLp.toLp 2 (fun e => d.ofLp e.1.1 - d.ofLp e.1.2)
  map_add' d₁ d₂ := by
    apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
    ext e
    change
      (d₁.ofLp e.1.1 + d₂.ofLp e.1.1) -
          (d₁.ofLp e.1.2 + d₂.ofLp e.1.2) =
        (d₁.ofLp e.1.1 - d₁.ofLp e.1.2) +
          (d₂.ofLp e.1.1 - d₂.ofLp e.1.2)
    ring
  map_smul' c d := by
    apply (WithLp.linearEquiv 2 ℂ (Edge V → ℂ)).injective
    ext e
    change
      c * d.ofLp e.1.1 - c * d.ofLp e.1.2 =
        c * (d.ofLp e.1.1 - d.ofLp e.1.2)
    ring

/--
@isnad1 id=eq.0h3v.s9.67af1aee20ea from=translated src=- shape=9fa97a38 vocab=80d8f1ed
-/
@[simp]
theorem gradientRaw_apply (d : VertexSpace V) (e : Edge V) :
    (gradientRaw (V := V) d).ofLp e =
      d.ofLp e.1.1 - d.ofLp e.1.2 := by
  rfl

/-- E-stage gradient restricted to the traceless diagonal coordinate sector.-/
def gradient : DiagZero (V := V) →ₗ[ℂ] EdgeSpace V :=
  (gradientRaw (V := V)).comp (DiagZero (V := V)).subtype

/--
@isnad1 id=eq.0h3v.s11.1761d5595bce from=translated src=- shape=cf3bf9f7 vocab=46f492a9
-/
@[simp]
theorem gradient_apply (d : DiagZero (V := V)) (e : Edge V) :
    (gradient (V := V) d).ofLp e =
      d.1.ofLp e.1.1 - d.1.ofLp e.1.2 := by
  rfl

/--
@isnad1 id=eq.0h1v.s11.3a6b5c0e3ada from=translated src=- shape=33cab3eb vocab=7cb9ea26
-/
@[simp]
theorem gradient_zero :
    gradient (V := V) (0 : DiagZero (V := V)) = 0 := by
  exact LinearMap.map_zero _

/--
@isnad1 id=eq.0h3v.s12.a8009f12f220 from=translated src=- shape=f3482b12 vocab=66b91bf7
-/
theorem gradient_add (d₁ d₂ : DiagZero (V := V)) :
    gradient (V := V) (d₁ + d₂) =
      gradient (V := V) d₁ + gradient (V := V) d₂ := by
  exact LinearMap.map_add _ _ _

/--
@isnad1 id=eq.0h3v.s12.1a69525ee5ff from=translated src=- shape=f5a52ca0 vocab=ca6b2eba
-/
theorem gradient_smul (c : ℂ) (d : DiagZero (V := V)) :
    gradient (V := V) (c • d) =
      c • gradient (V := V) d := by
  exact LinearMap.map_smul _ _ _

/-! ## E1: Gradient--Divergence adjointness (Lemma 7.1) -/

/-- The edge-matrix realization of a gradient has the expected coordinate
formula on every pair; on the diagonal both sides vanish.
@isnad1 id=eq.0h4v.s11.ffe11a91312b from=translated src=- shape=09b5b617 vocab=737a7069
-/
@[simp]
theorem edgeMatrix_gradient_apply
    (d : DiagZero (V := V)) (i j : V) :
    edgeMatrix (V := V) (gradient (V := V) d) i j =
      d.1.ofLp i - d.1.ofLp j := by
  by_cases h : i = j
  · subst j
    simp [edgeMatrix]
  · simp [edgeMatrix, h, gradient_apply]

/-- The standard Hermitian inner product on directed-edge space can be
written as a double sum over all vertex pairs, because the diagonal entries
of `edgeMatrix` vanish.
@isnad1 id=eq.0h3v.s10.39246f938bc2 from=translated src=- shape=4e7c0320 vocab=9545408d
-/
theorem edge_inner_eq_double_sum
    (f g : EdgeSpace V) :
    inner ℂ f g =
      ∑ i : V, ∑ j : V,
        edgeMatrix (V := V) g i j *
          star (edgeMatrix (V := V) f i j) := by
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply]
  change
    (∑ e : Edge V, g.ofLp e * star (f.ofLp e)) =
      ∑ i : V, ∑ j : V,
        edgeMatrix (V := V) g i j *
          star (edgeMatrix (V := V) f i j)
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun p : V × V => p.1 ≠ p.2)
      (fun p : V × V =>
        edgeMatrix (V := V) g p.1 p.2 *
          star (edgeMatrix (V := V) f p.1 p.2))
  have hdiag :
      (∑ p : {p : V × V // ¬ p.1 ≠ p.2},
        edgeMatrix (V := V) g p.1.1 p.1.2 *
          star (edgeMatrix (V := V) f p.1.1 p.1.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hEq : p.1.1 = p.1.2 := not_ne_iff.mp p.2
    simp [hEq]
  rw [hdiag, add_zero, Fintype.sum_prod_type] at hsplit
  calc
    (∑ e : Edge V, g.ofLp e * star (f.ofLp e)) =
        ∑ e : Edge V,
          edgeMatrix (V := V) g e.1.1 e.1.2 *
            star (edgeMatrix (V := V) f e.1.1 e.1.2) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [edgeMatrix_offdiag (V := V) g e.2,
          edgeMatrix_offdiag (V := V) f e.2]
    _ = ∑ i : V, ∑ j : V,
          edgeMatrix (V := V) g i j *
            star (edgeMatrix (V := V) f i j) := hsplit

/-- E1 / Lemma 7.1 (Gradient--Divergence Adjointness):
with the standard Hermitian products on `D_N^0` and directed-edge space,
`div` is adjoint to the diagonal gradient.
@isnad1 id=eq.0h3v.s13.22d99f02633e from=translated src=- shape=beabf8c1 vocab=d9493b77
-/
theorem gradient_divergence_adjoint
    (f : EdgeSpace V) (d : DiagZero (V := V)) :
    inner ℂ (divergence (V := V) f) d =
      inner ℂ f (gradient (V := V) d) := by
  rw [Submodule.coe_inner]
  rw [PiLp.inner_apply]
  simp_rw [RCLike.inner_apply, divergence_apply]
  rw [edge_inner_eq_double_sum (V := V)]
  simp_rw [edgeMatrix_gradient_apply]

  simp_rw [map_sub, map_sum]
  simp_rw [mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib]

  have hswap :
      (∑ i : V, ∑ j : V,
        d.1.ofLp i * (starRingEnd ℂ) (edgeMatrix (V := V) f j i)) =
      (∑ i : V, ∑ j : V,
        d.1.ofLp j * (starRingEnd ℂ) (edgeMatrix (V := V) f i j)) := by
    exact Finset.sum_comm

  rw [hswap]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rfl

/-! ## E2: Stabilizer Duality (Theorem 7.2) -/

/-- Native-module realization of the orthogonal complement of `R_k`.

This is exactly the condition `d ∈ R_k^\perp`, written directly on the
native `DiagZero` module structure.-/
def residueOrthogonal
    (φ : Dynamics V) (k : ℕ) :
    Submodule ℂ (DiagZero (V := V)) where
  carrier :=
    {d | ∀ r, r ∈ residue φ k → inner ℂ r d = 0}
  zero_mem' := by
    intro r hr
    simp
  add_mem' := by
    intro d₁ d₂ hd₁ hd₂ r hr
    simp [hd₁ r hr, hd₂ r hr]
  smul_mem' := by
    intro c d hd r hr
    simp [hd r hr]

/--
@isnad1 id=iff.0h4v.s13.1ec0c4fd6efc from=translated src=- shape=4d0de308 vocab=ac1177bd
-/
@[simp]
theorem mem_residueOrthogonal
    (φ : Dynamics V) (k : ℕ) (d : DiagZero (V := V)) :
    d ∈ residueOrthogonal (V := V) φ k ↔
      ∀ r ∈ residue φ k, inner ℂ r d = 0 := by
  rfl

/-- Native-module definition of the hidden-flow stabilizer:
`d` stabilizes depth `k` iff its gradient is orthogonal to every hidden flow.-/
def stabilizer
    (φ : Dynamics V) (k : ℕ) :
    Submodule ℂ (DiagZero (V := V)) where
  carrier :=
    {d | ∀ f, f ∈ hiddenFlow φ k →
      inner ℂ f (gradient (V := V) d) = 0}
  zero_mem' := by
    intro f hf
    simp
  add_mem' := by
    intro d₁ d₂ hd₁ hd₂ f hf
    rw [gradient_add (V := V)]
    simp [hd₁ f hf, hd₂ f hf]
  smul_mem' := by
    intro c d hd f hf
    rw [gradient_smul (V := V)]
    simp [hd f hf]

/--
@isnad1 id=iff.0h4v.s12.cfd7c7ef39fc from=translated src=- shape=0e4aa0f6 vocab=6399eb24
-/
@[simp]
theorem mem_stabilizer
    (φ : Dynamics V) (k : ℕ) (d : DiagZero (V := V)) :
    d ∈ stabilizer (V := V) φ k ↔
      ∀ f ∈ hiddenFlow φ k,
        inner ℂ f (gradient (V := V) d) = 0 := by
  rfl

/-- E2 / Theorem 7.2 (Stabilizer Duality):
the native realization of `R_k^\perp` equals the hidden-flow stabilizer.
@isnad1 id=eq.0h3v.s8.164c6feac875 from=translated src=- shape=8ea88ef0 vocab=46a0bea2
-/
theorem residueOrthogonal_eq_stabilizer
    (φ : Dynamics V) (k : ℕ) :
    residueOrthogonal (V := V) φ k =
      stabilizer (V := V) φ k := by
  ext d
  rw [mem_residueOrthogonal, mem_stabilizer]
  constructor
  · intro hd f hf
    have hdiv : divergence (V := V) f ∈ residue φ k := by
      rw [residue_eq_map_divergence (V := V) φ k]
      exact ⟨f, hf, rfl⟩
    have hzero :
        inner ℂ (divergence (V := V) f) d = 0 :=
      hd (divergence (V := V) f) hdiv
    rw [gradient_divergence_adjoint (V := V) f d] at hzero
    exact hzero
  · intro hd r hr
    rw [residue_eq_map_divergence (V := V) φ k] at hr
    rcases hr with ⟨f, hf, rfl⟩
    have hzero :
        inner ℂ f (gradient (V := V) d) = 0 :=
      hd f hf
    rw [← gradient_divergence_adjoint (V := V) f d] at hzero
    exact hzero

end Stabilizer

end P3
