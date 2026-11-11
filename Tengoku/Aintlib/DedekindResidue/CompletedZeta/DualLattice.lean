/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The dual lattice of a ℤ-lattice  (SP1-AGP, leaf P.1)

The first substrate brick for `n`-dimensional Poisson summation. Mathlib has the *set-level*
dual of a submodule with respect to a bilinear form (`LinearMap.BilinForm.dualSubmodule`) and
the structural identity `dualSubmodule_span_of_basis` (the dual of a lattice is spanned by the
dual basis), but **nothing** connecting it to `IsZLattice` / `ZLattice.covolume`. Here we
specialise it to the inner-product bilinear form `innerₗ V` of a finite-dimensional real inner
product space and record the foundational API.

## Main definitions / results (this file)
* `DedekindResidue.dualZLattice L` — the dual lattice `L♯ = {y | ∀ x ∈ L, ⟪y, x⟫ ∈ ℤ}`.
* `DedekindResidue.mem_dualZLattice` — its membership characterisation.
* `DedekindResidue.innerₗ_nondegenerate` — the inner-product bilinear form is nondegenerate.
* `DedekindResidue.dualZLattice_eq_span` — `L♯ = span ℤ (dual basis)`; the structural lever that
  makes `L♯` a ℤ-lattice (via `instIsZLatticeRealSpan`) and feeds the covolume reciprocal.

## Next targets (SP1-AGP, tracked in `.mathlib-quality/tickets.md`)
* `IsZLattice ℝ (dualZLattice L)` + `DiscreteTopology (dualZLattice L)` — from
  `dualZLattice_eq_span` + `instIsZLatticeRealSpan` (transport across the proved carrier
  equality; both are `Prop`-classes).
* the **covolume reciprocal** `covolume (dualZLattice L) * covolume L = 1` — via
  `dualZLattice_eq_span` + `ZLattice.covolume_eq_det` and the fact that the dual-basis matrix is
  `(Bᵀ)⁻¹` (so its determinant is `(det B)⁻¹`).

See `.mathlib-quality/substrate-api.md` for the verified mathlib footholds.
-/

namespace DedekindResidue

@[expose] public section

open LinearMap.BilinForm MeasureTheory Matrix
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The inner-product bilinear form `innerₗ V` of a real inner product space is nondegenerate:
if `⟪x, ·⟫ ≡ 0` then `x = 0` (and symmetrically). Both separating conditions reduce, by
symmetry, to `⟪x, x⟫ = 0 → x = 0`.
@isnad1 id=nondegen.0h1v.s5.d9c93d2789d4 from=translated src=- shape=4843e1e4 vocab=39c774f3
-/
theorem innerₗ_nondegenerate : Nondegenerate (innerₗ V) :=
  ⟨fun x hx => inner_self_eq_zero.mp (by have h := hx x; rwa [innerₗ_apply_apply] at h),
   fun x hx => inner_self_eq_zero.mp (by have h := hx x; rwa [innerₗ_apply_apply] at h)⟩

/-- The **dual lattice** `L♯` of `L` in a finite-dimensional real inner product space:
`L♯ = {y | ∀ x ∈ L, ⟪y, x⟫ ∈ ℤ}`, built from the inner-product bilinear form.-/
noncomputable def dualZLattice (L : Submodule ℤ V) : Submodule ℤ V :=
  dualSubmodule (innerₗ V) L

omit [FiniteDimensional ℝ V] in
/-- Membership in the dual lattice: `y ∈ L♯ ↔ ⟪y, x⟫` (as `innerₗ V y x`) is an integer for
every `x ∈ L`.
@isnad1 id=iff.0h3v.s9.e6d7231c3578 from=translated src=- shape=42fb86c2 vocab=a670d2b2
-/
theorem mem_dualZLattice {L : Submodule ℤ V} {y : V} :
    y ∈ dualZLattice L ↔ ∀ x ∈ L, innerₗ V y x ∈ (1 : Submodule ℤ ℝ) :=
  Iff.rfl

/-- **Structural characterisation.** For a ℤ-lattice `L` with ℤ-basis `b`, the dual lattice is
the ℤ-span of the (bilinear-form) dual of the associated real basis. This exhibits `L♯` as the
span of a basis' range, hence as a ℤ-lattice, and is the entry point to the covolume reciprocal.
@isnad1 id=eq.0h4v.s8.29aa5dda8f2f from=translated src=- shape=30b082ff vocab=3db627e5
-/
theorem dualZLattice_eq_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) :
    dualZLattice L =
      Submodule.span ℤ (Set.range (dualBasis (innerₗ V) innerₗ_nondegenerate
        (b.ofZLatticeBasis ℝ))) := by
  unfold dualZLattice
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate (b.ofZLatticeBasis ℝ)

/-- The dual of a ℤ-lattice is discrete: it is the span of the dual basis' range.
@isnad1 id=discrete.0h2v.s8.1aa4f52e9fd2 from=translated src=- shape=04a82a48 vocab=3c55255b
-/
instance instDiscreteTopologyDualZLattice (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : DiscreteTopology (dualZLattice L) := by
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  rw [dualZLattice_eq_span L (Module.Free.chooseBasis ℤ L)]
  infer_instance

/-- The dual of a ℤ-lattice is again a ℤ-lattice: the dual basis spans `V` over `ℝ`.
@isnad1 id=iszlatti.0h2v.s7.74f6c7a90fee from=translated src=- shape=0db6aa9d vocab=3c55255b
-/
instance instIsZLatticeDualZLattice (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    IsZLattice ℝ (dualZLattice L) where
  span_top := by
    classical
    have := ZLattice.module_finite ℝ L
    have := ZLattice.module_free ℝ L
    rw [dualZLattice_eq_span L (Module.Free.chooseBasis ℤ L)]
    exact ZSpan.span_top _

/-- The fundamental domain of an orthonormal basis of Euclidean space has volume `1`.
@isnad1 id=eq.0h2v.s8.a7f426a93d55 from=translated src=- shape=89df0c1d vocab=7b9dd0c9
-/
theorem volumeReal_fundamentalDomain_orthonormal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (volume : Measure (EuclideanSpace ℝ ι)).real (ZSpan.fundamentalDomain b.toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b.toBasis volume),
    measureReal_def, ← OrthonormalBasis.addHaar_eq_volume b, Module.Basis.addHaar_self,
    ENNReal.toReal_one]

/-- **Covolume reciprocal** (SP1-AGP P.1): the dual lattice has reciprocal covolume,
`covolume L♯ · covolume L = 1`, in Euclidean space with its canonical volume. This is the
metric heart of the dual lattice and supplies the `√|discr|` in the theta functional equation.
@isnad1 id=eq.0h2v.s9.e2df34d52d4a from=translated src=- shape=4b70e300 vocab=52009d48
-/
theorem covolume_dualZLattice_mul {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (dualZLattice L) * ZLattice.covolume L = 1 := by
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥L) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, finrank_euclideanSpace]
  set b : Module.Basis ι ℤ ↥L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard) with hb
  set b₀ := EuclideanSpace.basisFun ι ℝ with hb₀
  set c : Module.Basis ι ℝ (EuclideanSpace ℝ ι) := b.ofZLatticeBasis ℝ with hc
  set cstar := dualBasis (innerₗ (EuclideanSpace ℝ ι)) innerₗ_nondegenerate c with hcstar
  have hlinind : LinearIndependent ℤ ⇑cstar :=
    cstar.linearIndependent.restrict_scalars (by simpa using Int.cast_injective)
  -- Each covolume is the coordinate determinant in the (orthonormal) standard basis `b₀`.
  have hcb : (Subtype.val ∘ ⇑b) = ⇑c := by ext i; simp [hc]
  have hcbs : (Subtype.val ∘ ⇑(Module.Basis.span hlinind)) = ⇑cstar := by ext i; simp
  have hcovL : ZLattice.covolume L
      = |b₀.toBasis.det ⇑c| * (volume : Measure (EuclideanSpace ℝ ι)).real
          (ZSpan.fundamentalDomain b₀.toBasis) := by
    rw [ZLattice.covolume_eq_det_mul_measureReal (μ := volume) (b := b) (b₀ := b₀.toBasis), hcb]
  have hcovLstar : ZLattice.covolume (dualZLattice L)
      = |b₀.toBasis.det ⇑cstar| * (volume : Measure (EuclideanSpace ℝ ι)).real
          (ZSpan.fundamentalDomain b₀.toBasis) := by
    rw [dualZLattice_eq_span L b, ← hc, ← hcstar,
      ZLattice.covolume_eq_det_mul_measureReal (μ := volume)
        (b := Module.Basis.span hlinind) (b₀ := b₀.toBasis), hcbs]
  -- Coordinate-matrix entries are inner products with the (orthonormal) `b₀`.
  have hP : ∀ (v : Module.Basis ι ℝ (EuclideanSpace ℝ ι)) (m k : ι),
      b₀.toBasis.toMatrix ⇑v k m = ⟪b₀ k, v m⟫ := fun v m k => by
    rw [Module.Basis.toMatrix_apply, b₀.coe_toBasis_repr_apply, b₀.repr_apply_apply]
  -- The mixed Gram matrix `Pᵀ Q` of the primal / dual coordinate matrices is the identity.
  have hmat : (b₀.toBasis.toMatrix ⇑c)ᵀ * b₀.toBasis.toMatrix ⇑cstar = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, hP]
    have hpar : ∑ k, ⟪b₀ k, c i⟫ * ⟪b₀ k, cstar j⟫ = ⟪c i, cstar j⟫ := by
      rw [← b₀.sum_inner_mul_inner (c i) (cstar j)]
      exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm (c i) (b₀ k)]
    rw [hpar, hcstar, real_inner_comm, ← innerₗ_apply_apply,
      apply_dualBasis_left innerₗ_nondegenerate c j i]
  have hdet : b₀.toBasis.det ⇑c * b₀.toBasis.det ⇑cstar = 1 := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply,
      ← Matrix.det_transpose (b₀.toBasis.toMatrix ⇑c), ← Matrix.det_mul, hmat, Matrix.det_one]
  rw [hcovLstar, hcovL, volumeReal_fundamentalDomain_orthonormal, mul_one, mul_one,
    ← abs_mul, mul_comm (b₀.toBasis.det ⇑cstar) (b₀.toBasis.det ⇑c), hdet, abs_one]

/-- **Rigidity**: a sub-`ℤ`-lattice of equal covolume is the whole lattice (the relative
index is `covol L'/covol L = 1`).-/
theorem eq_of_le_of_covolume_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L' L : Submodule ℤ E) [DiscreteTopology L'] [IsZLattice ℝ L']
    [DiscreteTopology L] [IsZLattice ℝ L]
    (h : L' ≤ L)
    (hc : ZLattice.covolume L' volume = ZLattice.covolume L volume) : L' = L := by
  have h1 : ((L'.toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : ℝ) = 1 := by
    rw [← ZLattice.covolume_div_covolume_eq_relIndex' L' L h, hc,
      div_self (ZLattice.covolume_ne_zero L volume)]
  have h2 : L'.toAddSubgroup.relIndex L.toAddSubgroup = 1 := by exact_mod_cast h1
  have h3 : L.toAddSubgroup ≤ L'.toAddSubgroup := AddSubgroup.relIndex_eq_one.mp h2
  exact le_antisymm h (fun x hx => h3 hx)

/-- **Covolume under a linear pullback**: `covol(e⁻¹L) = |det e⁻¹|·covol L` — the
non-measure-preserving complement of `ZLattice.covolume_comap`, via the `ofZLatticeComap`
basis and `Basis.det_comp`.
@isnad1 id=eq.0h3v.s12.c802e483f2be from=translated src=- shape=dd015bef vocab=4a4b838e
-/
theorem covolume_zlattice_comap {ι : Type*} [Fintype ι] (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) volume
      = |LinearMap.det (e.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)|
        * ZLattice.covolume L volume := by
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥L) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, finrank_euclideanSpace]
  set b : Module.Basis ι ℤ ↥L :=
    (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard) with hb
  set bc : Module.Basis ι ℤ (ZLattice.comap ℝ L e.toLinearMap) :=
    Module.Basis.ofZLatticeComap ℝ L e.toLinearEquiv b with hbc
  set b₀ := (EuclideanSpace.basisFun ι ℝ) with hb₀
  have hcoe : (Subtype.val ∘ ⇑bc)
      = ⇑((e.symm : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) ∘ (Subtype.val ∘ ⇑b) := by
    funext i
    change ((bc i : EuclideanSpace ℝ ι)) = e.symm ((b i : EuclideanSpace ℝ ι))
    rw [hbc, Module.Basis.ofZLatticeComap_apply]
    rfl
  rw [ZLattice.covolume_eq_det_mul_measureReal (μ := volume) (b := bc) (b₀ := b₀.toBasis),
    ZLattice.covolume_eq_det_mul_measureReal (μ := volume) (b := b) (b₀ := b₀.toBasis),
    volumeReal_fundamentalDomain_orthonormal, mul_one, mul_one, hcoe,
    Module.Basis.det_comp, abs_mul]

end

end DedekindResidue
