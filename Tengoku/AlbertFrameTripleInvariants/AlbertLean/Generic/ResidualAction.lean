import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ExteriorAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CubicAutomorphismSource
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.SL4PairAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual residual determinant-one action on the source Albert algebra

For the literal source decomposition

`J = K³ ⊕ (K ⊕ K ⊕ Λ²U) ⊕ (U ⊕ U*) ⊕ (U ⊕ U*)`,

a residual matrix `g` acts by `g` on the two `U` slots, by the specified
inverse on the two row-covector slots, and by `Λ²g` on the six-coordinate
exterior slot.  The diagonal coordinates and the two scalar coordinates in
the vector slot are fixed.  This is the action with the convention
`X ↦ gX`, `A ↦ A gInv`.

The source norm and unit are preserved by calculation.  Preservation of the
Springer product is then derived from the source recovery theorem; it is not
included as an assumption on the action.
-/

noncomputable section

namespace AlbertLean.Generic.ResidualAction

open Matrix
open AlbertLean.CubicNorm
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Generic.ExteriorAction
open AlbertLean.Generic.CubicAutomorphism

variable {K : Type*} [Field K] [CharZero K]

/-- The vector, or `K ⊕ K ⊕ Λ²U`, part of the residual action.-/
def actV (G : DetOneMatrix K) (v : VCoord K) : VCoord K :=
  { r := v.r
    z := v.z
    omega := wedgeAct G.g v.omega }

/-- The first half-spin part.  Covectors are rows and therefore multiply the
specified inverse on the right.-/
def actS (G : DetOneMatrix K) (s : SCoord K) : SCoord K :=
  { p := vecAct G.g s.p
    phi := covAct G.gInv s.phi }

/-- The second half-spin part, in the same source convention.-/
def actC (G : DetOneMatrix K) (c : CCoord K) : CCoord K :=
  { q := vecAct G.g c.q
    psi := covAct G.gInv c.psi }

/-- The residual action on all 27 structured source coordinates.-/
def act (G : DetOneMatrix K) (x : JCoord K) : JCoord K :=
  { d1 := x.d1
    d2 := x.d2
    d3 := x.d3
    v := actV G x.v
    s := actS G x.s
    c := actC G x.c }

/--
@isnad1 id=eq.0h4v.s6.232a5c24f6d5 from=translated src=- shape=32dc06b7 vocab=388af42b
-/
theorem actV_add (G : DetOneMatrix K) (v w : VCoord K) :
    actV G (v + w) = actV G v + actV G w := by
  apply VCoord.ext <;> simp [actV, wedgeAct_add]

/--
@isnad1 id=eq.0h4v.s6.c0fd78ee2a7e from=translated src=- shape=32dc06b7 vocab=575f6290
-/
theorem actS_add (G : DetOneMatrix K) (s t : SCoord K) :
    actS G (s + t) = actS G s + actS G t := by
  apply SCoord.ext <;>
    simp [actS, vecAct, covAct, Matrix.mulVec_add, Matrix.add_vecMul]

/--
@isnad1 id=eq.0h4v.s6.55dd57d9831c from=translated src=- shape=32dc06b7 vocab=d3742414
-/
theorem actC_add (G : DetOneMatrix K) (c d : CCoord K) :
    actC G (c + d) = actC G c + actC G d := by
  apply CCoord.ext <;>
    simp [actC, vecAct, covAct, Matrix.mulVec_add, Matrix.add_vecMul]

/--
@isnad1 id=eq.0h4v.s8.2667b95f4bd9 from=translated src=- shape=a42e882b vocab=5e5ac96d
-/
theorem actV_smul (G : DetOneMatrix K) (a : K) (v : VCoord K) :
    actV G (a • v) = a • actV G v := by
  apply VCoord.ext <;> simp [actV, wedgeAct_smul]

/--
@isnad1 id=eq.0h4v.s8.0c1ba41fcf68 from=translated src=- shape=a42e882b vocab=756d0d1d
-/
theorem actS_smul (G : DetOneMatrix K) (a : K) (s : SCoord K) :
    actS G (a • s) = a • actS G s := by
  apply SCoord.ext <;>
    simp [actS, vecAct, covAct, Matrix.mulVec_smul, Matrix.smul_vecMul]

/--
@isnad1 id=eq.0h4v.s8.8f1a3410d644 from=translated src=- shape=a42e882b vocab=ef7dbfb4
-/
theorem actC_smul (G : DetOneMatrix K) (a : K) (c : CCoord K) :
    actC G (a • c) = a • actC G c := by
  apply CCoord.ext <;>
    simp [actC, vecAct, covAct, Matrix.mulVec_smul, Matrix.smul_vecMul]

/--
@isnad1 id=eq.0h4v.s6.673d6cc794d5 from=translated src=- shape=32dc06b7 vocab=c6c589dd
-/
theorem act_add (G : DetOneMatrix K) (x y : JCoord K) :
    act G (x + y) = act G x + act G y := by
  apply JCoord.ext <;> simp [act, actV_add, actS_add, actC_add]

/--
@isnad1 id=eq.0h4v.s8.5cc1da2b45be from=translated src=- shape=a42e882b vocab=97bace7e
-/
theorem act_smul (G : DetOneMatrix K) (a : K) (x : JCoord K) :
    act G (a • x) = a • act G x := by
  apply JCoord.ext <;> simp [act, actV_smul, actS_smul, actC_smul]

/-- The same determinant-one datum with the specified inverse exchanged.-/
def inverse (G : DetOneMatrix K) : DetOneMatrix K where
  g := G.gInv
  gInv := G.g
  g_mul_gInv := G.gInv_mul_g
  gInv_mul_g := G.g_mul_gInv
  det_g := G.det_gInv

/--
@isnad1 id=eq.0h3v.s5.2e1646de4c34 from=translated src=- shape=1918101c vocab=2c455776
-/
theorem actV_inverse_left (G : DetOneMatrix K) (v : VCoord K) :
    actV (inverse G) (actV G v) = v := by
  apply VCoord.ext
  · rfl
  · rfl
  · simp [actV, inverse, wedgeAct_mul, G.gInv_mul_g]

/--
@isnad1 id=eq.0h3v.s5.c7a25c187faa from=translated src=- shape=1918101c vocab=3c351042
-/
theorem actS_inverse_left (G : DetOneMatrix K) (s : SCoord K) :
    actS (inverse G) (actS G s) = s := by
  apply SCoord.ext <;>
    simp [actS, inverse, vecAct, covAct, Matrix.mulVec_mulVec,
      Matrix.vecMul_vecMul, G.gInv_mul_g]

/--
@isnad1 id=eq.0h3v.s5.80c498cd5325 from=translated src=- shape=1918101c vocab=428cd2f4
-/
theorem actC_inverse_left (G : DetOneMatrix K) (c : CCoord K) :
    actC (inverse G) (actC G c) = c := by
  apply CCoord.ext <;>
    simp [actC, inverse, vecAct, covAct, Matrix.mulVec_mulVec,
      Matrix.vecMul_vecMul, G.gInv_mul_g]

/-- Applying the specified inverse action on the left recovers the source
coordinate.
@isnad1 id=eq.0h3v.s5.0eec057bc2e9 from=translated src=- shape=1918101c vocab=8c1c2022
-/
theorem act_inverse_left (G : DetOneMatrix K) (x : JCoord K) :
    act (inverse G) (act G x) = x := by
  exact JCoord.ext rfl rfl rfl (actV_inverse_left G x.v)
    (actS_inverse_left G x.s) (actC_inverse_left G x.c)

/--
@isnad1 id=eq.0h3v.s5.5e88a8428516 from=translated src=- shape=f1712121 vocab=2c455776
-/
theorem actV_inverse_right (G : DetOneMatrix K) (v : VCoord K) :
    actV G (actV (inverse G) v) = v := by
  apply VCoord.ext
  · rfl
  · rfl
  · simp [actV, inverse, wedgeAct_mul, G.g_mul_gInv]

/--
@isnad1 id=eq.0h3v.s5.61cb681f8d5a from=translated src=- shape=f1712121 vocab=3c351042
-/
theorem actS_inverse_right (G : DetOneMatrix K) (s : SCoord K) :
    actS G (actS (inverse G) s) = s := by
  apply SCoord.ext <;>
    simp [actS, inverse, vecAct, covAct, Matrix.mulVec_mulVec,
      Matrix.vecMul_vecMul, G.g_mul_gInv]

/--
@isnad1 id=eq.0h3v.s5.eb1abd8693e8 from=translated src=- shape=f1712121 vocab=428cd2f4
-/
theorem actC_inverse_right (G : DetOneMatrix K) (c : CCoord K) :
    actC G (actC (inverse G) c) = c := by
  apply CCoord.ext <;>
    simp [actC, inverse, vecAct, covAct, Matrix.mulVec_mulVec,
      Matrix.vecMul_vecMul, G.g_mul_gInv]

/-- Applying the specified inverse action on the right recovers the source
coordinate.
@isnad1 id=eq.0h3v.s5.227d2ec2c748 from=translated src=- shape=f1712121 vocab=8c1c2022
-/
theorem act_inverse_right (G : DetOneMatrix K) (x : JCoord K) :
    act G (act (inverse G) x) = x := by
  exact JCoord.ext rfl rfl rfl (actV_inverse_right G x.v)
    (actS_inverse_right G x.s) (actC_inverse_right G x.c)

/-- The residual action as a rational-linear equivalence (and, more
generally, as a `K`-linear equivalence in characteristic zero).-/
def linearEquiv (G : DetOneMatrix K) : JCoord K ≃ₗ[K] JCoord K where
  toFun := act G
  invFun := act (inverse G)
  left_inv := act_inverse_left G
  right_inv := act_inverse_right G
  map_add' := act_add G
  map_smul' := act_smul G

/--
@isnad1 id=eq.0h3v.s8.7cf213a937d0 from=translated src=- shape=d84fc4b9 vocab=4d663abd
-/
@[simp] theorem linearEquiv_apply (G : DetOneMatrix K) (x : JCoord K) :
    linearEquiv G x = act G x := rfl

/-- Ordinary vector/covector evaluation is invariant.
@isnad1 id=eq.0h4v.s5.e2507c3889fe from=translated src=- shape=1f034552 vocab=10971cda
-/
theorem eval_act (G : DetOneMatrix K) (phi : Udual K) (p : U K) :
    evalU (covAct G.gInv phi) (vecAct G.g p) = evalU phi p :=
  evalU_covAct_vecAct G.g G.gInv G.gInv_mul_g phi p

/--
@isnad1 id=eq.0h3v.s5.f44e53828cc5 from=translated src=- shape=90f6c1f5 vocab=7ca0b0f5
-/
theorem nV_actV (G : DetOneMatrix K) (v : VCoord K) :
    nV (actV G v) = nV v := by
  simp only [nV, actV]
  unfold Pf
  rw [BW_wedgeAct_of_det_one G.g G.det_g]

/--
@isnad1 id=eq.0h4v.s5.1d42d32bc611 from=translated src=- shape=726b1277 vocab=20ec46d3
-/
theorem BV_actV (G : DetOneMatrix K) (v w : VCoord K) :
    BV (actV G v) (actV G w) = BV v w := by
  simp only [BV, actV]
  rw [BW_wedgeAct_of_det_one G.g G.det_g]

/--
@isnad1 id=eq.0h3v.s5.6ce9c1490d45 from=translated src=- shape=90f6c1f5 vocab=037052e8
-/
theorem nS_actS (G : DetOneMatrix K) (s : SCoord K) :
    nS (actS G s) = nS s := by
  exact eval_act G s.phi s.p

/--
@isnad1 id=eq.0h4v.s5.7cb7a4a6b5e0 from=translated src=- shape=726b1277 vocab=6b56d58a
-/
theorem BS_actS (G : DetOneMatrix K) (s t : SCoord K) :
    BS (actS G s) (actS G t) = BS s t := by
  simp only [BS, actS]
  rw [eval_act G, eval_act G]

/--
@isnad1 id=eq.0h3v.s5.dba61e95e493 from=translated src=- shape=90f6c1f5 vocab=89b211a4
-/
theorem nC_actC (G : DetOneMatrix K) (c : CCoord K) :
    nC (actC G c) = nC c := by
  exact eval_act G c.psi c.q

/--
@isnad1 id=eq.0h4v.s5.c38180f95112 from=translated src=- shape=726b1277 vocab=043f0d4c
-/
theorem BC_actC (G : DetOneMatrix K) (c d : CCoord K) :
    BC (actC G c) (actC G d) = BC c d := by
  simp only [BC, actC]
  rw [eval_act G, eval_act G]

/-- The four literal terms of `eq:sl4forms` are invariant in their source
order.
@isnad1 id=eq.0h5v.s5.1a9cc7a7881b from=translated src=- shape=836f1ab2 vocab=fec8bc80
-/
theorem triality_act (G : DetOneMatrix K)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (actV G v) (actS G s) (actC G c) = triality v s c := by
  simp only [triality, actV, actS, actC]
  rw [eval_act G, eval_act G]
  rw [← wedgeAct_wedge2]
  rw [BW_wedgeAct_of_det_one G.g G.det_g]
  rw [pairW_wedgeAct_dualWedge G.g G.gInv G.gInv_mul_g]

/-- The actual source cubic is invariant under every declared
determinant-one residual matrix.
@isnad1 id=eq.0h3v.s5.338dfdc7877a from=translated src=- shape=90f6c1f5 vocab=f0bd6ed1
-/
theorem sourceNorm_act (G : DetOneMatrix K) (x : JCoord K) :
    sourceNorm (act G x) = sourceNorm x := by
  simp only [sourceNorm, act]
  rw [nV_actV G, nS_actS G, nC_actC G, triality_act G]

/--
@isnad1 id=eq.0h2v.s5.6e01511b167d from=translated src=- shape=03058639 vocab=e766c12d
-/
@[simp] theorem sourceOne_act (G : DetOneMatrix K) :
    act G (sourceOne : JCoord K) = sourceOne := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext
    · rfl
    · rfl
    · exact wedgeAct_zero G.g
  · apply SCoord.ext <;> simp [act, actS, sourceOne, vecAct, covAct]
  · apply CCoord.ext <;> simp [act, actC, sourceOne, vecAct, covAct]

/--
@isnad1 id=eq.0h3v.s5.f2032415f7c2 from=translated src=- shape=90f6c1f5 vocab=2c0a184b
-/
theorem sourceTrace_act (G : DetOneMatrix K) (x : JCoord K) :
    sourceTrace (act G x) = sourceTrace x := rfl

/--
@isnad1 id=eq.0h4v.s5.5931034a16a1 from=translated src=- shape=726b1277 vocab=00ceade1
-/
theorem sourceTraceForm_act (G : DetOneMatrix K) (x y : JCoord K) :
    sourceTraceForm (act G x) (act G y) = sourceTraceForm x y := by
  rw [sourceTraceForm_formula, sourceTraceForm_formula]
  simp only [act]
  rw [BV_actV G, BS_actS G, BC_actC G]

/--
@isnad1 id=eq.0h5v.s5.4a1650d7f77d from=translated src=- shape=aa54a559 vocab=8ea70e47
-/
theorem sourcePolar_act (G : DetOneMatrix K) (x y z : JCoord K) :
    sourcePolar (act G x) (act G y) (act G z) = sourcePolar x y z := by
  have hxyz : sourceNorm (act G x + act G y + act G z) =
      sourceNorm (x + y + z) := by
    rw [← act_add G x y, ← act_add G (x + y) z, sourceNorm_act]
  have hxy : sourceNorm (act G x + act G y) = sourceNorm (x + y) := by
    rw [← act_add G x y, sourceNorm_act]
  have hxz : sourceNorm (act G x + act G z) = sourceNorm (x + z) := by
    rw [← act_add G x z, sourceNorm_act]
  have hyz : sourceNorm (act G y + act G z) = sourceNorm (y + z) := by
    rw [← act_add G y z, sourceNorm_act]
  simp only [sourcePolar, hxyz, hxy, hxz, hyz, sourceNorm_act]

/-- Product preservation is a consequence of the source cubic calculation
and trace-dual recovery.
@isnad1 id=eq.0h4v.s5.d4dc1442f9b8 from=translated src=- shape=24c60158 vocab=b37337a0
-/
theorem sourceProduct_act (G : DetOneMatrix K) (x y : JCoord K) :
    act G (sourceProduct x y) = sourceProduct (act G x) (act G y) := by
  exact sourceProduct_invariant_of_cubic_unit
    (linearEquiv G) (sourceOne_act G) (sourceNorm_act G) x y

/-- An actual unital automorphism of the structured source Albert algebra.-/
structure SourceAut where
  linear : JCoord K ≃ₗ[K] JCoord K
  map_one : linear sourceOne = sourceOne
  map_product : ∀ x y, linear (sourceProduct x y) =
    sourceProduct (linear x) (linear y)

/-- Every determinant-one residual matrix with its audited inverse gives an
actual source-Albert automorphism.-/
def sourceAut (G : DetOneMatrix K) : SourceAut (K := K) where
  linear := linearEquiv G
  map_one := sourceOne_act G
  map_product := sourceProduct_act G

/-- Composition in the determinant-one residual matrices, retaining the
specified inverse rather than choosing one nonconstructively.-/
def compose (G H : DetOneMatrix K) : DetOneMatrix K where
  g := G.g * H.g
  gInv := H.gInv * G.gInv
  g_mul_gInv := by
    calc
      (G.g * H.g) * (H.gInv * G.gInv) =
          G.g * ((H.g * H.gInv) * G.gInv) := by
            simp only [Matrix.mul_assoc]
      _ = G.g * G.gInv := by rw [H.g_mul_gInv, Matrix.one_mul]
      _ = 1 := G.g_mul_gInv
  gInv_mul_g := by
    calc
      (H.gInv * G.gInv) * (G.g * H.g) =
          H.gInv * ((G.gInv * G.g) * H.g) := by
            simp only [Matrix.mul_assoc]
      _ = H.gInv * H.g := by rw [G.gInv_mul_g, Matrix.one_mul]
      _ = 1 := H.gInv_mul_g
  det_g := by rw [Matrix.det_mul, G.det_g, H.det_g, one_mul]

/-- The source action respects residual matrix multiplication.
@isnad1 id=eq.0h4v.s5.98d44c7b8957 from=translated src=- shape=df086678 vocab=2aae3e64
-/
theorem act_compose (G H : DetOneMatrix K) (x : JCoord K) :
    act (compose G H) x = act G (act H x) := by
  apply JCoord.ext <;>
    simp [act, actV, actS, actC, compose, wedgeAct_mul,
      vecAct, covAct, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
      Matrix.mul_assoc]

/-- The induced linear equivalences obey the same composition law.
@isnad1 id=eq.0h3v.s8.8225aba18557 from=translated src=- shape=a0e5673f vocab=e45f99b4
-/
theorem linearEquiv_compose (G H : DetOneMatrix K) :
    linearEquiv (compose G H) = (linearEquiv H).trans (linearEquiv G) := by
  apply LinearEquiv.ext
  intro x
  exact act_compose G H x

end AlbertLean.Generic.ResidualAction
