import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualLedgerPower
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualMomentSubfield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms all_trialities_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms all_U_mem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Actual source Gram, triality and adjoint pairings
recovered from the literal ledger. All identities use the accepted source
product/square/tensor definitions. Nothing identifies a global invariant field.
-/

noncomputable section
namespace AlbertLean.Generic.ResidualPowerMeasurements

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Residual.TrialitySquares
open AlbertLean.Generic.ProductDiagonal
open AlbertLean.Generic.ResidualLedgerPower
open AlbertLean.Generic.ResidualMomentSubfield

variable {K : Type*} [Field K] [CharZero K]

/--
@isnad1 id=eq.0h2v.s7.7952fa2c6b39 from=translated src=- shape=a99a77e8 vocab=e5efd91f
-/
@[simp] theorem diagLinear_zero (x : JCoord K) : diagLinear 0 x = x.d1 := rfl
/--
@isnad1 id=eq.0h2v.s7.26d0a3313c87 from=translated src=- shape=a99a77e8 vocab=0b8b85c6
-/
@[simp] theorem diagLinear_one (x : JCoord K) : diagLinear 1 x = x.d2 := rfl
/--
@isnad1 id=eq.0h2v.s7.ee431c9a1c15 from=translated src=- shape=a99a77e8 vocab=db6841bc
-/
@[simp] theorem diagLinear_two (x : JCoord K) : diagLinear 2 x = x.d3 := rfl

def DiagIn (F : Subfield K) (x : JCoord K) : Prop := ∀ i, diagLinear i x ∈ F

def SectorIn (F : Subfield K) (x y : JCoord K) : Prop :=
  BV x.v y.v ∈ F ∧ BS x.s y.s ∈ F ∧ BC x.c y.c ∈ F

/--
@isnad1 id=sectorin.1h4v.s5.276f948806fb from=translated src=- shape=f55a0adf vocab=89edd46f
-/
theorem SectorIn.symm (F : Subfield K) (x y : JCoord K)
    (h : SectorIn F x y) : SectorIn F y x := by
  simpa only [SectorIn, BV_symmetric y.v x.v, BS_symmetric y.s x.s,
    BC_symmetric y.c x.c] using h

/--
@isnad1 id=sectorin.3h4v.s5.18f06db3085a from=translated src=- shape=353be7ff vocab=3f6bc405
-/
theorem sector_pairings_mem (F : Subfield K) (x y : JCoord K)
    (hx : DiagIn F x) (hy : DiagIn F y)
    (hxy : DiagIn F (sourceProduct x y)) : SectorIn F x y := by
  have h2 : (2 : K) ∈ F := natCast_mem F 2
  have pairSum (i : Fin 3) :
      2 * diagLinear i (sourceProduct x y) -
        2 * (diagLinear i x * diagLinear i y) ∈ F :=
    F.sub_mem (F.mul_mem h2 (hxy i)) (F.mul_mem h2 (F.mul_mem (hx i) (hy i)))
  have hVS : BV x.v y.v + BS x.s y.s ∈ F := by
    convert pairSum 2 using 1
    simp only [diagLinear_zero, diagLinear_one, diagLinear_two, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, sourceProduct_d3]
    ring
  have hSC : BS x.s y.s + BC x.c y.c ∈ F := by
    convert pairSum 0 using 1
    simp only [diagLinear_zero, diagLinear_one, diagLinear_two, Matrix.cons_val_zero, sourceProduct_d1]
    ring
  have hCV : BC x.c y.c + BV x.v y.v ∈ F := by
    convert pairSum 1 using 1
    simp only [diagLinear_zero, diagLinear_one, diagLinear_two, Matrix.cons_val_one, Matrix.cons_val_zero, sourceProduct_d2]
    ring
  exact triple_mem_of_pair_sums F _ _ _ hVS hSC hCV

/--
@isnad1 id=and.2h3v.s6.afc8994eb083 from=translated src=- shape=46f9cba5 vocab=1556d036
-/
theorem norms_mem (F : Subfield K) (x : JCoord K)
    (hx : DiagIn F x) (hx2 : DiagIn F (sourceSquare x)) :
    nV x.v ∈ F ∧ nS x.s ∈ F ∧ nC x.c ∈ F := by
  have pairSum (i : Fin 3) :
      diagLinear i (sourceSquare x) - diagLinear i x ^ 2 ∈ F :=
    F.sub_mem (hx2 i) (F.pow_mem (hx i) 2)
  have hVS : nV x.v + nS x.s ∈ F := by
    convert pairSum 2 using 1
    simp [diagLinear, sourceSquare_d3]
    <;> ring
  have hSC : nS x.s + nC x.c ∈ F := by
    convert pairSum 0 using 1
    simp [diagLinear, sourceSquare_d1]
    <;> ring
  have hCV : nC x.c + nV x.v ∈ F := by
    convert pairSum 1 using 1
    simp [diagLinear, sourceSquare_d2]
    <;> ring
  exact triple_mem_of_pair_sums F _ _ _ hVS hSC hCV

/--
@isnad1 id=and.1h4v.s6.3d31b5473a4c from=translated src=- shape=4eae3a30 vocab=b4397e2f
-/
theorem powers_diag_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b)) :
    (∀ p, DiagIn F (power a p)) ∧ (∀ q, DiagIn F (power b q)) := by
  constructor
  · intro p i
    simpa only [power, Matrix.cons_val_zero, sourceProduct_one_right] using
      power_diagonal_mem F a b h i p 0
  · intro q i
    simpa only [power, Matrix.cons_val_zero, sourceProduct_one_left] using
      power_diagonal_mem F a b h i 0 q

/-- All V/S/C pairings between 1,a,a² and 1,b,b² are retained.
@isnad1 id=sectorin.1h6v.s6.57a05b37eff2 from=translated src=- shape=4020efb8 vocab=863bbdb6
-/
theorem power_sectors_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b)) (p q : Fin 3) :
    SectorIn F (power a p) (power b q) :=
  sector_pairings_mem F _ _ ((powers_diag_mem F a b h).1 p)
    ((powers_diag_mem F a b h).2 q)
    (fun i => power_diagonal_mem F a b h i p q)

/-- The three adjoint contractions are exactly the same accepted triality.
@isnad1 id=eq.0h4v.s5.e9468e0b5535 from=translated src=- shape=bc94dd4f vocab=43d37d41
-/
theorem muV_triality (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    BV (normalizedMuV s c) v = triality v s c := by
  simp [normalizedMuV, muV, BV, BW, pairW, triality,
    evalU, wedge2, dualWedge2, hodgeStar]
  ring

/--
@isnad1 id=eq.0h4v.s5.344c01a4835f from=translated src=- shape=28d2e186 vocab=9ca16103
-/
theorem muS_triality (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    BS (sourceMuS c v) s = triality v s c := by
  simp [sourceMuS, BS, triality, evalU, BW, pairW, wedge2, dualWedge2]
  ring

/--
@isnad1 id=eq.0h4v.s5.4c889ec9a5d8 from=translated src=- shape=7a83b3b1 vocab=7b5805cc
-/
theorem muC_triality (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    BC (sourceMuC v s) c = triality v s c := by
  simp [sourceMuC, BC, triality, evalU, BW, pairW, wedge2, dualWedge2]
  ring

/--
@isnad1 id=and.3h4v.s7.11fbec7cab81 from=translated src=- shape=8dafab29 vocab=ab67b01c
-/
theorem mixed_trialities_mem (F : Subfield K) (x y : JCoord K)
    (hx : DiagIn F x) (hxy : SectorIn F x y)
    (hx2y : SectorIn F (sourceSquare x) y) :
    triality y.v x.s x.c ∈ F ∧ triality x.v y.s x.c ∈ F ∧
      triality x.v x.s y.c ∈ F := by
  have hv := hx2y.1
  rw [sourceSquare_v, BV_add_left, BV_smul_left, muV_triality] at hv
  have hs := hx2y.2.1
  rw [sourceSquare_s, BS_add_left, BS_smul_left, muS_triality] at hs
  have hc := hx2y.2.2
  rw [sourceSquare_c, BC_add_left, BC_smul_left, muC_triality] at hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [diagLinear_zero, diagLinear_one, diagLinear_two, add_sub_cancel_left] using
      F.sub_mem hv (F.mul_mem (F.add_mem (hx 1) (hx 2)) hxy.1)
  · simpa only [diagLinear_zero, diagLinear_one, diagLinear_two, add_sub_cancel_left] using
      F.sub_mem hs (F.mul_mem (F.add_mem (hx 0) (hx 2)) hxy.2.1)
  · simpa only [diagLinear_zero, diagLinear_one, diagLinear_two, add_sub_cancel_left] using
      F.sub_mem hc (F.mul_mem (F.add_mem (hx 0) (hx 1)) hxy.2.2)

/--
@isnad1 id=mem.3h3v.s7.040c634ca5ec from=translated src=- shape=b51bc5c2 vocab=0f3cec20
-/
theorem single_triality_mem (F : Subfield K) (x : JCoord K)
    (hx : DiagIn F x) (hn : nV x.v ∈ F ∧ nS x.s ∈ F ∧ nC x.c ∈ F)
    (hN : sourceNorm x = 0) : triality x.v x.s x.c ∈ F := by
  have hformula : triality x.v x.s x.c =
      x.d1 * nV x.v + x.d2 * nS x.s + x.d3 * nC x.c -
        x.d1 * x.d2 * x.d3 := by
    dsimp only [sourceNorm] at hN
    linear_combination hN
  rw [hformula]
  exact F.sub_mem
    (F.add_mem (F.add_mem (F.mul_mem (hx 0) hn.1)
      (F.mul_mem (hx 1) hn.2.1)) (F.mul_mem (hx 2) hn.2.2))
    (F.mul_mem (F.mul_mem (hx 0) (hx 1)) (hx 2))

/-- The ledger and the two actual norm-zero frame equations recover every
mixed triality. No generic-field-generation premise occurs.
@isnad1 id=mem.3h7v.s7.527e0c358111 from=translated src=- shape=babdd29c vocab=8b97c4c0
-/
theorem all_trialities_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b))
    (hNa : sourceNorm a = 0) (hNb : sourceNorm b = 0) :
    ∀ i j l : Fin 2, triality (![a.v, b.v] i) (![a.s, b.s] j)
      (![a.c, b.c] l) ∈ F := by
  have hd := powers_diag_mem F a b h
  have ha : DiagIn F a := hd.1 1
  have hb : DiagIn F b := hd.2 1
  have hab : SectorIn F a b := power_sectors_mem F a b h 1 1
  have hab3 := mixed_trialities_mem F a b ha hab (power_sectors_mem F a b h 2 1)
  have hba3 := mixed_trialities_mem F b a hb (SectorIn.symm F a b hab)
    (SectorIn.symm F a (sourceSquare b) (power_sectors_mem F a b h 1 2))
  have haa := single_triality_mem F a ha (norms_mem F a ha (hd.1 2)) hNa
  have hbb := single_triality_mem F b hb (norms_mem F b hb (hd.2 2)) hNb
  intro i j l
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals first
    | exact haa | exact hbb
    | exact hab3.1 | exact hab3.2.1 | exact hab3.2.2
    | exact hba3.1 | exact hba3.2.1 | exact hba3.2.2

def lV (x : JCoord K) : K := x.d2 + x.d3
def lS (x : JCoord K) : K := x.d1 + x.d3
def lC (x : JCoord K) : K := x.d1 + x.d2

/--
@isnad1 id=eq.0h3v.s7.fb2aefb40f32 from=translated src=- shape=e9118383 vocab=e453c3bc
-/
theorem uV_centered (a b : JCoord K) :
    normalizedUV a.s b.s a.c b.c =
      BV (sourceSquare a).v (sourceSquare b).v -
      lV a * BV a.v (sourceSquare b).v -
      lV b * BV (sourceSquare a).v b.v + lV a * lV b * BV a.v b.v := by
  simp only [normalizedUV, sourceSquare_v, BV_add_left, BV_add_right,
    BV_smul_left, BV_smul_right, lV]
  ring

/--
@isnad1 id=eq.0h3v.s7.f7e0381d1038 from=translated src=- shape=3ccc1e98 vocab=a87180a5
-/
theorem uS_centered (a b : JCoord K) :
    BS (sourceMuS a.c a.v) (sourceMuS b.c b.v) =
      BS (sourceSquare a).s (sourceSquare b).s -
      lS a * BS a.s (sourceSquare b).s -
      lS b * BS (sourceSquare a).s b.s + lS a * lS b * BS a.s b.s := by
  simp only [sourceSquare_s, BS_add_left, BS_add_right,
    BS_smul_left, BS_smul_right, lS]
  ring

/--
@isnad1 id=eq.0h3v.s7.20ff220e2f30 from=translated src=- shape=3ccc1e98 vocab=c62f3648
-/
theorem uC_centered (a b : JCoord K) :
    BC (sourceMuC a.v a.s) (sourceMuC b.v b.s) =
      BC (sourceSquare a).c (sourceSquare b).c -
      lC a * BC a.c (sourceSquare b).c -
      lC b * BC (sourceSquare a).c b.c + lC a * lC b * BC a.c b.c := by
  simp only [sourceSquare_c, BC_add_left, BC_add_right,
    BC_smul_left, BC_smul_right, lC]
  ring

/-- A single closure calculation handles all three centered U formulas.
@isnad1 id=mem.6h8v.s8.f9fe7afdb0f9 from=translated src=- shape=1bd68626 vocab=1569072e
-/
theorem centered_mem (F : Subfield K) (la lb g11 g12 g21 g22 : K)
    (hla : la ∈ F) (hlb : lb ∈ F) (h11 : g11 ∈ F)
    (h12 : g12 ∈ F) (h21 : g21 ∈ F) (h22 : g22 ∈ F) :
    g22 - la * g12 - lb * g21 + la * lb * g11 ∈ F :=
  F.add_mem (F.sub_mem (F.sub_mem h22 (F.mul_mem hla h12)) (F.mul_mem hlb h21))
    (F.mul_mem (F.mul_mem hla hlb) h11)

/--
@isnad1 id=and.1h4v.s7.844fdc6174d3 from=translated src=- shape=0d8dbd30 vocab=3c5893b6
-/
theorem all_U_mem (F : Subfield K) (a b : JCoord K)
    (h : LedgerIn F (sourceLedger a b)) :
    normalizedUV a.s b.s a.c b.c ∈ F ∧
      BS (sourceMuS a.c a.v) (sourceMuS b.c b.v) ∈ F ∧
      BC (sourceMuC a.v a.s) (sourceMuC b.v b.s) ∈ F := by
  have hd := powers_diag_mem F a b h
  have ha : DiagIn F a := hd.1 1
  have hb : DiagIn F b := hd.2 1
  have h11 : SectorIn F a b := power_sectors_mem F a b h 1 1
  have h12 : SectorIn F a (sourceSquare b) := power_sectors_mem F a b h 1 2
  have h21 : SectorIn F (sourceSquare a) b := power_sectors_mem F a b h 2 1
  have h22 : SectorIn F (sourceSquare a) (sourceSquare b) := power_sectors_mem F a b h 2 2
  rw [uV_centered, uS_centered, uC_centered]
  refine ⟨?_, ?_, ?_⟩
  · exact centered_mem F _ _ _ _ _ _ (F.add_mem (ha 1) (ha 2))
      (F.add_mem (hb 1) (hb 2)) h11.1 h12.1 h21.1 h22.1
  · exact centered_mem F _ _ _ _ _ _ (F.add_mem (ha 0) (ha 2))
      (F.add_mem (hb 0) (hb 2)) h11.2.1 h12.2.1 h21.2.1 h22.2.1
  · exact centered_mem F _ _ _ _ _ _ (F.add_mem (ha 0) (ha 1))
      (F.add_mem (hb 0) (hb 1)) h11.2.2 h12.2.2 h21.2.2 h22.2.2

end AlbertLean.Generic.ResidualPowerMeasurements
