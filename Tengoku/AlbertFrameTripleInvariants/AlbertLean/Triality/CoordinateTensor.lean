import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.ExteriorSix
import Tengoku.Seed.Algebra.Group.Prod
import Tengoku.Seed.Algebra.Group.TransferInstance
import Tengoku.Seed.Algebra.Module.Prod
import Tengoku.Seed.Algebra.Module.TransferInstance
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms nV_add` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BS_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BC_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trialityLinear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms triality_torus` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms triality_coefficient_BW_i13_i24` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms triality_coefficient_dual_i12` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nV_muV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms composition_iff_mul_eq_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TrialityTensorCompositionTheorem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms composition_does_not_force_normalization` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Coordinate triality tensor and composition identity

This file gives the coordinate tensor and composition identities.  It reuses the
accepted six-coordinate exterior kernel and the typed `SCoord`/`CCoord`
carriers from `ExteriorSix`.

**Source relationship.**  The definitions of `nV`, `triality`, and `muV`, and
the formula `nV_muV`, are the coordinate formulas exported from
`eq:sl4forms` and the triality-composition discussion immediately following
it.  The additive/module structures, polarizations, explicit linear-map
packaging, coefficient witnesses, and the factor non-normalization example
are supporting constructions and lemmas.  Nothing here identifies these coordinates with
an Albert algebra, a spin group, or a product model.
-/

namespace AlbertLean.Triality.CoordinateTensor

open ExteriorSix

/-- The vector coordinate slot `K × K × W`, with the exported field order.-/
@[ext]
structure VCoord (K : Type*) where
  r : K
  z : K
  omega : W K

section LinearStructures

variable {K : Type*}

private def vCoordEquiv : VCoord K ≃ K × K × W K where
  toFun v := (v.r, v.z, v.omega)
  invFun v := { r := v.1, z := v.2.1, omega := v.2.2 }
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

private def sCoordEquiv : SCoord K ≃ U K × Udual K where
  toFun s := (s.p, s.phi)
  invFun s := { p := s.1, phi := s.2 }
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

private def cCoordEquiv : CCoord K ≃ U K × Udual K where
  toFun c := (c.q, c.psi)
  invFun c := { q := c.1, psi := c.2 }
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

instance [AddCommGroup K] : AddCommGroup (VCoord K) :=
  Equiv.addCommGroup (vCoordEquiv (K := K))

instance [Semiring R] [AddCommGroup K] [Module R K] : Module R (VCoord K) :=
  (Equiv.addEquiv (vCoordEquiv (K := K))).module R

instance [AddCommGroup K] : AddCommGroup (SCoord K) :=
  Equiv.addCommGroup (sCoordEquiv (K := K))

instance [Semiring R] [AddCommGroup K] [Module R K] : Module R (SCoord K) :=
  (Equiv.addEquiv (sCoordEquiv (K := K))).module R

instance [AddCommGroup K] : AddCommGroup (CCoord K) :=
  Equiv.addCommGroup (cCoordEquiv (K := K))

instance [Semiring R] [AddCommGroup K] [Module R K] : Module R (CCoord K) :=
  (Equiv.addEquiv (cCoordEquiv (K := K))).module R

/--
@isnad1 id=eq.0h3v.s5.0a67fb9b380d from=translated src=- shape=0090f101 vocab=44cb3bd5
-/
@[simp] theorem add_r [AddCommGroup K] (v w : VCoord K) :
    (v + w).r = v.r + w.r := rfl

/--
@isnad1 id=eq.0h3v.s5.ac456a8f7e12 from=translated src=- shape=0090f101 vocab=a531eb5a
-/
@[simp] theorem add_z [AddCommGroup K] (v w : VCoord K) :
    (v + w).z = v.z + w.z := rfl

/--
@isnad1 id=eq.0h3v.s6.a4f0eaacc118 from=translated src=- shape=e69ef69b vocab=9e5b6c00
-/
@[simp] theorem add_omega [AddCommGroup K] (v w : VCoord K) :
    (v + w).omega = v.omega + w.omega := rfl

/--
@isnad1 id=eq.0h4v.s7.cb7a09eee3e8 from=translated src=- shape=4dad5650 vocab=084a26db
-/
@[simp] theorem smul_r [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (v : VCoord K) : (a • v).r = a • v.r := rfl

/--
@isnad1 id=eq.0h4v.s7.7782eb8efd3a from=translated src=- shape=4dad5650 vocab=2a0f7b5d
-/
@[simp] theorem smul_z [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (v : VCoord K) : (a • v).z = a • v.z := rfl

/--
@isnad1 id=eq.0h4v.s7.6e9b0adfe107 from=translated src=- shape=39484d90 vocab=9ebdec14
-/
@[simp] theorem smul_omega [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (v : VCoord K) : (a • v).omega = a • v.omega := rfl

/--
@isnad1 id=eq.0h3v.s6.82768442cdbe from=translated src=- shape=e69ef69b vocab=6372496e
-/
@[simp] theorem add_p [AddCommGroup K] (s t : SCoord K) :
    (s + t).p = s.p + t.p := rfl

/--
@isnad1 id=eq.0h3v.s6.a061b2a7ba6c from=translated src=- shape=e69ef69b vocab=fea57957
-/
@[simp] theorem add_phi [AddCommGroup K] (s t : SCoord K) :
    (s + t).phi = s.phi + t.phi := rfl

/--
@isnad1 id=eq.0h4v.s7.4b1690ea396e from=translated src=- shape=39484d90 vocab=54f254e9
-/
@[simp] theorem smul_p [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (s : SCoord K) : (a • s).p = a • s.p := rfl

/--
@isnad1 id=eq.0h4v.s7.1e61deb0cfd5 from=translated src=- shape=39484d90 vocab=9fcbc294
-/
@[simp] theorem smul_phi [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (s : SCoord K) : (a • s).phi = a • s.phi := rfl

/--
@isnad1 id=eq.0h3v.s6.939ff1cca932 from=translated src=- shape=e69ef69b vocab=4dc8ba0c
-/
@[simp] theorem add_q [AddCommGroup K] (c d : CCoord K) :
    (c + d).q = c.q + d.q := rfl

/--
@isnad1 id=eq.0h3v.s6.65b7adaf6d32 from=translated src=- shape=e69ef69b vocab=3107ce0d
-/
@[simp] theorem add_psi [AddCommGroup K] (c d : CCoord K) :
    (c + d).psi = c.psi + d.psi := rfl

/--
@isnad1 id=eq.0h4v.s7.72fbc87cbbea from=translated src=- shape=39484d90 vocab=8e67f717
-/
@[simp] theorem smul_q [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (c : CCoord K) : (a • c).q = a • c.q := rfl

/--
@isnad1 id=eq.0h4v.s7.767adc209fc6 from=translated src=- shape=39484d90 vocab=f948f9f9
-/
@[simp] theorem smul_psi [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (c : CCoord K) : (a • c).psi = a • c.psi := rfl

end LinearStructures

section FormsAndTensor

variable {K : Type*} [Field K] [CharZero K]

local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- The exported quadratic form on the vector coordinate slot.-/
def nV (v : VCoord K) : K := v.r * v.z + Pf v.omega

/-- the symmetric polarization of `nV`.-/
def BV (v w : VCoord K) : K :=
  v.r * w.z + v.z * w.r + BW v.omega w.omega

/--
@isnad1 id=eq.0h3v.s5.cc5ef3aabdf4 from=translated src=- shape=1bf5b2d1 vocab=0c30bac1
-/
theorem BV_symmetric (v w : VCoord K) : BV v w = BV w v := by
  simp only [BV, BW_symmetric]
  ring

/--
@isnad1 id=eq.0h3v.s6.323318a8054c from=translated src=- shape=dfd2aa99 vocab=c4e5b43d
-/
theorem nV_add (v w : VCoord K) :
    nV (v + w) = nV v + nV w + BV v w := by
  simp only [nV, add_r, add_z, add_omega, pf_polar, BV]
  ring

/--
@isnad1 id=eq.0h3v.s7.a0ac8689e16d from=translated src=- shape=09bc91e2 vocab=6a34ad95
-/
theorem nV_smul (a : K) (v : VCoord K) : nV (a • v) = a ^ 2 * nV v := by
  simp only [nV, smul_r, smul_z, smul_eq_mul, smul_omega, pf_smul]
  ring

/--
@isnad1 id=eq.0h2v.s6.4bf6656dc8d1 from=translated src=- shape=19ceee7b vocab=93c5605b
-/
theorem BV_self_eq_two_nV (v : VCoord K) : BV v v = 2 * nV v := by
  rw [show nV v = v.r * v.z +
      (v.omega .i12 * v.omega .i34 - v.omega .i13 * v.omega .i24 +
        v.omega .i14 * v.omega .i23) by rw [nV, pf_coordinate]]
  simp [BV, BW]
  ring

/-- the exported `S` polarization is nondegenerate.
@isnad1 id=eq.1h2v.s6.2833dfb4b6f0 from=translated src=- shape=59d462ba vocab=d0512645
-/
theorem BS_nondegenerate {s : SCoord K} (h : ∀ t : SCoord K, BS s t = 0) :
    s = 0 := by
  have hphi : s.phi = 0 := by
    funext i
    have hi := h ({ p := uBasis i, phi := 0 } : SCoord K)
    fin_cases i <;> simpa [BS, evalU, uBasis] using hi
  have hp : s.p = 0 := by
    funext i
    have hi := h ({ p := 0, phi := uDualBasis i } : SCoord K)
    fin_cases i <;> simpa [BS, evalU, uDualBasis] using hi
  change s = ({ p := 0, phi := 0 } : SCoord K)
  exact SCoord.ext hp hphi

/-- the exported `C` polarization is nondegenerate.
@isnad1 id=eq.1h2v.s6.20922b003160 from=translated src=- shape=59d462ba vocab=4da53a37
-/
theorem BC_nondegenerate {c : CCoord K} (h : ∀ d : CCoord K, BC c d = 0) :
    c = 0 := by
  have hpsi : c.psi = 0 := by
    funext i
    have hi := h ({ q := uBasis i, psi := 0 } : CCoord K)
    fin_cases i <;> simpa [BC, evalU, uBasis] using hi
  have hq : c.q = 0 := by
    funext i
    have hi := h ({ q := 0, psi := uDualBasis i } : CCoord K)
    fin_cases i <;> simpa [BC, evalU, uDualBasis] using hi
  change c = ({ q := 0, psi := 0 } : CCoord K)
  exact CCoord.ext hq hpsi

/-- The exact exported triality tensor in the locked slot order.-/
def triality (v : VCoord K) (s : SCoord K) (c : CCoord K) : K :=
  v.r * evalU s.phi c.q
    + v.z * evalU c.psi s.p
    + BW v.omega (wedge2 s.p c.q)
    + pairW v.omega (dualWedge2 s.phi c.psi)

/--
@isnad1 id=eq.0h5v.s6.2f8103719791 from=translated src=- shape=84bf1b2a vocab=b0824d34
-/
theorem triality_add_v (v w : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (v + w) s c = triality v s c + triality w s c := by
  simp [triality, evalU, pairW, BW]
  ring

/--
@isnad1 id=eq.0h5v.s7.cf403e1a2405 from=translated src=- shape=34e5d76e vocab=c87aa911
-/
theorem triality_smul_v (a : K) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (a • v) s c = a * triality v s c := by
  simp [triality, evalU, pairW, BW]
  ring

/--
@isnad1 id=eq.0h5v.s6.1518506b6a91 from=translated src=- shape=c3c7cb1a vocab=b0824d34
-/
theorem triality_add_s (v : VCoord K) (s t : SCoord K) (c : CCoord K) :
    triality v (s + t) c = triality v s c + triality v t c := by
  simp [triality, evalU, pairW, BW, wedge2, dualWedge2]
  ring

/--
@isnad1 id=eq.0h5v.s7.b6ad930ce280 from=translated src=- shape=b96ccadd vocab=c87aa911
-/
theorem triality_smul_s (a : K) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality v (a • s) c = a * triality v s c := by
  simp [triality, evalU, pairW, BW, wedge2, dualWedge2]
  ring

/--
@isnad1 id=eq.0h5v.s6.a3a0f62da4ee from=translated src=- shape=338ed6dc vocab=b0824d34
-/
theorem triality_add_c (v : VCoord K) (s : SCoord K) (c d : CCoord K) :
    triality v s (c + d) = triality v s c + triality v s d := by
  simp [triality, evalU, pairW, BW, wedge2, dualWedge2]
  ring

/--
@isnad1 id=eq.0h5v.s7.5cb5e692ad4f from=translated src=- shape=c254ca8f vocab=c87aa911
-/
theorem triality_smul_c (a : K) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality v s (a • c) = a * triality v s c := by
  simp [triality, evalU, pairW, BW, wedge2, dualWedge2]
  ring

/-- the tensor packaged as a curried trilinear map.-/
def trialityLinear : VCoord K →ₗ[K] SCoord K →ₗ[K] CCoord K →ₗ[K] K where
  toFun v :=
    { toFun := fun s =>
        { toFun := fun c => triality v s c
          map_add' := triality_add_c v s
          map_smul' := by intro a c; simpa using triality_smul_c a v s c }
      map_add' := by
        intro s t
        ext c
        exact triality_add_s v s t c
      map_smul' := by
        intro a s
        ext c
        simpa using triality_smul_s a v s c }
  map_add' := by
    intro v w
    ext s c
    exact triality_add_v v w s c
  map_smul' := by
    intro a v
    ext s c
    simpa using triality_smul_v a v s c

/--
@isnad1 id=eq.0h4v.s11.5558688294dd from=translated src=- shape=e07b5ad7 vocab=82191d57
-/
@[simp] theorem trialityLinear_apply (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    trialityLinear v s c = triality v s c := rfl

/-!
The following four coefficient tests are supporting constructions and lemmas.  They expose
the two evaluation terms and both exterior terms without asserting a complete
basis theorem for the three carriers.
-/

/--
@isnad1 id=eq.0h1v.s7.0bd6fbe3d4ef from=translated src=- shape=5507b23d vocab=6906a456
-/
theorem triality_coefficient_r_phi_q :
    triality ({ r := 1, z := 0, omega := 0 } : VCoord K)
      ({ p := 0, phi := uDualBasis 0 } : SCoord K)
      ({ q := uBasis 0, psi := 0 } : CCoord K) = 1 := by
  simp [triality, evalU, uBasis, uDualBasis, BW, pairW,
    wedge2, dualWedge2]

/--
@isnad1 id=eq.0h1v.s7.838074603167 from=translated src=- shape=d88c0e87 vocab=6906a456
-/
theorem triality_coefficient_z_p_psi :
    triality ({ r := 0, z := 1, omega := 0 } : VCoord K)
      ({ p := uBasis 0, phi := 0 } : SCoord K)
      ({ q := 0, psi := uDualBasis 0 } : CCoord K) = 1 := by
  simp [triality, evalU, uBasis, uDualBasis, BW, pairW,
    wedge2, dualWedge2]

/--
@isnad1 id=eq.0h1v.s7.c110d88e0380 from=translated src=- shape=06525eb7 vocab=9d0768a7
-/
theorem triality_coefficient_BW_i13_i24 :
    triality ({ r := 0, z := 0, omega := wBasis .i13 } : VCoord K)
      ({ p := uBasis 1, phi := 0 } : SCoord K)
      ({ q := uBasis 3, psi := 0 } : CCoord K) = -1 := by
  simp [triality, evalU, uBasis, wBasis, BW, pairW, wedge2,
    dualWedge2]

/--
@isnad1 id=eq.0h1v.s7.0e9cddc6c20d from=translated src=- shape=6b3bdbee vocab=986b9dde
-/
theorem triality_coefficient_dual_i12 :
    triality ({ r := 0, z := 0, omega := wBasis .i12 } : VCoord K)
      ({ p := 0, phi := uDualBasis 0 } : SCoord K)
      ({ q := 0, psi := uDualBasis 1 } : CCoord K) = 1 := by
  simp [triality, evalU, uDualBasis, wBasis, BW, pairW, wedge2,
    dualWedge2]

/-!
The following unit-parameter actions are the residual torus weights exported
after `eq:sl4forms`: `(r,z)` have weights `(2,-2)`, `(p,phi)` have
weights `(1,-1)`, `(q,psi)` have weights `(-1,1)`, and `omega` has weight
zero.
-/

def torusV (beta : Kˣ) (v : VCoord K) : VCoord K :=
  { r := (beta : K) ^ 2 * v.r
    z := ((beta⁻¹ : Kˣ) : K) ^ 2 * v.z
    omega := v.omega }

def torusS (beta : Kˣ) (s : SCoord K) : SCoord K :=
  { p := (beta : K) • s.p
    phi := ((beta⁻¹ : Kˣ) : K) • s.phi }

def torusC (beta : Kˣ) (c : CCoord K) : CCoord K :=
  { q := ((beta⁻¹ : Kˣ) : K) • c.q
    psi := (beta : K) • c.psi }

/--
@isnad1 id=eq.0h3v.s5.19e69f448c4c from=translated src=- shape=90f6c1f5 vocab=49f28286
-/
theorem nV_torus (beta : Kˣ) (v : VCoord K) : nV (torusV beta v) = nV v := by
  simp only [nV, torusV, Units.val_inv_eq_inv_val]
  field_simp

/--
@isnad1 id=eq.0h3v.s5.54a5bc17375c from=translated src=- shape=90f6c1f5 vocab=1b6b4293
-/
theorem nS_torus (beta : Kˣ) (s : SCoord K) : nS (torusS beta s) = nS s := by
  simp only [nS, torusS, Units.val_inv_eq_inv_val]
  simp [evalU]
  field_simp

/--
@isnad1 id=eq.0h3v.s5.ceaf96faf875 from=translated src=- shape=90f6c1f5 vocab=a7f9eb98
-/
theorem nC_torus (beta : Kˣ) (c : CCoord K) : nC (torusC beta c) = nC c := by
  simp only [nC, torusC, Units.val_inv_eq_inv_val]
  simp [evalU]
  field_simp

/--
@isnad1 id=eq.0h5v.s6.4232738859d2 from=translated src=- shape=836f1ab2 vocab=63c1911c
-/
theorem triality_torus (beta : Kˣ) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (torusV beta v) (torusS beta s) (torusC beta c) = triality v s c := by
  simp only [torusV, torusS, torusC, Units.val_inv_eq_inv_val]
  simp [triality, evalU, wedge2, dualWedge2, BW, pairW]
  field_simp

end FormsAndTensor

section Composition

variable {K : Type*} [Field K] [CharZero K]

local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- The locked two-parameter triality composition map.-/
def muV (alpha beta : K) (s : SCoord K) (c : CCoord K) : VCoord K :=
  { r := evalU c.psi s.p
    z := evalU s.phi c.q
    omega := alpha • wedge2 s.p c.q
      + beta • hodgeStar (dualWedge2 s.phi c.psi) }

/-- A dual decomposable exterior vector has zero Pfaffian after Hodge star.
@isnad1 id=eq.0h3v.s5.319342842f29 from=translated src=- shape=ea9c886e vocab=8558a3a3
-/
theorem pf_hodgeStar_dualWedge_zero (phi psi : Udual K) :
    Pf (hodgeStar (dualWedge2 phi psi)) = 0 := by
  rw [pf_coordinate]
  simp [hodgeStar, dualWedge2]
  ring

/-- The cross term in the composition calculation.
@isnad1 id=eq.0h5v.s7.feecaf34a915 from=translated src=- shape=b37cda31 vocab=b416ef91
-/
theorem BW_wedge_hodge_dual (p q : U K) (phi psi : Udual K) :
    BW (wedge2 p q) (hodgeStar (dualWedge2 phi psi)) =
      evalU phi p * evalU psi q - evalU phi q * evalU psi p := by
  rw [BW_symmetric, BW_hodgeStar, wedge_dual_pairing]

/-- The full locked source formula, retaining both parameters separately.
@isnad1 id=eq.0h5v.s7.815cf1679f12 from=translated src=- shape=4113fd17 vocab=9789be13
-/
theorem nV_muV (alpha beta : K) (s : SCoord K) (c : CCoord K) :
    nV (muV alpha beta s c) =
      alpha * beta * evalU s.phi s.p * evalU c.psi c.q
        + (1 - alpha * beta) * evalU c.psi s.p * evalU s.phi c.q := by
  simp only [nV, muV, pf_polar, pf_smul, decomposable_pf_zero,
    pf_hodgeStar_dualWedge_zero, BW_smul_left, BW_smul_right,
    BW_wedge_hodge_dual]
  ring

/--
@isnad1 id=eq.1h5v.s6.90724d4a58c4 from=translated src=- shape=77cfb8fd vocab=97593205
-/
theorem composition_of_mul_eq_one {alpha beta : K} (h : alpha * beta = 1) :
    ∀ s c, nV (muV alpha beta s c) = nS s * nC c := by
  intro s c
  rw [nV_muV, h]
  simp [nS, nC]

/-- A single locked diagonal specialization recovers the product `alpha*beta`.
@isnad1 id=eq.0h3v.s6.caa70223abea from=translated src=- shape=cccd498e vocab=f5b2cdfa
-/
theorem composition_diagonal_witness (alpha beta : K) :
    nV (muV alpha beta (sBasis 0) (cBasis 1)) = alpha * beta := by
  rw [nV_muV]
  simp [sBasis, cBasis, evalU, uBasis, uDualBasis]

/-- Composition holds for every pair exactly when the parameter product is one.
@isnad1 id=iff.0h3v.s6.8e32936d7f3d from=translated src=- shape=b3701004 vocab=97593205
-/
theorem composition_iff_mul_eq_one (alpha beta : K) :
    (∀ s c, nV (muV alpha beta s c) = nS s * nC c) ↔ alpha * beta = 1 := by
  constructor
  · intro h
    have hw := h (sBasis 0) (cBasis 1)
    rw [composition_diagonal_witness] at hw
    simpa [nS_basis, nC_basis] using hw
  · exact composition_of_mul_eq_one

/-- The separately declared normalization convention.-/
def normalizedMuV (s : SCoord K) (c : CCoord K) : VCoord K := muV 1 1 s c

/--
@isnad1 id=eq.0h3v.s5.dc2f267bd7c0 from=translated src=- shape=efabeac0 vocab=18edbf6b
-/
theorem normalizedMuV_composition (s : SCoord K) (c : CCoord K) :
    nV (normalizedMuV s c) = nS s * nC c := by
  exact composition_of_mul_eq_one (by simp) s c

/--
Tensor and composition comparison.  The conjunction binds the exact tensor and
`muV` coordinate formulas, the full norm calculation, and the universal
composition equivalence without selecting a normalization of the factors.
@isnad1 id=and.0h3v.s9.8bda8a39e690 from=translated src=- shape=e7af9bfa vocab=f8e6a58b
-/
theorem TrialityTensorCompositionTheorem (alpha beta : K) :
    (∀ (v : VCoord K) (s : SCoord K) (c : CCoord K),
      triality v s c =
        v.r * evalU s.phi c.q
          + v.z * evalU c.psi s.p
          + BW v.omega (wedge2 s.p c.q)
          + pairW v.omega (dualWedge2 s.phi c.psi)) ∧
    (∀ (s : SCoord K) (c : CCoord K),
      muV alpha beta s c =
        { r := evalU c.psi s.p
          z := evalU s.phi c.q
          omega := alpha • wedge2 s.p c.q
            + beta • hodgeStar (dualWedge2 s.phi c.psi) }) ∧
    (∀ (s : SCoord K) (c : CCoord K),
      nV (muV alpha beta s c) =
        alpha * beta * evalU s.phi s.p * evalU c.psi c.q
          + (1 - alpha * beta) * evalU c.psi s.p * evalU s.phi c.q) ∧
    ((∀ (s : SCoord K) (c : CCoord K),
      nV (muV alpha beta s c) = nS s * nC c) ↔ alpha * beta = 1) := by
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl, nV_muV alpha beta,
    composition_iff_mul_eq_one alpha beta⟩

/--
composition does not determine the two factors
separately.  This characteristic-zero witness rejects an illicit inference
from `alpha*beta=1` to the normalization convention `alpha=beta=1`.
@isnad1 id=ex.0h0v.s5.164490e1a397 from=translated src=- shape=aa9a83c0 vocab=b3f75c3d
-/
theorem composition_does_not_force_normalization :
    ∃ alpha beta : ℚ,
      (∀ s c, nV (muV alpha beta s c) = nS s * nC c) ∧
        alpha ≠ 1 ∧ beta ≠ 1 := by
  refine ⟨2, 1 / 2, ?_, by norm_num, by norm_num⟩
  exact composition_of_mul_eq_one (by norm_num)

end Composition

end AlbertLean.Triality.CoordinateTensor
