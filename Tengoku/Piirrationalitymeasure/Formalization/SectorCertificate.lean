import Tengoku.Piirrationalitymeasure.Formalization.PrimeSaving

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxRecDepth 100000

/-!
Finite arithmetic certificate for the twelve directional sectors in Section 6.6.
-/

namespace PiIrrationality

structure SectorData where
  nA : ℤ
  nB : ℤ
  nC : ℤ
  nQ : ℤ
  px : ℚ
  py : ℚ
deriving DecidableEq

def sectorRows : List SectorData :=
  [ ⟨0, -2786, 1671, 1115, -223 / 743, 206777 / 1379751⟩
  , ⟨0, -2786, 1671, 1115, -223 / 743, 206777 / 1379751⟩
  , ⟨-1857, -929, 1671, 1115, 520 / 743, -966197 / 2759502⟩
  , ⟨-1856, -929, 1670, 1115, 964897 / 1379751, -966197 / 2759502⟩
  , ⟨-1856, -930, 1670, 1116, 4822628 / 6898755, -805783 / 2299585⟩
  , ⟨-1856, -930, 1673, 1113, 4828199 / 6898755, -802069 / 2299585⟩
  , ⟨-1856, -928, 1671, 1113, 4828199 / 6898755, -2409922 / 6898755⟩
  , ⟨-1857, -928, 1671, 1114, 2601 / 3715, -2413636 / 6898755⟩
  , ⟨0, -2785, 1671, 1114, -1114 / 3715, 2071483 / 13797510⟩
  , ⟨0, -2785, 1671, 1114, -1114 / 3715, 2071483 / 13797510⟩
  , ⟨0, -2784, 1671, 1113, -1113 / 3715, 345866 / 2299585⟩
  , ⟨0, -2784, 1669, 1115, -223 / 743, 68678 / 459917⟩ ]

def sectorChecksum (r : SectorData) : Prop :=
  r.nA + r.nB + r.nC + r.nQ = 0

def sectorFormConsistent (r : SectorData) : Prop :=
  r.px = -(r.nA : ℚ) / 1857 - (r.nQ : ℚ) / 3715 ∧
    r.py = -(r.nB : ℚ) / 3714 - 2 * (r.nQ : ℚ) / 3715

/--
@isnad1 id=eq.0h0v.s3.d7cf0766e189 from=translated src=- shape=b3c4969c vocab=1db9f1fd
-/
theorem sectorRows_length : sectorRows.length = 12 := by
  decide

/--
@isnad1 id=sectorch.1h1v.s3.12aeafbc0d83 from=translated src=- shape=704778be vocab=62052faa
-/
theorem sectorRows_checksums : ∀ r ∈ sectorRows, sectorChecksum r := by
  intro r hr
  simp [sectorRows, sectorChecksum] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

/--
@isnad1 id=sectorfo.1h1v.s3.0c0586cbe345 from=translated src=- shape=704778be vocab=c089c504
-/
theorem sectorRows_forms : ∀ r ∈ sectorRows, sectorFormConsistent r := by
  intro r hr
  simp [sectorRows, sectorFormConsistent] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

/--
@isnad1 id=and.0h0v.s8.e0bd3a11f173 from=translated src=- shape=4bbd400a vocab=ad553ab0
-/
theorem sector_ray_values_negative :
    (-(223 : ℚ) / 743 < 0) ∧
    (-(776458 : ℚ) / 1857 < 0) ∧
    (-(557 : ℚ) / 1379751 < 0) ∧
    (-(966197 : ℚ) / 2759502 < 0) ∧
    (-(7236730 : ℚ) / 1857 < 0) ∧
    (-(3247 : ℚ) / 1857 < 0) ∧
    (-(4828199 : ℚ) / 6898755 < 0) ∧
    (-(1810807 : ℚ) / 1857 < 0) ∧
    (-(2071483 : ℚ) / 13797510 < 0) ∧
    (-(1671 : ℚ) < 0) ∧
    (-(464 : ℚ) / 619 < 0) := by
  norm_num

/--
@isnad1 id=lt.0h0v.s4.fc62d642df42 from=translated src=- shape=5ee22617 vocab=a4066e59
-/
theorem sector_kappa_positive : 0 < (557 : ℚ) / 4139253 := by
  norm_num

def sectorForm1 (v1 v2 : ℚ) : ℚ :=
  -(223 : ℚ) / 743 * v1 + 206777 / 1379751 * v2

def sectorForm9 (v1 v2 : ℚ) : ℚ :=
  -(1114 : ℚ) / 3715 * v1 + 2071483 / 13797510 * v2

/--
@isnad1 id=eq.0h0v.s5.c01aae285265 from=translated src=- shape=5883e1a0 vocab=12d8c6b6
-/
theorem sectorForm1_diagonal : sectorForm1 (1 / 2) 1 = -(557 : ℚ) / 2759502 := by
  norm_num [sectorForm1]

/--
@isnad1 id=eq.0h0v.s5.da2f86897333 from=translated src=- shape=1ffd3c6c vocab=8fb83a47
-/
theorem sectorForm9_antidiagonal : sectorForm9 (-(1 / 2)) (-1) =
    -(557 : ℚ) / 2759502 := by
  norm_num [sectorForm9]

/--
@isnad1 id=and.0h0v.s9.429a7eb04df0 from=translated src=- shape=bb42cf94 vocab=7c17de2b
-/
theorem sector_kappa_ray_bounds :
    (557 : ℚ) / 4139253 ≤ 223 / 743 ∧
    (557 : ℚ) / 4139253 ≤ 776458 / (1857 * 2786) ∧
    (557 : ℚ) / 4139253 ≤ 557 / (1379751 * 3) ∧
    (557 : ℚ) / 4139253 ≤ 966197 / 2759502 ∧
    (557 : ℚ) / 4139253 ≤ 7236730 / (1857 * 7427) ∧
    (557 : ℚ) / 4139253 ≤ 3247 / (1857 * 3) ∧
    (557 : ℚ) / 4139253 ≤ 4828199 / 6898755 ∧
    (557 : ℚ) / 4139253 ≤ 1810807 / (1857 * 2786) ∧
    (557 : ℚ) / 4139253 ≤ 557 / (1379751 * 3) ∧
    (557 : ℚ) / 4139253 ≤ 2071483 / 13797510 ∧
    (557 : ℚ) / 4139253 ≤ 1671 / 7427 ∧
    (557 : ℚ) / 4139253 ≤ 464 / (619 * 3) := by
  norm_num

/--
@isnad1 id=eq.0h0v.s5.f8c57bda33e8 from=translated src=- shape=29714cae vocab=53df3535
-/
theorem sector_kappa_ray_equality :
    (557 : ℚ) / 4139253 = 557 / (1379751 * 3) := by
  norm_num

/--
@isnad1 id=ne.0h0v.s2.ce057c4f5d59 from=translated src=- shape=228d301a vocab=29402020
-/
theorem sectorRows_nonempty : sectorRows ≠ [] := by
  decide

end PiIrrationality
