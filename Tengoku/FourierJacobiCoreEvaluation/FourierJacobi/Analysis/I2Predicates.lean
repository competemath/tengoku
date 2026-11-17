import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.I2Domains

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace FourierJacobi.Analysis

/--
@isnad1 id=iff.0h1v.s6.cfceeddffd49 from=translated src=- shape=86ebb01e vocab=77c34720
-/
@[simp] theorem i2SpatialPredicate_row0 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 0 p ↔ (2 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.9ff889d3967d from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row0 (c : ℕ) : i2DepthPredicate 0 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.24770bccb3ad from=translated src=- shape=aa721ebc vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row1 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 1 p ↔ (p.1 = 1 ∧ -2 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.f65018d2f8be from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row1 (c : ℕ) : i2DepthPredicate 1 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.04ba3f4b4999 from=translated src=- shape=c73d75de vocab=8349330d
-/
@[simp] theorem i2SpatialPredicate_row2 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 2 p ↔ (1 ≤ p.1 ∧ -2*p.1 ≤ p.2.1 ∧ p.2.2 < -p.1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.3c8370695672 from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row2 (c : ℕ) : i2DepthPredicate 2 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.4e644f2b7a20 from=translated src=- shape=f03527b5 vocab=e2d50036
-/
@[simp] theorem i2SpatialPredicate_row3 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 3 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.c9303d2d5fff from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row3 (c : ℕ) : i2DepthPredicate 3 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.277ca02be9a5 from=translated src=- shape=0ef005f4 vocab=e2d50036
-/
@[simp] theorem i2SpatialPredicate_row4 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 4 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.cbee320dda36 from=translated src=- shape=dae5f6d0 vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row4 (c : ℕ) : i2DepthPredicate 4 c ↔ (c = 0) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.dae85fe1eff2 from=translated src=- shape=0ef005f4 vocab=e2d50036
-/
@[simp] theorem i2SpatialPredicate_row5 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 5 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.3cf37878e2f9 from=translated src=- shape=dae5f6d0 vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row5 (c : ℕ) : i2DepthPredicate 5 c ↔ (c = 1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.232a055965a9 from=translated src=- shape=0ef005f4 vocab=e2d50036
-/
@[simp] theorem i2SpatialPredicate_row6 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 6 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.03b282de581b from=translated src=- shape=4992ae84 vocab=fa83318a
-/
@[simp] theorem i2DepthPredicate_row6 (c : ℕ) : i2DepthPredicate 6 c ↔ (2 ≤ c) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.891894d13a9c from=translated src=- shape=af3672b9 vocab=e2d50036
-/
@[simp] theorem i2SpatialPredicate_row7 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 7 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.1+p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.10138baea9d1 from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row7 (c : ℕ) : i2DepthPredicate 7 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.7b42c6395556 from=translated src=- shape=c98537a3 vocab=fb842c67
-/
@[simp] theorem i2SpatialPredicate_row8 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 8 p ↔ (1 ≤ p.1 ∧ p.2.1 < -2*p.1 ∧ p.2.2 < p.1+p.2.1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.3ab21b92136a from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row8 (c : ℕ) : i2DepthPredicate 8 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.f7fe6fc904fe from=translated src=- shape=5fa5607b vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row9 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 9 p ↔ (p.1 = 0 ∧ 0 ≤ p.2.1 ∧ -1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.453fc87906dc from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row9 (c : ℕ) : i2DepthPredicate 9 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.5a8b7de15122 from=translated src=- shape=3463ec9d vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row10 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 10 p ↔ (p.1 = 0 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.1e5a4ca5fe1b from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row10 (c : ℕ) : i2DepthPredicate 10 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.fe44cb3a28d9 from=translated src=- shape=c626af2a vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row11 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 11 p ↔ (p.1 = 0 ∧ -1 ≤ p.2.1 ∧ p.2.2 ≤ -2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.e339f4957bfd from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row11 (c : ℕ) : i2DepthPredicate 11 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.1f58cf017e63 from=translated src=- shape=4c4de4cd vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row12 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 12 p ↔ (p.1 = -1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.b460131d3d1f from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row12 (c : ℕ) : i2DepthPredicate 12 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.83062a28e639 from=translated src=- shape=f3ab96ce vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row13 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 13 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.a5ee4c2b9d61 from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row13 (c : ℕ) : i2DepthPredicate 13 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.8c8f5656d068 from=translated src=- shape=7306f1b3 vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row14 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 14 p ↔ (p.1 = -1 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.95f29edc7d8f from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row14 (c : ℕ) : i2DepthPredicate 14 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.554be0ae6c54 from=translated src=- shape=94ab46b4 vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row15 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 15 p ↔ (p.1 ≤ -2 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.6aa5c7846a4f from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row15 (c : ℕ) : i2DepthPredicate 15 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.6ee44789c05b from=translated src=- shape=eb9cf294 vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row16 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 16 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ -1 ≤ p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.e7a9a25e9557 from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row16 (c : ℕ) : i2DepthPredicate 16 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.0fcd2868a75f from=translated src=- shape=02dc2086 vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row17 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 17 p ↔ (p.1 ≤ -2 ∧ p.2.1 = -1 ∧ p.2.2 ≤ -2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.b177d24e51af from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row17 (c : ℕ) : i2DepthPredicate 17 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.34b435f09df9 from=translated src=- shape=d8f8dbc4 vocab=bdd72619
-/
@[simp] theorem i2SpatialPredicate_row18 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 18 p ↔ (p.1 ≤ -1 ∧ 0 ≤ p.2.1 ∧ p.2.2 ≤ -1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.58160dff7fb7 from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row18 (c : ℕ) : i2DepthPredicate 18 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.74fd792fb531 from=translated src=- shape=669632ff vocab=8ea3bc44
-/
@[simp] theorem i2SpatialPredicate_row19 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 19 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ p.2.1-1 ≤ 2*p.2.2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.f596aab580da from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row19 (c : ℕ) : i2DepthPredicate 19 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.2a4f9c4d5de3 from=translated src=- shape=ee01d75e vocab=8ea3bc44
-/
@[simp] theorem i2SpatialPredicate_row20 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 20 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.18c5b7cb300a from=translated src=- shape=dae5f6d0 vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row20 (c : ℕ) : i2DepthPredicate 20 c ↔ (c = 0) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.45bff7b5e0ed from=translated src=- shape=ee01d75e vocab=8ea3bc44
-/
@[simp] theorem i2SpatialPredicate_row21 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 21 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.cea01b7c0b84 from=translated src=- shape=dae5f6d0 vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row21 (c : ℕ) : i2DepthPredicate 21 c ↔ (c = 1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.4ee1c675af97 from=translated src=- shape=ee01d75e vocab=8ea3bc44
-/
@[simp] theorem i2SpatialPredicate_row22 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 22 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 = p.2.1-2) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.b07c82bf7f38 from=translated src=- shape=4992ae84 vocab=fa83318a
-/
@[simp] theorem i2DepthPredicate_row22 (c : ℕ) : i2DepthPredicate 22 c ↔ (2 ≤ c) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s7.78aea3521294 from=translated src=- shape=12843819 vocab=8ea3bc44
-/
@[simp] theorem i2SpatialPredicate_row23 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 23 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.1 ≤ p.2.2 ∧ 2*p.2.2 ≤ p.2.1-3) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.eac375d5b74e from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row23 (c : ℕ) : i2DepthPredicate 23 c ↔ (True) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s6.7543020a612a from=translated src=- shape=9b84ec73 vocab=149ace44
-/
@[simp] theorem i2SpatialPredicate_row24 (p : ℤ × ℤ × ℤ) : i2SpatialPredicate 24 p ↔ (p.1 ≤ 0 ∧ p.2.1 < -1 ∧ p.2.2 < p.2.1) := Iff.rfl
/--
@isnad1 id=iff.0h1v.s4.e7c4ebfe6e6f from=translated src=- shape=e7da5d0e vocab=c0dfc963
-/
@[simp] theorem i2DepthPredicate_row24 (c : ℕ) : i2DepthPredicate 24 c ↔ (True) := Iff.rfl

end FourierJacobi.Analysis
