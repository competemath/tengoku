/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Divisorial.Discriminant
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.ChargeFamily
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Discriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Every fixed-`u` slice of a divisorial alignmentLocus family is an `(s, t)` half plane

`Walls/Numerical/Basic.lean` proves that a numerical alignmentLocus in the `(s, t)` plane
is a circle centred on the `s`-axis or a vertical line, that two walls of a
fixed class are disjoint, and that they are nested.  Those are theorems about
the three-coordinate polynomial and, until this file, were available only to
the compressed Picard-rank-one transport that geometric consumers build.

The divisorial family of `Slice.lean` is indexed by
`B = s H + G(u)`, `omega = t H` with `u` in an arbitrary real transverse space.
Fixing `u` and letting `(s, t)` vary gives a half plane, and the theorem below
says that half plane **is** the `(s, t)` model, pulled back along the
degree-weighted triple of the `G(u)`-twisted character:

```text
(T.chargeFamily ch).reindex (fun (s,t) => ⟨s, u, t⟩)
  = stChargeFamily.pullback ((ch.twist S (G u)).coordinatesAt S H).toNumClassHom
```

Consequently the circle, line, disjointness, and nesting results hold on every
`u`-slice of a surface of arbitrary Picard rank.  This is the alignmentLocus picture used
by Maciocia (arXiv:1202.4587, Prop. 2.6 and Thm 3.1), Arcara--Miles
(arXiv:1401.6149, §4) and Mizuno--Yoshida (arXiv:2502.18894, Thm 2.1), and it is
the reason those papers fix a transverse direction before drawing circles.

## The `u`-dependence is real

Twisting by `G(u)` does not change the compressed degree, because `H · G(u) = 0`,
but it does change the compressed `ch₂` and hence the discriminant:
`discr` of the slice class exceeds the untwisted one by
`2 H² r (G(u) · ch₁) - H² r² G(u)²` (`discr_sliceCoordinates`).  So the walls
genuinely move as `u` varies, which is what makes the transverse parameter worth
carrying; only within one `u`-plane are they nested.

## Nesting needs a nonnegative discriminant, and now has one

`barDiscriminant_parameters` computes the `\bar Δ^B_ω` of
`Discriminant.lean` at a slice point: it is `t²` times the slice
discriminant, with the `s`-dependence cancelling exactly.  Bogomolov--Gieseker
and a Hodge index at `omega` therefore discharge the `0 ≤ discr` hypothesis of
the disjointness and nesting theorems on every `u`-plane, not only on the
rank-one one.

Nothing here proves a Bogomolov inequality or a Hodge index theorem; both remain
supplied certificates: `DivisorSpace.HodgeIndex` here, and a Bogomolov
inequality that only a geometric consumer can provide.
-/

universe v w x

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

variable {N : Type v} {D : Type w}
variable [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-! ### Compressed coordinates as a point of the `(s, t)` alignmentLocus plane -/

namespace ChargeCoordinates

variable (Dc : ChargeCoordinates N)

/-- The degree-weighted numerical triple of compressed charge coordinates.

The rank slot carries `∫H²`, which is what the `(s,t)` charge polynomial
requires; `stCharge_toNumClass` below is the identity that forces it.-/
def toNumClass (E : N) : Wall.NumClass :=
  (Dc.hyperplaneSquare * Dc.rank E, Dc.degree E, Dc.chTwo E)

/--
@isnad1 id=eq.0h3v.s6.5cff0125ae1a from=translated src=- shape=999a5ba6 vocab=090a836a
-/
@[simp]
theorem toNumClass_rk (E : N) :
    (Dc.toNumClass E).rk = Dc.hyperplaneSquare * Dc.rank E := rfl

/--
@isnad1 id=eq.0h3v.s6.571f786d221b from=translated src=- shape=117a5808 vocab=9d880312
-/
@[simp]
theorem toNumClass_deg (E : N) : (Dc.toNumClass E).deg = Dc.degree E := rfl

/--
@isnad1 id=eq.0h3v.s6.4c8a6447b96f from=translated src=- shape=117a5808 vocab=44a94ee0
-/
@[simp]
theorem toNumClass_ch2 (E : N) : (Dc.toNumClass E).ch2 = Dc.chTwo E := rfl

/-- The triple is additive, because each of its three coordinates is.-/
def toNumClassHom : N →+ Wall.NumClass :=
  AddMonoidHom.mk' Dc.toNumClass (by
    intro E F
    simp only [toNumClass, map_add, Prod.mk_add_mk, mul_add])

/--
@isnad1 id=eq.0h3v.s6.def5c535f4da from=translated src=- shape=9f296ce8 vocab=d1c74cff
-/
@[simp]
theorem toNumClassHom_apply (E : N) : Dc.toNumClassHom E = Dc.toNumClass E := rfl

/-- The alignmentLocus-plane discriminant of the transported triple is the compressed
discriminant.
@isnad1 id=eq.0h3v.s4.8ec2c326be90 from=translated src=- shape=74388937 vocab=d0e2a084
-/
@[simp]
theorem discr_toNumClass (E : N) :
    Wall.NumClass.discr (Dc.toNumClass E) = Dc.discr E := by
  simp only [Wall.NumClass.discr_eq, toNumClass_rk, toNumClass_deg, toNumClass_ch2,
    ChargeCoordinates.discr]
  ring

/-- **The `(s,t)` charge of the transported triple is the scalar-twisted
charge.**  This is the identity that makes the whole `(s,t)` development
available to any compressed coordinates.
@isnad1 id=eq.0h5v.s7.6ed11ecb13ef from=translated src=- shape=8558e3f5 vocab=53054c70
-/
theorem stCharge_toNumClass (b a : ℝ) (E : N) :
    Wall.stCharge b a (Dc.toNumClass E) = (Dc.twistByScalar b).centralCharge a E := by
  apply Complex.ext
  · rw [Wall.stCharge_re, ChargeCoordinates.centralCharge_re]
    simp only [Wall.reZ, toNumClass_rk, toNumClass_deg, toNumClass_ch2,
      twistByScalar_chTwo, twistByScalar_rank, twistByScalar_hyperplaneSquare]
    ring
  · rw [Wall.stCharge_im, ChargeCoordinates.centralCharge_im]
    simp only [Wall.imZ, toNumClass_rk, toNumClass_deg, twistByScalar_degree]
    ring

/-- The `(s,t)` alignmentLocus family of compressed coordinates: the generic `(s,t)` child
pulled back along the degree-weighted triple.-/
def stWallFamily : Wall.ChargeFamily (ℝ × ℝ) N :=
  Wall.stChargeFamily.pullback Dc.toNumClassHom

/--
@isnad1 id=eq.0h4v.s7.4b0df345bc48 from=translated src=- shape=68b347c7 vocab=52212b76
-/
@[simp]
theorem stWallFamily_charge (p : ℝ × ℝ) (E : N) :
    Dc.stWallFamily.charge p E = Wall.stCharge p.1 p.2 (Dc.toNumClass E) := rfl

/--
@isnad1 id=eq.0h5v.s5.0fe04e3fdb93 from=translated src=- shape=2a7ff4bc vocab=4cb7d30a
-/
@[simp]
theorem stWallFamily_alignmentValue (p : ℝ × ℝ) (E F : N) :
    Dc.stWallFamily.alignmentValue p E F =
      Wall.wallExpr p.1 p.2 (Dc.toNumClass E) (Dc.toNumClass F) := by
  simp [stWallFamily]

end ChargeCoordinates

/-! ### Twisting the character moves the `B`-field -/

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- **Twisting the character adds to the `B`-field.**  This is
`exp(-B₀) exp(-B) = exp(-(B₀+B))` read on the central charge, and it is what
lets a slice absorb its transverse direction into the character.
@isnad1 id=eq.0h7v.s7.d4145dafa828 from=translated src=- shape=e294364b vocab=a32fcb43
-/
theorem centralCharge_twist (B : D) (P : StabilityParameters D) (E : N) :
    (ch.twist S B).centralCharge S P E =
      ch.centralCharge S ⟨P.B + B, P.omega⟩ E := by
  have hcomm : S.pair P.B B = S.pair B P.B := S.pair_comm P.B B
  rw [centralCharge_apply, centralCharge_apply]
  simp only [twist_rank, twist_chOne, twist_chTwo, DivisorSpace.pair, map_add, map_sub,
    map_smul, LinearMap.add_apply, smul_eq_mul] at hcomm ⊢
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero]
  · linear_combination (-(ch.rank E) / 2) * hcomm
  · ring

end ChernCharacter

/-! ### A fixed transverse parameter gives an `(s, t)` half plane -/

namespace OrthogonalSlice

variable {U : Type x} [AddCommGroup U] [Module ℝ U]

namespace Point

/-- The slice point at a fixed transverse parameter, as a function of `(s, t)`.-/
def ofST (uu : U) (p : ℝ × ℝ) : Point U := ⟨p.1, uu, p.2⟩

end Point

variable {S : DivisorSpace D} (T : OrthogonalSlice S U)

/-- The compressed coordinates a fixed `u`-slice sees: the `G(u)`-twisted
character, read at `H`.-/
def sliceCoordinates (ch : ChernCharacter N D) (uu : U) : ChargeCoordinates N :=
  (ch.twist S (T.transverse uu)).coordinatesAt S T.H

/--
@isnad1 id=eq.0h8v.s7.fbb2928b4502 from=translated src=- shape=98cdeeca vocab=b2ab0566
-/
@[simp]
theorem sliceCoordinates_rank (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).rank E = ch.rank E := rfl

/-- The compressed degree does not see the transverse direction, because
`G(u)` is orthogonal to `H`.
@isnad1 id=eq.0h8v.s7.50e822e2d696 from=translated src=- shape=8b645f1e vocab=05ce151b
-/
@[simp]
theorem sliceCoordinates_degree (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).degree E = S.pair T.H (ch.chOne E) := by
  show S.pair T.H (ch.chOne E - ch.rank E • T.transverse uu) = _
  simp only [DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
  rw [show S.intersection T.H (T.transverse uu) = 0 from T.orthogonal uu]
  ring

/--
@isnad1 id=eq.0h8v.s8.807fe40822ea from=translated src=- shape=50a301f2 vocab=7ae929f7
-/
@[simp]
theorem sliceCoordinates_chTwo (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).chTwo E =
      ch.chTwo E - S.pair (T.transverse uu) (ch.chOne E)
        + S.pair (T.transverse uu) (T.transverse uu) * ch.rank E / 2 := rfl

/--
@isnad1 id=eq.0h7v.s6.e2d0a3ac6f76 from=translated src=- shape=f2f6afbd vocab=e4bd7cb4
-/
@[simp]
theorem sliceCoordinates_hyperplaneSquare (ch : ChernCharacter N D) (uu : U) :
    (T.sliceCoordinates ch uu).hyperplaneSquare = S.pair T.H T.H := rfl

/--
@isnad1 id=eq.0h6v.s8.949b46e47f31 from=translated src=- shape=9aa9f51f vocab=0aad23f0
-/
@[simp]
theorem parameters_ofST (uu : U) (p : ℝ × ℝ) :
    T.parameters (Point.ofST uu p) =
      ⟨p.1 • T.H + T.transverse uu, p.2 • T.H⟩ := rfl

/-- **The fixed-`u` slice of a divisorial alignmentLocus family is the `(s,t)` model.**

Reindexing the divisorial family to a fixed transverse parameter gives exactly
the generic `(s,t)` charge family, pulled back along the degree-weighted triple
of the `G(u)`-twisted character.  Every circle, line, disjointness and nesting
theorem of `Walls/Numerical/` therefore applies on that half plane.
@isnad1 id=eq.0h7v.s6.8ee10e165e69 from=translated src=- shape=396e8852 vocab=5655dea6
-/
theorem chargeFamily_reindex_ofST (ch : ChernCharacter N D) (uu : U) :
    (T.chargeFamily ch).reindex (Point.ofST uu) =
      (T.sliceCoordinates ch uu).stWallFamily := by
  ext p E
  rw [Wall.ChargeFamily.reindex_charge, ChargeCoordinates.stWallFamily_charge,
    ChargeCoordinates.stCharge_toNumClass]
  show ch.centralCharge S (T.parameters (Point.ofST uu p)) E
      = ((((ch.twist S (T.transverse uu)).coordinatesAt S T.H).twistByScalar
          p.1).centralCharge p.2) E
  rw [← ChernCharacter.centralCharge_rankOne_eq (ch.twist S (T.transverse uu)) S T.H p.2 p.1 E,
    ChernCharacter.centralCharge_twist]
  rfl

/-- The alignmentLocus of two classes on a fixed `u`-slice is the `(s,t)` alignmentLocus of their
transported triples.
@isnad1 id=eq.0h10v.s7.29f54381d477 from=translated src=- shape=6f4f9329 vocab=44f15264
-/
theorem alignmentValue_ofST (ch : ChernCharacter N D) (uu : U) (p : ℝ × ℝ) (v w : N) :
    (T.chargeFamily ch).alignmentValue (Point.ofST uu p) v w =
      Wall.wallExpr p.1 p.2 ((T.sliceCoordinates ch uu).toNumClass v)
        ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [show (T.chargeFamily ch).alignmentValue (Point.ofST uu p) v w
        = ((T.chargeFamily ch).reindex (Point.ofST uu)).alignmentValue p v w from rfl,
    T.chargeFamily_reindex_ofST ch uu, ChargeCoordinates.stWallFamily_alignmentValue]

/-! ### The circle, on every slice -/

/-- **A numerical alignmentLocus on a fixed `u`-slice is cut out by a circle equation.**
Maciocia Prop. 2.6; Mizuno--Yoshida Thm 2.1(1).
@isnad1 id=iff.1h10v.s8.5a5e7ce7d8e6 from=translated src=- shape=058338cb vocab=e166864a
-/
theorem alignmentLocus_ofST_iff_circle (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) (v w : N) :
    Point.ofST uu p ∈ T.alignmentLocus ch v w ↔
      Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) * (p.1 ^ 2 + p.2 ^ 2)
          + 2 * Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) * p.1
          + 2 * Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
            ((T.sliceCoordinates ch uu).toNumClass w) = 0 := by
  rw [OrthogonalSlice.alignmentLocus, Wall.ChargeFamily.mem_alignmentLocus, T.alignmentValue_ofST]
  exact Wall.wall_iff_circle ht _ _

/-- Centre `(-minB/minA, 0)` and radius squared `(minB² - 2 minA minC)/minA²`,
on a fixed `u`-slice, in cleared form.
@isnad1 id=iff.2h10v.s8.5c2885f33160 from=translated src=- shape=0564760a vocab=4f13ace9
-/
theorem alignmentLocus_ofST_circle_eq (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) {v w : N}
    (hA : Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) ≠ 0) :
    Point.ofST uu p ∈ T.alignmentLocus ch v w ↔
      (Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) * p.1
            + Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w)) ^ 2
          + (Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) * p.2) ^ 2
        = Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) ^ 2
          - 2 * Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w)
            * Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
              ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [OrthogonalSlice.alignmentLocus, Wall.ChargeFamily.mem_alignmentLocus, T.alignmentValue_ofST]
  exact Wall.wall_circle_eq ht hA

/-- The vertical-line case, on a fixed `u`-slice.
@isnad1 id=iff.3h10v.s8.0a79eb6eb2d4 from=translated src=- shape=c4a401ea vocab=5d4258e9
-/
theorem alignmentLocus_ofST_line_eq (ch : ChernCharacter N D) (uu : U) {p : ℝ × ℝ}
    (ht : p.2 ≠ 0) {v w : N}
    (hA : Wall.minA ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) = 0)
    (hB : Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
      ((T.sliceCoordinates ch uu).toNumClass w) ≠ 0) :
    Point.ofST uu p ∈ T.alignmentLocus ch v w ↔
      p.1 = -(Wall.minC ((T.sliceCoordinates ch uu).toNumClass v)
          ((T.sliceCoordinates ch uu).toNumClass w))
        / Wall.minB ((T.sliceCoordinates ch uu).toNumClass v)
          ((T.sliceCoordinates ch uu).toNumClass w) := by
  rw [OrthogonalSlice.alignmentLocus, Wall.ChargeFamily.mem_alignmentLocus, T.alignmentValue_ofST]
  exact Wall.wall_line_eq ht hA hB

/-! ### The discriminant on a slice -/

/-- The slice discriminant, expanded.  The transverse direction contributes
`2 H² r (G(u) · ch₁) - H² r² G(u)²`, so the walls of one class genuinely move
with `u`.
@isnad1 id=eq.0h8v.s9.dadd305cb471 from=translated src=- shape=e03b868c vocab=d92bc72d
-/
theorem discr_sliceCoordinates (ch : ChernCharacter N D) (uu : U) (E : N) :
    (T.sliceCoordinates ch uu).discr E =
      S.pair T.H (ch.chOne E) ^ 2
        - 2 * S.pair T.H T.H * ch.rank E * ch.chTwo E
        + 2 * S.pair T.H T.H * ch.rank E * S.pair (T.transverse uu) (ch.chOne E)
        - S.pair T.H T.H * ch.rank E ^ 2
          * S.pair (T.transverse uu) (T.transverse uu) := by
  simp only [ChargeCoordinates.discr, T.sliceCoordinates_degree,
    T.sliceCoordinates_rank, T.sliceCoordinates_chTwo,
    T.sliceCoordinates_hyperplaneSquare]
  ring

/-- **The bar discriminant at a slice point is `t²` times the slice
discriminant.**  The `s`-dependence cancels exactly, which is why
`\bar Δ^B_ω` is constant along each vertical line of the half plane.
@isnad1 id=eq.0h8v.s6.f0d7dbd583a9 from=translated src=- shape=1bfcd6c2 vocab=e3ffcae0
-/
theorem barDiscriminant_parameters (ch : ChernCharacter N D) (p : Point U) (E : N) :
    ch.barDiscriminant S (T.parameters p) E =
      p.t ^ 2 * (T.sliceCoordinates ch p.u).discr E := by
  have hHG : S.pair T.H (T.transverse p.u) = 0 := T.orthogonal p.u
  have hGH : S.pair (T.transverse p.u) T.H = 0 := by
    rw [S.pair_comm]; exact hHG
  simp only [DivisorSpace.pair] at hHG hGH
  simp only [ChernCharacter.barDiscriminant, ChernCharacter.twist_chOne,
    ChernCharacter.twist_chTwo, parameters_B, parameters_omega,
    T.discr_sliceCoordinates, DivisorSpace.pair, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hHG, hGH]
  ring

/-- **Bogomolov--Gieseker and a Hodge index discharge the discriminant
hypothesis on every `u`-slice.**  This is what the disjointness and nesting
theorems of `Walls/Numerical/` need, and until now it was available only on the
rank-one transport.
@isnad1 id=le.3h8v.s7.12fb09a0fc10 from=translated src=- shape=8f7e1732 vocab=3b956946
-/
theorem discr_sliceCoordinates_nonneg (ch : ChernCharacter N D) (p : Point U)
    (ht : p.t ≠ 0) (h : S.HodgeIndex (T.parameters p).omega) {E : N}
    (hΔ : 0 ≤ ch.discriminant S E) :
    0 ≤ (T.sliceCoordinates ch p.u).discr E := by
  have hbar : 0 ≤ ch.barDiscriminant S (T.parameters p) E :=
    ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg ch S _ h E hΔ
  rw [T.barDiscriminant_parameters ch p E] at hbar
  have hts : 0 < p.t ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hts
  rw [mul_zero]
  exact hbar

/-- The same, against the alignmentLocus-plane discriminant the `(s,t)` theorems consume.
@isnad1 id=le.3h8v.s7.0a924665280d from=translated src=- shape=c3043272 vocab=44a92920
-/
theorem discr_toNumClass_sliceCoordinates_nonneg (ch : ChernCharacter N D)
    (p : Point U) (ht : p.t ≠ 0) (h : S.HodgeIndex (T.parameters p).omega) {E : N}
    (hΔ : 0 ≤ ch.discriminant S E) :
    0 ≤ Wall.NumClass.discr ((T.sliceCoordinates ch p.u).toNumClass E) := by
  rw [ChargeCoordinates.discr_toNumClass]
  exact T.discr_sliceCoordinates_nonneg ch p ht h hΔ

end OrthogonalSlice

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
