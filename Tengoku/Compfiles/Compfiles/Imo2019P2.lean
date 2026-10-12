/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 2019, Problem 2

In triangle `ABC`, point `A₁` lies on side `BC` and point `B₁` lies on side `AC`. Let `P` and
`Q` be points on segments `AA₁` and `BB₁`, respectively, such that `PQ` is parallel to `AB`.
Let `P₁` be a point on line `PB₁`, such that `B₁` lies strictly between `P` and `P₁`, and
`∠PP₁C = ∠BAC`. Similarly, let `Q₁` be a point on line `QA₁`, such that `A₁` lies strictly
between `Q` and `Q₁`, and `∠CQ₁Q = ∠CBA`.

Prove that points `P`, `Q`, `P₁`, and `Q₁` are concyclic.
-/

open Affine Affine.Simplex EuclideanGeometry FiniteDimensional Module

open scoped Affine EuclideanGeometry Real

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable (V : Type*) (Pt : Type*)

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace Pt]

variable [NormedAddTorsor V Pt]

namespace Imo2019P2

/-
We follow Solution 1 from the
[official solutions](https://www.imo2019.uk/wp-content/uploads/2018/07/solutions-r856.pdf).
Letting the rays `AA₁` and `BB₁` intersect the circumcircle of `ABC` at `A₂` and `B₂`
respectively, we show with an angle chase that `P`, `Q`, `A₂`, `B₂` are concyclic and let `ω` be
the circle through those points. We then show that `C`, `Q₁`, `A₂`, `A₁` are concyclic, and
then that `Q₁` lies on `ω`, and similarly that `P₁` lies on `ω`, so the required four points are
concyclic.

Note that most of the formal proof is actually proving nondegeneracy conditions needed for that
angle chase / concyclicity argument, where an informal solution doesn't discuss those conditions
at all. Also note that (as described in `Geometry.Euclidean.Angle.Oriented.Basic`) the oriented
angles used are modulo `2 * π`, so parts of the angle chase that are only valid for angles modulo
`π` (as used in the informal solution) are represented as equalities of twice angles, which we write
as `(2 : ℤ) • ∡ _ _ _ = (2 : ℤ) • ∡ _ _ _`.
-/

/-
We apply the following conventions for formalizing IMO geometry problems. A problem is assumed
to take place in the plane unless that is clearly not intended, so it is not required to prove
that the points are coplanar (whether or not that in fact follows from the other conditions).
Angles in problem statements are taken to be unoriented. A reference to an angle `∠XYZ` is taken
to imply that `X` and `Z` are not equal to `Y`, since choices of junk values play no role in
informal mathematics, and those implications are included as hypotheses for the problem whether
or not they follow from the other hypotheses. Similar, a reference to `XY` as a line is taken to
imply that `X` does not equal `Y` and that is included as a hypothesis, and a reference to `XY`
being parallel to something is considered a reference to it as a line. However, such an implicit
hypothesis about two points being different is included only once for any given two points (even
if it follows from more than one reference to a line or an angle), if `X ≠ Y` is included then
`Y ≠ X` is not included separately, and such hypotheses are not included in the case where there
is also a reference in the problem to a triangle including those two points, or to strict
betweenness of three points including those two. If betweenness is stated, it is taken to be
strict betweenness. However, segments and sides are taken to include their endpoints (unless
this makes a problem false), although those degenerate cases might not necessarily have been
considered when the problem was formulated and contestants might not have been expected to deal
with them. A reference to a point being on a side or a segment is expressed directly with `Wbtw`
rather than more literally with `affineSegment`.
-/

noncomputable section

/-- A configuration satisfying the conditions of the problem. We define this structure to avoid
passing many hypotheses around as we build up information about the configuration; the final
result for a statement of the problem not using this structure is then deduced from one in terms
of this structure. -/
structure Imo2019q2Cfg where
  (A B C A₁ B₁ P Q P₁ Q₁ : Pt)
  affineIndependent_ABC : AffineIndependent ℝ ![A, B, C]
  wbtw_B_A₁_C : Wbtw ℝ B A₁ C
  wbtw_A_B₁_C : Wbtw ℝ A B₁ C
  wbtw_A_P_A₁ : Wbtw ℝ A P A₁
  wbtw_B_Q_B₁ : Wbtw ℝ B Q B₁
  PQ_parallel_AB : line[ℝ, P, Q] ∥ line[ℝ, A, B]
  -- A hypothesis implicit in the named line.
  P_ne_Q : P ≠ Q
  sbtw_P_B₁_P₁ : Sbtw ℝ P B₁ P₁
  angle_PP₁C_eq_angle_BAC : ∠ P P₁ C = ∠ B A C
  -- A hypothesis implicit in the first named angle.
  C_ne_P₁ : C ≠ P₁
  sbtw_Q_A₁_Q₁ : Sbtw ℝ Q A₁ Q₁
  angle_CQ₁Q_eq_angle_CBA : ∠ C Q₁ Q = ∠ C B A
  -- A hypothesis implicit in the first named angle.
  C_ne_Q₁ : C ≠ Q₁

/-- A default choice of orientation, for lemmas that need to pick one. -/
@[implicit_reducible]
def someOrientation  [hd2 : Fact (finrank ℝ V = 2)] : Module.Oriented ℝ V (Fin 2) :=
  ⟨Basis.orientation (finBasisOfFinrankEq _ _ hd2.out)⟩

variable {V Pt}

namespace Imo2019q2Cfg

variable (cfg : Imo2019q2Cfg V Pt)

/-- The configuration has symmetry, allowing results proved for one point to be applied for
another (where the informal solution says "similarly"). -/
def symm : Imo2019q2Cfg V Pt where
  A := cfg.B
  B := cfg.A
  C := cfg.C
  A₁ := cfg.B₁
  B₁ := cfg.A₁
  P := cfg.Q
  Q := cfg.P
  P₁ := cfg.Q₁
  Q₁ := cfg.P₁
  affineIndependent_ABC := by
    rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 1)]
    convert cfg.affineIndependent_ABC using 1
    ext x
    fin_cases x <;> rfl
  wbtw_B_A₁_C := cfg.wbtw_A_B₁_C
  wbtw_A_B₁_C := cfg.wbtw_B_A₁_C
  wbtw_A_P_A₁ := cfg.wbtw_B_Q_B₁
  wbtw_B_Q_B₁ := cfg.wbtw_A_P_A₁
  PQ_parallel_AB := Set.pair_comm cfg.P cfg.Q ▸ Set.pair_comm cfg.A cfg.B ▸ cfg.PQ_parallel_AB
  P_ne_Q := cfg.P_ne_Q.symm
  sbtw_P_B₁_P₁ := cfg.sbtw_Q_A₁_Q₁
  angle_PP₁C_eq_angle_BAC :=
    angle_comm cfg.C cfg.Q₁ cfg.Q ▸ angle_comm cfg.C cfg.B cfg.A ▸ cfg.angle_CQ₁Q_eq_angle_CBA
  C_ne_P₁ := cfg.C_ne_Q₁
  sbtw_Q_A₁_Q₁ := cfg.sbtw_P_B₁_P₁
  angle_CQ₁Q_eq_angle_CBA :=
    angle_comm cfg.P cfg.P₁ cfg.C ▸ angle_comm cfg.B cfg.A cfg.C ▸ cfg.angle_PP₁C_eq_angle_BAC
  C_ne_Q₁ := cfg.C_ne_P₁

/- ### Configuration properties that are obvious from the diagram, and construction of the
points `A₂` and `B₂` -/

/--
@isnad1 id=ne.0h3v.s5.bfaf02e2e68b from=translated src=- shape=a6dc988e vocab=1bd83371
-/
theorem A_ne_B : cfg.A ≠ cfg.B :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (0 : Fin 3) ≠ 1)

/--
@isnad1 id=ne.0h3v.s5.475d9890c1db from=translated src=- shape=a6dc988e vocab=ff82b2f0
-/
theorem B_ne_C : cfg.B ≠ cfg.C :=
  cfg.affineIndependent_ABC.injective.ne (by decide : (1 : Fin 3) ≠ 2)

/--
@isnad1 id=not.0h3v.s6.0c715d20e154 from=translated src=- shape=66f83bdc vocab=a93b5fb4
-/
theorem not_collinear_ABC : ¬Collinear ℝ ({cfg.A, cfg.B, cfg.C} : Set Pt) :=
  affineIndependent_iff_not_collinear_set.1 cfg.affineIndependent_ABC

/-- `ABC` as a `Triangle`. -/
def triangleABC : Triangle ℝ Pt :=
  ⟨_, cfg.affineIndependent_ABC⟩

/--
@isnad1 id=mem.0h3v.s6.e2ffab88df78 from=translated src=- shape=1269d495 vocab=afa472ea
-/
theorem A_mem_circumsphere : cfg.A ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 0

/--
@isnad1 id=mem.0h3v.s6.9c959e9cd9d3 from=translated src=- shape=1269d495 vocab=42aa75bc
-/
theorem B_mem_circumsphere : cfg.B ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 1

/--
@isnad1 id=mem.0h3v.s6.7a2fac8894f5 from=translated src=- shape=1269d495 vocab=5db302a0
-/
theorem C_mem_circumsphere : cfg.C ∈ cfg.triangleABC.circumsphere :=
  cfg.triangleABC.mem_circumsphere 2

/--
@isnad1 id=eq.0h3v.s7.daa34d5337ff from=translated src=- shape=02ee3ce1 vocab=f1dbbfa9
-/
theorem symm_triangleABC : cfg.symm.triangleABC = cfg.triangleABC.reindex (Equiv.swap 0 1) := by
  ext i; fin_cases i <;> rfl

/--
@isnad1 id=eq.0h3v.s6.871bfee2610d from=translated src=- shape=68368ba2 vocab=47b5aa1a
-/
theorem symm_triangleABC_circumsphere :
    cfg.symm.triangleABC.circumsphere = cfg.triangleABC.circumsphere := by
  rw [symm_triangleABC, Affine.Simplex.circumsphere_reindex]

/-- `A₂` is the second point of intersection of the ray `AA₁` with the circumcircle of `ABC`. -/
def A₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.A (cfg.A₁ -ᵥ cfg.A)

/-- `B₂` is the second point of intersection of the ray `BB₁` with the circumcircle of `ABC`. -/
def B₂ : Pt :=
  cfg.triangleABC.circumsphere.secondInter cfg.B (cfg.B₁ -ᵥ cfg.B)

/--
@isnad1 id=mem.0h3v.s6.811b337d7dd2 from=translated src=- shape=1269d495 vocab=1aba5fd5
-/
theorem A₂_mem_circumsphere : cfg.A₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.A_mem_circumsphere

/--
@isnad1 id=mem.0h3v.s6.97cec32ca1c4 from=translated src=- shape=1269d495 vocab=426eea62
-/
theorem B₂_mem_circumsphere : cfg.B₂ ∈ cfg.triangleABC.circumsphere :=
  (Sphere.secondInter_mem _).2 cfg.B_mem_circumsphere

/--
@isnad1 id=eq.0h3v.s5.29b0d8c5db9e from=translated src=- shape=b39df9bb vocab=6a77bda2
-/
theorem symm_A₂ : cfg.symm.A₂ = cfg.B₂ := by simp_rw [A₂, B₂, symm_triangleABC_circumsphere]; rfl

/--
@isnad1 id=parallel.0h3v.s7.680b819507ba from=translated src=- shape=270af0b6 vocab=84927e4a
-/
theorem QP_parallel_BA : line[ℝ, cfg.Q, cfg.P] ∥ line[ℝ, cfg.B, cfg.A] := by
  rw [Set.pair_comm cfg.Q, Set.pair_comm cfg.B]; exact cfg.PQ_parallel_AB

/--
@isnad1 id=ne.0h3v.s5.e1708855f354 from=translated src=- shape=a6dc988e vocab=124fa068
-/
theorem A_ne_A₁ : cfg.A ≠ cfg.A₁ := by
  intro h
  have h' := cfg.not_collinear_ABC
  rw [h, Set.insert_comm] at h'
  exact h' cfg.wbtw_B_A₁_C.collinear

/--
@isnad1 id=collinea.0h3v.s6.9bc5704ebb57 from=translated src=- shape=5061105b vocab=5bcef56d
-/
theorem collinear_PAA₁A₂ : Collinear ℝ ({cfg.P, cfg.A, cfg.A₁, cfg.A₂} : Set Pt) := by
  rw [A₂,
    (cfg.triangleABC.circumsphere.secondInter_collinear cfg.A cfg.A₁).collinear_insert_iff_of_ne
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) cfg.A_ne_A₁,
    Set.insert_comm]
  exact cfg.wbtw_A_P_A₁.collinear

/--
@isnad1 id=ne.0h3v.s5.8c7d7a1c8861 from=translated src=- shape=a6dc988e vocab=32a7d75f
-/
theorem A₁_ne_C : cfg.A₁ ≠ cfg.C := by
  intro h
  have hsbtw := cfg.sbtw_Q_A₁_Q₁
  rw [h] at hsbtw
  have ha := hsbtw.angle₂₃₁_eq_zero
  rw [angle_CQ₁Q_eq_angle_CBA, angle_comm] at ha
  exact (angle_ne_zero_of_not_collinear cfg.not_collinear_ABC) ha

/--
@isnad1 id=ne.0h3v.s5.d808cc596941 from=translated src=- shape=a6dc988e vocab=13982ef0
-/
theorem B₁_ne_C : cfg.B₁ ≠ cfg.C :=
  cfg.symm.A₁_ne_C

/--
@isnad1 id=not.0h3v.s7.379bf55532e4 from=translated src=- shape=fcdfbf94 vocab=5aa62000
-/
theorem Q_not_mem_CB : cfg.Q ∉ line[ℝ, cfg.C, cfg.B] := by
  intro hQ
  have hQ₁ : cfg.Q₁ ∈ line[ℝ, cfg.C, cfg.B] :=
    affineSpan_pair_le_of_mem_of_mem hQ cfg.wbtw_B_A₁_C.symm.mem_affineSpan
      cfg.sbtw_Q_A₁_Q₁.right_mem_affineSpan
  have hc : Collinear ℝ ({cfg.C, cfg.Q₁, cfg.Q} : Set Pt) :=
    collinear_triple_of_mem_affineSpan_pair (left_mem_affineSpan_pair _ _ _) hQ₁ hQ
  rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, cfg.angle_CQ₁Q_eq_angle_CBA,
    or_iff_right cfg.C_ne_Q₁, or_iff_right cfg.sbtw_Q_A₁_Q₁.left_ne_right, angle_comm] at hc
  exact cfg.not_collinear_ABC (hc.elim collinear_of_angle_eq_zero collinear_of_angle_eq_pi)

/--
@isnad1 id=ne.0h3v.s5.c9e4061f17c7 from=translated src=- shape=a6dc988e vocab=1c18e77b
-/
theorem Q_ne_B : cfg.Q ≠ cfg.B := by
  intro h
  have h' := cfg.Q_not_mem_CB
  rw [h] at h'
  exact h' (right_mem_affineSpan_pair _ _ _)

/--
@isnad1 id=soppside.0h3v.s7.a78739f58534 from=translated src=- shape=c06b0091 vocab=5ae935d9
-/
theorem sOppSide_CB_Q_Q₁ : line[ℝ, cfg.C, cfg.B].SOppSide cfg.Q cfg.Q₁ :=
  cfg.sbtw_Q_A₁_Q₁.sOppSide_of_notMem_of_mem cfg.Q_not_mem_CB cfg.wbtw_B_A₁_C.symm.mem_affineSpan

/- ### Relate the orientations of different angles in the configuration -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

/--
@isnad1 id=eq.0h3v.s7.540a8195fd45 from=translated src=- shape=dd35d9c6 vocab=5225d3bd
-/
theorem oangle_CQ₁Q_sign_eq_oangle_CBA_sign [Fact (finrank ℝ V = 2)] :
    (∡ cfg.C cfg.Q₁ cfg.Q).sign = (∡ cfg.C cfg.B cfg.A).sign := by
  rw [← cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right,
    cfg.sOppSide_CB_Q_Q₁.oangle_sign_eq_neg (left_mem_affineSpan_pair ℝ cfg.C cfg.B)
      cfg.wbtw_B_A₁_C.symm.mem_affineSpan,
    ← Real.Angle.sign_neg, ← oangle_rev,
    cfg.wbtw_B_A₁_C.oangle_sign_eq_of_ne_right cfg.Q cfg.A₁_ne_C, oangle_rotate_sign,
    cfg.wbtw_B_Q_B₁.oangle_eq_right cfg.Q_ne_B,
    cfg.wbtw_A_B₁_C.symm.oangle_sign_eq_of_ne_left cfg.B cfg.B₁_ne_C.symm]

/--
@isnad1 id=eq.0h3v.s7.5d92c02fcf59 from=translated src=- shape=53ac872a vocab=916116a5
-/
theorem oangle_CQ₁Q_eq_oangle_CBA [Fact (finrank ℝ V = 2)] :
    ∡ cfg.C cfg.Q₁ cfg.Q = ∡ cfg.C cfg.B cfg.A :=
  oangle_eq_of_angle_eq_of_sign_eq cfg.angle_CQ₁Q_eq_angle_CBA
    cfg.oangle_CQ₁Q_sign_eq_oangle_CBA_sign

end Oriented

/- ### More obvious configuration properties -/

section

variable [hd2 : Fact (finrank ℝ V = 2)]

/--
@isnad1 id=ne.0h3v.s6.633b9a8b959c from=translated src=- shape=0d43da9c vocab=c0f39519
-/
theorem A₁_ne_B : cfg.A₁ ≠ cfg.B := by
  intro h
  have hwbtw := cfg.wbtw_A_P_A₁
  rw [h] at hwbtw
  have hPQ : line[ℝ, cfg.P, cfg.Q] = line[ℝ, cfg.A, cfg.B] := by
    rw [AffineSubspace.eq_iff_direction_eq_of_mem (left_mem_affineSpan_pair _ _ _)
      hwbtw.mem_affineSpan]
    exact cfg.PQ_parallel_AB.direction_eq
  have := someOrientation V
  have haQ : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A := by
    rw [Collinear.two_zsmul_oangle_eq_right _ cfg.A_ne_B cfg.Q_ne_B]
    rw [Set.pair_comm, Set.insert_comm]
    refine collinear_insert_of_mem_affineSpan_pair ?_
    rw [← hPQ]
    exact right_mem_affineSpan_pair _ _ _
  have ha : (2 : ℤ) • ∡ cfg.C cfg.B cfg.Q = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q := by
    rw [oangle_CQ₁Q_eq_oangle_CBA, haQ]
  have hn : ¬Collinear ℝ ({cfg.C, cfg.B, cfg.Q} : Set Pt) := by
    rw [collinear_iff_of_two_zsmul_oangle_eq haQ, Set.pair_comm, Set.insert_comm, Set.pair_comm]
    exact cfg.not_collinear_ABC
  have hc := cospherical_of_two_zsmul_oangle_eq_of_not_collinear ha hn
  have hBQ₁ : cfg.B ≠ cfg.Q₁ := by rw [← h]; exact cfg.sbtw_Q_A₁_Q₁.ne_right
  have hBQ₁Q : AffineIndependent ℝ ![cfg.B, cfg.Q₁, cfg.Q] :=
    (hc.subset (by simp)).affineIndependent_of_ne hBQ₁
      cfg.Q_ne_B.symm cfg.sbtw_Q_A₁_Q₁.left_ne_right.symm
  refine affineIndependent_iff_not_collinear_set.1 hBQ₁Q ?_
  rw [← h, Set.pair_comm, Set.insert_comm]
  exact cfg.sbtw_Q_A₁_Q₁.wbtw.collinear

/--
@isnad1 id=sbtw.0h3v.s6.6eb176df1462 from=translated src=- shape=3245a848 vocab=12c47caf
-/
theorem sbtw_B_A₁_C : Sbtw ℝ cfg.B cfg.A₁ cfg.C :=
  ⟨cfg.wbtw_B_A₁_C, cfg.A₁_ne_B, cfg.A₁_ne_C⟩

/--
@isnad1 id=sbtw.0h3v.s6.ee73ee2dda49 from=translated src=- shape=3245a848 vocab=4bd3d400
-/
theorem sbtw_A_B₁_C : Sbtw ℝ cfg.A cfg.B₁ cfg.C :=
  cfg.symm.sbtw_B_A₁_C

/--
@isnad1 id=sbtw.0h3v.s6.03d053149a56 from=translated src=- shape=3245a848 vocab=29745baa
-/
theorem sbtw_A_A₁_A₂ : Sbtw ℝ cfg.A cfg.A₁ cfg.A₂ := by
  refine Sphere.sbtw_secondInter cfg.A_mem_circumsphere ?_
  convert cfg.sbtw_B_A₁_C.dist_lt_max_dist _
  change _ = max (dist (cfg.triangleABC.points 1) _) (dist (cfg.triangleABC.points 2) _)
  simp_rw [circumsphere_center, circumsphere_radius, dist_circumcenter_eq_circumradius, max_self]

/--
@isnad1 id=sbtw.0h3v.s6.48c648cd8a07 from=translated src=- shape=3245a848 vocab=8d36b997
-/
theorem sbtw_B_B₁_B₂ : Sbtw ℝ cfg.B cfg.B₁ cfg.B₂ := by
  rw [← cfg.symm_A₂]; exact cfg.symm.sbtw_A_A₁_A₂

/--
@isnad1 id=ne.0h3v.s6.4be4bd81100e from=translated src=- shape=0d43da9c vocab=7b920b32
-/
theorem A₂_ne_A : cfg.A₂ ≠ cfg.A :=
  cfg.sbtw_A_A₁_A₂.left_ne_right.symm

/--
@isnad1 id=ne.0h3v.s6.654b833cce3a from=translated src=- shape=0d43da9c vocab=3219e202
-/
theorem A₂_ne_P : cfg.A₂ ≠ cfg.P :=
  (cfg.sbtw_A_A₁_A₂.trans_wbtw_left_ne cfg.wbtw_A_P_A₁).symm

/--
@isnad1 id=ne.0h3v.s6.a21ad6b46f34 from=translated src=- shape=0d43da9c vocab=70d86860
-/
theorem A₂_ne_B : cfg.A₂ ≠ cfg.B := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁
  have hc : Collinear ℝ ({cfg.A, cfg.C, cfg.B, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affineSpan
      cfg.sbtw_B_A₁_C.right_mem_affineSpan
  exact cfg.not_collinear_ABC (hc.subset (by simp [Set.insert_subset_iff]))

/--
@isnad1 id=ne.0h3v.s6.0fb7449371f9 from=translated src=- shape=0d43da9c vocab=40793692
-/
theorem A₂_ne_C : cfg.A₂ ≠ cfg.C := by
  intro h
  have h₁ := cfg.sbtw_A_A₁_A₂
  rw [h] at h₁
  have hc : Collinear ℝ ({cfg.A, cfg.B, cfg.C, cfg.A₁} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair h₁.left_mem_affineSpan
      cfg.sbtw_B_A₁_C.left_mem_affineSpan
  exact cfg.not_collinear_ABC (hc.subset (by simp [Set.insert_subset_iff]))

/--
@isnad1 id=ne.0h3v.s6.078e942bb35e from=translated src=- shape=0d43da9c vocab=543ee126
-/
theorem B₂_ne_B : cfg.B₂ ≠ cfg.B := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_A

/--
@isnad1 id=ne.0h3v.s6.59d6dca1cd19 from=translated src=- shape=0d43da9c vocab=b195b337
-/
theorem B₂_ne_Q : cfg.B₂ ≠ cfg.Q := by rw [← symm_A₂]; exact cfg.symm.A₂_ne_P

/--
@isnad1 id=ne.0h3v.s6.c6668e1955f7 from=translated src=- shape=0d43da9c vocab=bb688625
-/
theorem B₂_ne_A₂ : cfg.B₂ ≠ cfg.A₂ := by
  intro h
  have hA : Sbtw ℝ (cfg.triangleABC.points 1) cfg.A₁ (cfg.triangleABC.points 2) := cfg.sbtw_B_A₁_C
  have hB : Sbtw ℝ (cfg.triangleABC.points 0) cfg.B₁ (cfg.triangleABC.points 2) := cfg.sbtw_A_B₁_C
  have hA' : cfg.A₂ ∈ line[ℝ, cfg.triangleABC.points 0, cfg.A₁] :=
    Sphere.secondInter_vsub_mem_affineSpan _ _ _
  have hB' : cfg.A₂ ∈ line[ℝ, cfg.triangleABC.points 1, cfg.B₁] := by
    rw [← h]; exact Sphere.secondInter_vsub_mem_affineSpan _ _ _
  exact (sbtw_of_sbtw_of_sbtw_of_mem_affineSpan_pair (by decide) hA hB hA' hB').symm.not_rotate
    cfg.sbtw_A_A₁_A₂.wbtw

/--
@isnad1 id=wbtw.0h3v.s6.b91e3e3110ae from=translated src=- shape=3245a848 vocab=fce24a7f
-/
theorem wbtw_B_Q_B₂ : Wbtw ℝ cfg.B cfg.Q cfg.B₂ :=
  cfg.sbtw_B_B₁_B₂.wbtw.trans_left cfg.wbtw_B_Q_B₁

/- ### The first equality in the first angle chase in the solution -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

/--
@isnad1 id=eq.0h3v.s7.cce319e49ab6 from=translated src=- shape=2aaa31a8 vocab=382b5d5f
-/
theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ := by
  refine two_zsmul_oangle_of_parallel cfg.QP_parallel_BA ?_
  convert AffineSubspace.Parallel.refl (k := ℝ) (P := Pt) _ using 1
  rw [cfg.collinear_PAA₁A₂.affineSpan_eq_of_ne (by simp) (by simp) cfg.A₂_ne_A,
    cfg.collinear_PAA₁A₂.affineSpan_eq_of_ne (by simp) (by simp) cfg.A₂_ne_P]

end Oriented

/- ### More obvious configuration properties -/

/--
@isnad1 id=not.0h3v.s7.4b182622a687 from=translated src=- shape=a88a4f3f vocab=1004b8e5
-/
theorem not_collinear_QPA₂ : ¬Collinear ℝ ({cfg.Q, cfg.P, cfg.A₂} : Set Pt) := by
  have := someOrientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂, ←
    affineIndependent_iff_not_collinear_set]
  have h : Cospherical ({cfg.B, cfg.A, cfg.A₂} : Set Pt) := by
    refine cfg.triangleABC.circumsphere.cospherical.subset ?_
    simp only [Set.insert_subset_iff, cfg.A_mem_circumsphere, cfg.B_mem_circumsphere,
      cfg.A₂_mem_circumsphere, Sphere.mem_coe, Set.singleton_subset_iff, and_true]
  exact h.affineIndependent_of_ne cfg.A_ne_B.symm cfg.A₂_ne_B.symm cfg.A₂_ne_A.symm

/--
@isnad1 id=ne.0h3v.s6.ac32a1a4a6e8 from=translated src=- shape=0d43da9c vocab=ef2b5582
-/
theorem Q₁_ne_A₂ : cfg.Q₁ ≠ cfg.A₂ := by
  intro h
  have h₁ := cfg.sbtw_Q_A₁_Q₁
  rw [h] at h₁
  have hA₂ := cfg.sbtw_A_A₁_A₂.right_mem_affineSpan
  have hQ : cfg.Q ∈ line[ℝ, cfg.A, cfg.A₁] :=
    affineSpan_pair_le_of_left_mem hA₂ h₁.left_mem_affineSpan
  exact cfg.not_collinear_QPA₂
    (collinear_triple_of_mem_affineSpan_pair hQ cfg.wbtw_A_P_A₁.mem_affineSpan hA₂)

/--
@isnad1 id=affinein.0h3v.s7.721232abaa0a from=translated src=- shape=2cae88e7 vocab=4eeb0f9d
-/
theorem affineIndependent_QPA₂ : AffineIndependent ℝ ![cfg.Q, cfg.P, cfg.A₂] :=
  affineIndependent_iff_not_collinear_set.2 cfg.not_collinear_QPA₂

/--
@isnad1 id=affinein.0h3v.s7.7e905aa7340a from=translated src=- shape=2cae88e7 vocab=2fc5a5e8
-/
theorem affineIndependent_PQB₂ : AffineIndependent ℝ ![cfg.P, cfg.Q, cfg.B₂] := by
  rw [← symm_A₂]; exact cfg.symm.affineIndependent_QPA₂

/-- `QPA₂` as a `Triangle`. -/
def triangleQPA₂ : Triangle ℝ Pt := ⟨_, cfg.affineIndependent_QPA₂⟩

/-- `PQB₂` as a `Triangle`. -/
def trianglePQB₂ : Triangle ℝ Pt := ⟨_, cfg.affineIndependent_PQB₂⟩

/--
@isnad1 id=eq.0h3v.s7.30bda4047a30 from=translated src=- shape=1ab9f97d vocab=a3213f8d
-/
theorem symm_triangleQPA₂ : cfg.symm.triangleQPA₂ = cfg.trianglePQB₂ := by
  simp_rw [trianglePQB₂, ← symm_A₂]; ext i; fin_cases i <;> rfl

/-- `ω` is the circle containing `Q`, `P` and `A₂`, which will be shown also to contain `B₂`,
`P₁` and `Q₁`. -/
def ω : Sphere Pt := cfg.triangleQPA₂.circumsphere

/--
@isnad1 id=mem.0h3v.s6.924f9ec42532 from=translated src=- shape=13b2e409 vocab=fe853380
-/
theorem P_mem_ω : cfg.P ∈ cfg.ω := cfg.triangleQPA₂.mem_circumsphere 1

/--
@isnad1 id=mem.0h3v.s6.8a7305d71783 from=translated src=- shape=13b2e409 vocab=5f070618
-/
theorem Q_mem_ω : cfg.Q ∈ cfg.ω := cfg.triangleQPA₂.mem_circumsphere 0

/- ### The rest of the first angle chase in the solution -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

/--
@isnad1 id=eq.0h3v.s7.521c8950c77e from=translated src=- shape=fcabd48a vocab=4c775f77
-/
theorem two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ :=
  calc
    (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :=
      cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂
    _ = (2 : ℤ) • ∡ cfg.B cfg.B₂ cfg.A₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.A_mem_circumsphere
        cfg.B₂_mem_circumsphere cfg.A₂_mem_circumsphere cfg.A_ne_B cfg.A₂_ne_A.symm cfg.B₂_ne_B
        cfg.B₂_ne_A₂)
    _ = (2 : ℤ) • ∡ cfg.Q cfg.B₂ cfg.A₂ := by
      rw [cfg.wbtw_B_Q_B₂.symm.oangle_eq_left cfg.B₂_ne_Q.symm]

end Oriented

/- ### Conclusions from that first angle chase -/

/--
@isnad1 id=cospheri.0h3v.s7.02dfd4f6adcd from=translated src=- shape=53d86073 vocab=2a150469
-/
theorem cospherical_QPB₂A₂ : Cospherical ({cfg.Q, cfg.P, cfg.B₂, cfg.A₂} : Set Pt) :=
  have := someOrientation V
  cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_QB₂A₂ cfg.not_collinear_QPA₂

/--
@isnad1 id=eq.0h3v.s6.41339aebe6d1 from=translated src=- shape=78ee7c9a vocab=c1b0e48f
-/
theorem symm_ω : cfg.symm.ω = cfg.ω := by
  rw [ω, symm_triangleQPA₂, ω]
  refine circumsphere_eq_of_cospherical hd2.out cfg.cospherical_QPB₂A₂ ?_ ?_ <;>
    simp [triangleQPA₂, trianglePQB₂, Matrix.range_cons, Set.insert_subset_iff]

/- ### The second angle chase in the solution -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

/--
@isnad1 id=eq.0h3v.s7.318f40397253 from=translated src=- shape=d210ef62 vocab=f8301299
-/
theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA :
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A := by
      rw [cfg.sbtw_A_A₁_A₂.symm.oangle_eq_right]
    _ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
      Sphere.two_zsmul_oangle_eq cfg.C_mem_circumsphere cfg.A₂_mem_circumsphere
        cfg.B_mem_circumsphere cfg.A_mem_circumsphere cfg.A₂_ne_C cfg.A₂_ne_A cfg.B_ne_C
        cfg.A_ne_B.symm

/--
@isnad1 id=eq.0h3v.s7.91b596bab92e from=translated src=- shape=fcabd48a vocab=5a3c9523
-/
theorem two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ :
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ :=
  calc
    (2 : ℤ) • ∡ cfg.C cfg.A₂ cfg.A₁ = (2 : ℤ) • ∡ cfg.C cfg.B cfg.A :=
      cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA
    _ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.Q := by rw [oangle_CQ₁Q_eq_oangle_CBA]
    _ = (2 : ℤ) • ∡ cfg.C cfg.Q₁ cfg.A₁ := by rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_right]

end Oriented

/- ### Conclusions from that second angle chase -/

/--
@isnad1 id=not.0h3v.s7.b3623f3dbe68 from=translated src=- shape=a88a4f3f vocab=c9f38288
-/
theorem not_collinear_CA₂A₁ : ¬Collinear ℝ ({cfg.C, cfg.A₂, cfg.A₁} : Set Pt) := by
  have := someOrientation V
  rw [collinear_iff_of_two_zsmul_oangle_eq cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CBA,
    Set.pair_comm, Set.insert_comm, Set.pair_comm]
  exact cfg.not_collinear_ABC

/--
@isnad1 id=cospheri.0h3v.s7.e067c5ed0892 from=translated src=- shape=53d86073 vocab=6e72b9d8
-/
theorem cospherical_A₁Q₁CA₂ : Cospherical ({cfg.A₁, cfg.Q₁, cfg.C, cfg.A₂} : Set Pt) :=
  have := someOrientation V
  (cospherical_of_two_zsmul_oangle_eq_of_not_collinear
    cfg.two_zsmul_oangle_CA₂A₁_eq_two_zsmul_oangle_CQ₁A₁ cfg.not_collinear_CA₂A₁).subset
    (by simp [Set.insert_subset_iff])

/- ### The third angle chase in the solution -/

section Oriented

variable [Module.Oriented ℝ V (Fin 2)]

/--
@isnad1 id=eq.0h3v.s7.26abef96f8d2 from=translated src=- shape=fcabd48a vocab=423d02fd
-/
theorem two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂ :
    (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ :=
  calc
    (2 : ℤ) • ∡ cfg.Q cfg.Q₁ cfg.A₂ = (2 : ℤ) • ∡ cfg.A₁ cfg.Q₁ cfg.A₂ := by
      rw [cfg.sbtw_Q_A₁_Q₁.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.A₁ cfg.C cfg.A₂ :=
      (cfg.cospherical_A₁Q₁CA₂.two_zsmul_oangle_eq cfg.sbtw_Q_A₁_Q₁.right_ne cfg.Q₁_ne_A₂
        cfg.A₁_ne_C.symm cfg.A₂_ne_C.symm)
    _ = (2 : ℤ) • ∡ cfg.B cfg.C cfg.A₂ := by rw [cfg.sbtw_B_A₁_C.symm.oangle_eq_left]
    _ = (2 : ℤ) • ∡ cfg.B cfg.A cfg.A₂ :=
      (Sphere.two_zsmul_oangle_eq cfg.B_mem_circumsphere cfg.C_mem_circumsphere
        cfg.A_mem_circumsphere cfg.A₂_mem_circumsphere cfg.B_ne_C.symm cfg.A₂_ne_C.symm cfg.A_ne_B
        cfg.A₂_ne_A.symm)
    _ = (2 : ℤ) • ∡ cfg.Q cfg.P cfg.A₂ := cfg.two_zsmul_oangle_QPA₂_eq_two_zsmul_oangle_BAA₂.symm

end Oriented

/- ### Conclusions from that third angle chase -/

/--
@isnad1 id=mem.0h3v.s6.28db42fff02e from=translated src=- shape=13b2e409 vocab=14edb9d1
-/
theorem Q₁_mem_ω : cfg.Q₁ ∈ cfg.ω :=
  have := someOrientation V
  Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq (by decide : (0 : Fin 3) ≠ 1)
    (by decide : (0 : Fin 3) ≠ 2) (by decide) cfg.two_zsmul_oangle_QQ₁A₂_eq_two_zsmul_oangle_QPA₂

/--
@isnad1 id=mem.0h3v.s6.c14eee26e8eb from=translated src=- shape=13b2e409 vocab=660294bc
-/
theorem P₁_mem_ω : cfg.P₁ ∈ cfg.ω := by rw [← symm_ω]; exact cfg.symm.Q₁_mem_ω

/--
@isnad1 id=concycli.0h3v.s7.4743bf7e292b from=translated src=- shape=58ae6f25 vocab=0c234d8f
-/
theorem result : Concyclic ({cfg.P, cfg.Q, cfg.P₁, cfg.Q₁} : Set Pt) :=
  ⟨cospherical_iff_exists_sphere.2 ⟨cfg.ω, by
      simp [Set.insert_subset_iff, cfg.P_mem_ω, cfg.Q_mem_ω, cfg.P₁_mem_ω, cfg.Q₁_mem_ω]⟩,
    coplanar_of_fact_finrank_eq_two _⟩

end

end Imo2019q2Cfg

end

end Imo2019P2
