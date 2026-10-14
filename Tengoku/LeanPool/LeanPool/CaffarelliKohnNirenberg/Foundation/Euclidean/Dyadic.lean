/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# Dyadic cubes in the native three-dimensional carrier

The cubes use the half-open product grid on `Vec3 = Fin 3 → ℝ`.  The scale
index is integral so that parent and child cubes are represented uniformly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

/-- Integer lattice coordinates locating a dyadic cube in three dimensions. -/
abbrev DyadicCorner := Fin 3 → ℤ

/-- Integer scale and lattice corner specifying a half-open dyadic cube. -/
structure DyadicIndex where
  /-- Dyadic scale index, with side length `2 ^ (-scale)`. -/
  scale : ℤ
  /-- Integer lattice corner of the dyadic cube. -/
  corner : DyadicCorner

/-- Side length of the dyadic grid at integer scale `k`. -/
def dyadicScale (k : ℤ) : ℝ := (2 : ℝ) ^ (-k : ℤ)

/-- Half-open dyadic cube with scale index `k` and lattice corner `a`. -/
def dyadicCube (k : ℤ) (a : DyadicCorner) : Set Vec3 :=
  Set.univ.pi (fun i => Ico ((a i : ℝ) * dyadicScale k)
    (((a i : ℝ) + 1) * dyadicScale k))

/-- Center of a dyadic cube in native Euclidean coordinates. -/
def dyadicCubeCenter (k : ℤ) (a : DyadicCorner) : Vec3 :=
  fun i => ((a i : ℝ) + 1 / 2) * dyadicScale k

/-- Lattice corner of the unique grid cube containing a point. -/
def dyadicCorner (k : ℤ) (x : Vec3) : DyadicCorner :=
  fun i => ⌊x i / dyadicScale k⌋

/-- Immediate containing dyadic cube at the next coarser scale. -/
def dyadicParent (Q : DyadicIndex) : DyadicIndex :=
  { scale := Q.scale - 1
    corner := fun i => Q.corner i / 2 }

/--
@isnad1 id=iff.0h3v.s6.034c7c383440 from=translated src=- shape=759db763 vocab=585e577c
-/
@[simp] theorem mem_dyadicCube {k : ℤ} {a : DyadicCorner} {x : Vec3} :
    x ∈ dyadicCube k a ↔
      ∀ i, (a i : ℝ) * dyadicScale k ≤ x i ∧
        x i < ((a i : ℝ) + 1) * dyadicScale k := by
  simp [dyadicCube]

/--
@isnad1 id=lt.0h1v.s3.87be62c7a409 from=translated src=- shape=b9369acb vocab=ca4dac59
-/
theorem dyadicScale_pos (k : ℤ) : 0 < dyadicScale k := by
  dsimp [dyadicScale]
  positivity

/--
@isnad1 id=measurab.0h2v.s5.ca5aa3d76b1e from=translated src=- shape=6ad8120f vocab=f1292d9b
-/
theorem dyadicCube_measurable (k : ℤ) (a : DyadicCorner) :
    MeasurableSet (dyadicCube k a) := by
  apply MeasurableSet.pi Set.countable_univ
  intro i hi
  exact measurableSet_Ico

/--
@isnad1 id=eq.0h2v.s7.77a19f03daec from=translated src=- shape=a04e0712 vocab=f3f483f7
-/
theorem volume_dyadicCube (k : ℤ) (a : DyadicCorner) :
    volume (dyadicCube k a) = ENNReal.ofReal (dyadicScale k) ^ (3 : ℕ) := by
  rw [dyadicCube, Real.volume_pi_Ico]
  simp only [add_mul, one_mul, add_sub_cancel_left]
  norm_num [Fin.prod_univ_succ]

/--
@isnad1 id=eq.0h2v.s7.6a2db1cee621 from=translated src=- shape=26a5bcf2 vocab=c13277b2
-/
theorem volume_dyadicCube_eq_pow (k : ℤ) (a : DyadicCorner) :
    volume (dyadicCube k a) = ENNReal.ofReal ((8 : ℝ) ^ (-k : ℤ)) := by
  rw [volume_dyadicCube]
  rw [← ENNReal.ofReal_pow (dyadicScale_pos k).le]
  congr 1
  dsimp [dyadicScale]
  calc
    ((2 : ℝ) ^ (-k : ℤ)) ^ (3 : ℕ) = (2 : ℝ) ^ (3 * (-k : ℤ)) := by
      symm
      exact zpow_mul' 2 3 (-k)
    _ = ((2 : ℝ) ^ (3 : ℤ)) ^ (-k : ℤ) := by
      exact zpow_mul 2 3 (-k)
    _ = (8 : ℝ) ^ (-k : ℤ) := by norm_num

/--
@isnad1 id=nonempty.0h2v.s3.a0b7330b3ffe from=translated src=- shape=6ad8120f vocab=f85448fe
-/
theorem dyadicCube_nonempty (k : ℤ) (a : DyadicCorner) :
    (dyadicCube k a).Nonempty := by
  refine ⟨dyadicCubeCenter k a, ?_⟩
  rw [mem_dyadicCube]
  dsimp [dyadicCubeCenter]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  constructor <;> nlinarith only [hs]

/--
@isnad1 id=mem.0h2v.s4.eaec7f3ad0b3 from=translated src=- shape=febe5707 vocab=2aa3e152
-/
theorem mem_dyadicCube_of_corner (k : ℤ) (x : Vec3) :
    x ∈ dyadicCube k (dyadicCorner k x) := by
  rw [mem_dyadicCube]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  constructor
  · exact (le_div_iff₀ hs).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _)

/--
@isnad1 id=eq.2h4v.s5.87c344a7aabd from=translated src=- shape=31efe392 vocab=83d33ee5
-/
theorem dyadicCorner_unique {k : ℤ} {x : Vec3} {a b : DyadicCorner}
    (ha : x ∈ dyadicCube k a) (hb : x ∈ dyadicCube k b) : a = b := by
  funext i
  have hscale : 0 < dyadicScale k := dyadicScale_pos k
  have ha' := (mem_dyadicCube.mp ha) i
  have hb' := (mem_dyadicCube.mp hb) i
  apply le_antisymm
  · apply (Int.cast_le (R := ℝ)).1
    apply le_of_not_gt
    intro hlt
    have hltInt : b i < a i := Int.cast_lt.mp hlt
    have hlt' : (b i : ℝ) + 1 ≤ a i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hltInt)
    nlinarith only [ha'.1, hb'.2, hscale, hlt']
  · apply (Int.cast_le (R := ℝ)).1
    apply le_of_not_gt
    intro hlt
    have hltInt : a i < b i := Int.cast_lt.mp hlt
    have hlt' : (a i : ℝ) + 1 ≤ b i := by
      exact_mod_cast (Int.add_one_le_iff.mpr hltInt)
    nlinarith only [ha'.2, hb'.1, hscale, hlt']

/--
@isnad1 id=existsun.0h2v.s4.30356ca79bcc from=translated src=- shape=1c311e29 vocab=cad808d1
-/
theorem dyadicCube_unique_at_scale {k : ℤ} {x : Vec3} :
    ∃! a : DyadicCorner, x ∈ dyadicCube k a := by
  refine ⟨dyadicCorner k x, mem_dyadicCube_of_corner k x, ?_⟩
  intro a ha
  exact dyadicCorner_unique ha (mem_dyadicCube_of_corner k x)

/--
@isnad1 id=le.1h3v.s5.859099c96814 from=translated src=- shape=c725a01b vocab=f3eadd6d
-/
theorem dyadicCube_subset_closedBall {k : ℤ} {a : DyadicCorner}
    {x : Vec3} (hx : x ∈ dyadicCube k a) :
    dyadicCube k a ⊆ Metric.closedBall x (dyadicScale k) := by
  intro y hy
  rw [Metric.mem_closedBall]
  rw [dist_eq_norm]
  have hscale : 0 < dyadicScale k := dyadicScale_pos k
  apply (pi_norm_le_iff_of_nonneg hscale.le).2
  intro i
  have hx' := (mem_dyadicCube.mp hx) i
  have hy' := (mem_dyadicCube.mp hy) i
  change |y i - x i| ≤ dyadicScale k
  rw [abs_le]
  constructor <;> nlinarith only [hx'.1, hx'.2, hy'.1, hy'.2, hscale]

/--
@isnad1 id=le.0h2v.s6.d15f64885223 from=translated src=- shape=93e40ab9 vocab=65ed4a2e
-/
theorem supBall_subset_dyadicCubeCenter (k : ℤ) (a : DyadicCorner) :
    Metric.ball (dyadicCubeCenter k a) (dyadicScale k / 2) ⊆
      dyadicCube k a := by
  intro x hx
  rw [Metric.mem_ball] at hx
  rw [dist_eq_norm] at hx
  rw [mem_dyadicCube]
  intro i
  have hs : 0 < dyadicScale k := dyadicScale_pos k
  have hcoord := norm_le_pi_norm (x - dyadicCubeCenter k a) i
  have hxi : |x i - dyadicCubeCenter k a i| < dyadicScale k / 2 := by
    have hcoord' := lt_of_le_of_lt hcoord hx
    change ‖x i - dyadicCubeCenter k a i‖ < dyadicScale k / 2 at hcoord'
    simpa only [Real.norm_eq_abs] using hcoord'
  dsimp [dyadicCubeCenter] at hxi ⊢
  rw [abs_lt] at hxi
  constructor <;> nlinarith only [hxi.1, hxi.2, hs]

/--
@isnad1 id=ex.1h2v.s5.26b6488b8442 from=translated src=- shape=4a07fb54 vocab=40c9f59b
-/
theorem dyadicScale_ratio {k l : ℤ} (hkl : k ≤ l) :
    ∃ m : ℤ, 0 < m ∧ dyadicScale k = (m : ℝ) * dyadicScale l := by
  let n : ℕ := Int.toNat (l - k)
  have hnonneg : 0 ≤ l - k := sub_nonneg.mpr hkl
  have hn : (l - k : ℤ) = n := by
    dsimp [n]
    exact (Int.toNat_of_nonneg hnonneg).symm
  refine ⟨(2 : ℤ) ^ n, by positivity, ?_⟩
  calc
    dyadicScale k = (2 : ℝ) ^ (-k : ℤ) := rfl
    _ = (2 : ℝ) ^ ((-l : ℤ) + (l - k)) := by congr 1; ring
    _ = (2 : ℝ) ^ (-l : ℤ) * (2 : ℝ) ^ (l - k) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ (-l : ℤ) * (2 : ℝ) ^ n := by
      rw [hn, zpow_natCast]
    _ = (((2 : ℤ) ^ n : ℤ) : ℝ) * dyadicScale l := by
      have hcast : (((2 : ℤ) ^ n : ℤ) : ℝ) = (2 : ℝ) ^ n := by
        norm_cast
      rw [hcast]
      dsimp [dyadicScale]
      ring

/--
@isnad1 id=le.0h1v.s5.6b7d0a7aab22 from=translated src=- shape=c4e8a472 vocab=680a008e
-/
theorem dyadicCube_subset_parent (Q : DyadicIndex) :
    dyadicCube Q.scale Q.corner ⊆
      dyadicCube (Q.scale - 1) (fun i => Q.corner i / 2) := by
  intro x hx
  rw [mem_dyadicCube]
  intro i
  have hs : dyadicScale (Q.scale - 1) = 2 * dyadicScale Q.scale := by
    dsimp [dyadicScale]
    rw [show - (Q.scale - 1) = -Q.scale + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hx' := (mem_dyadicCube.mp hx) i
  have hleft : 2 * (Q.corner i / 2) ≤ Q.corner i := by omega
  have hright : Q.corner i + 1 ≤ 2 * (Q.corner i / 2 + 1) := by omega
  have hleft' : (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) ≤ (Q.corner i : ℝ) := by
    exact_mod_cast hleft
  have hright'' : ((Q.corner i + 1 : ℤ) : ℝ) ≤
      ((2 * (Q.corner i / 2 + 1) : ℤ) : ℝ) := by
    exact_mod_cast hright
  norm_num at hright''
  have hright' : (Q.corner i : ℝ) + 1 ≤
      (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2 := by
    calc
      (Q.corner i : ℝ) + 1 ≤
          (2 : ℝ) * (((Q.corner i / 2 : ℤ) : ℝ) + 1) := hright''
      _ = (2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2 := by ring
  constructor
  · calc
      ((Q.corner i / 2 : ℤ) : ℝ) * dyadicScale (Q.scale - 1) =
          ((2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ)) * dyadicScale Q.scale := by
            rw [hs]
            ring
      _ ≤ (Q.corner i : ℝ) * dyadicScale Q.scale :=
        mul_le_mul_of_nonneg_right hleft' (dyadicScale_pos Q.scale).le
      _ ≤ x i := hx'.1
  · calc
      x i < ((Q.corner i : ℝ) + 1) * dyadicScale Q.scale := hx'.2
      _ ≤ ((2 : ℝ) * ((Q.corner i / 2 : ℤ) : ℝ) + 2) * dyadicScale Q.scale := by
        exact mul_le_mul_of_nonneg_right hright' (dyadicScale_pos Q.scale).le
      _ = (((Q.corner i / 2 : ℤ) : ℝ) + 1) * dyadicScale (Q.scale - 1) := by
        rw [hs]
        ring

/--
@isnad1 id=le.2h4v.s5.a0c2e1b9ab55 from=translated src=- shape=063e9665 vocab=93de0dac
-/
theorem dyadicCube_subset_of_intersect {k l : ℤ} (hkl : k ≤ l)
    {a b : DyadicCorner}
    (hint : (dyadicCube k a ∩ dyadicCube l b).Nonempty) :
    dyadicCube l b ⊆ dyadicCube k a := by
  obtain ⟨x, hxa, hxb⟩ := hint
  obtain ⟨m, hm, hscale⟩ := dyadicScale_ratio hkl
  intro y hy
  rw [mem_dyadicCube]
  intro i
  have hxa' := (mem_dyadicCube.mp hxa) i
  have hxb' := (mem_dyadicCube.mp hxb) i
  have hy' := (mem_dyadicCube.mp hy) i
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hleft : (a i : ℤ) * m ≤ b i := by
    apply Int.lt_add_one_iff.mp
    have hprod : ((a i : ℝ) * (m : ℝ)) * dyadicScale l <
        ((b i : ℝ) + 1) * dyadicScale l := by
      calc
        ((a i : ℝ) * (m : ℝ)) * dyadicScale l =
            (a i : ℝ) * dyadicScale k := by rw [hscale]; ring
        _ ≤ x i := hxa'.1
        _ < ((b i : ℝ) + 1) * dyadicScale l := hxb'.2
    have hreal : (a i : ℝ) * (m : ℝ) < (b i : ℝ) + 1 := by
      exact lt_of_mul_lt_mul_right hprod (dyadicScale_pos l).le
    exact_mod_cast hreal
  have hright : b i + 1 ≤ (a i + 1) * m := by
    apply Int.add_one_le_iff.mpr
    have hprod : (b i : ℝ) * dyadicScale l <
        (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l := by
      calc
        (b i : ℝ) * dyadicScale l ≤ x i := hxb'.1
        _ < ((a i : ℝ) + 1) * dyadicScale k := hxa'.2
        _ = (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l := by
          rw [hscale]
          ring
    have hreal : (b i : ℝ) < ((a i : ℝ) + 1) * (m : ℝ) := by
      exact lt_of_mul_lt_mul_right hprod (dyadicScale_pos l).le
    exact_mod_cast hreal
  constructor
  · have hleft' : (a i : ℝ) * (m : ℝ) ≤ b i := by exact_mod_cast hleft
    calc
      (a i : ℝ) * dyadicScale k =
          ((a i : ℝ) * (m : ℝ)) * dyadicScale l := by rw [hscale]; ring
      _ ≤ (b i : ℝ) * dyadicScale l :=
        mul_le_mul_of_nonneg_right hleft' (dyadicScale_pos l).le
      _ ≤ y i := hy'.1
  · have hright' : (b i : ℝ) + 1 ≤ ((a i : ℝ) + 1) * (m : ℝ) := by
      exact_mod_cast hright
    calc
      y i < ((b i : ℝ) + 1) * dyadicScale l := hy'.2
      _ ≤ (((a i : ℝ) + 1) * (m : ℝ)) * dyadicScale l :=
        mul_le_mul_of_nonneg_right hright' (dyadicScale_pos l).le
      _ = ((a i : ℝ) + 1) * dyadicScale k := by rw [hscale]; ring

/--
@isnad1 id=or.0h2v.s6.25cc9f6fa51f from=translated src=- shape=1bddb04e vocab=d2bd327e
-/
theorem dyadicCube_nested_or_disjoint (Q R : DyadicIndex) :
    dyadicCube Q.scale Q.corner ⊆ dyadicCube R.scale R.corner ∨
      dyadicCube R.scale R.corner ⊆ dyadicCube Q.scale Q.corner ∨
      Disjoint (dyadicCube Q.scale Q.corner) (dyadicCube R.scale R.corner) := by
  by_cases hQR : Q.scale ≤ R.scale
  · by_cases hint : (dyadicCube Q.scale Q.corner ∩
        dyadicCube R.scale R.corner).Nonempty
    · exact Or.inr (Or.inl (dyadicCube_subset_of_intersect hQR hint))
    · exact Or.inr (Or.inr (Set.disjoint_left.2 (by
        intro x hxQ hxR
        exact hint ⟨x, hxQ, hxR⟩)))
  · have hRQ : R.scale ≤ Q.scale := le_of_not_ge hQR
    by_cases hint : (dyadicCube Q.scale Q.corner ∩
        dyadicCube R.scale R.corner).Nonempty
    · have hint' : (dyadicCube R.scale R.corner ∩
          dyadicCube Q.scale Q.corner).Nonempty := by
        obtain ⟨x, hxQ, hxR⟩ := hint
        exact ⟨x, hxR, hxQ⟩
      exact Or.inl (dyadicCube_subset_of_intersect hRQ hint')
    · exact Or.inr (Or.inr (Set.disjoint_left.2 (by
        intro x hxQ hxR
        exact hint ⟨x, hxQ, hxR⟩)))

/--
@isnad1 id=eq.0h1v.s7.a956bb0ac0b6 from=translated src=- shape=97395df7 vocab=f003aaca
-/
theorem dyadicParent_volume_ratio (Q : DyadicIndex) :
    volume (dyadicCube (dyadicParent Q).scale (dyadicParent Q).corner) =
      8 * volume (dyadicCube Q.scale Q.corner) := by
  change volume (dyadicCube (Q.scale - 1) (fun i => Q.corner i / 2)) =
      8 * volume (dyadicCube Q.scale Q.corner)
  rw [volume_dyadicCube, volume_dyadicCube]
  have hs : dyadicScale (Q.scale - 1) = 2 * dyadicScale Q.scale := by
    dsimp [dyadicScale]
    rw [show - (Q.scale - 1) = -Q.scale + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  rw [hs, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [mul_pow]
  norm_num

end CKN.Foundation.Euclidean
