import Tengoku.TdaLib.TDA.Filtration.Cech
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Čech complex and Rips/Čech sandwich fixtures

The fixtures test the `Cech.complex` and `Cech.filter` definitions: a closed boundary
on the line with a sharp lower value bound, an acute planar triangle on which both sandwich
inclusions are strict, the failure of attainment in the punctured line, repeated labels, and
empty negative-radius stages.
-/

universe u v

namespace TDA.Filtration.Cech.Examples

open TDA.Simplicial

/-! ### Two points on the line -/

namespace TwoPoints

/-- The labelled points `0` and `2` on the real line.-/
def pts : Fin 2 → ℝ := ![0, 2]

/--
@isnad1 id=injectiv.0h0v.s3.d9a9e15f3c92 from=translated src=- shape=bfe16b09 vocab=29f604c2
-/
theorem pts_injective : Function.Injective pts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h

/-- The label metric induced by the two points.-/
noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

/--
@isnad1 id=eq.0h2v.s5.168a360a8945 from=translated src=- shape=0e1f8095 vocab=a55839db
-/
theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The edge joining the two labels.-/
def edge : Finset (Fin 2) := {0, 1}

/--
@isnad1 id=nonempty.0h0v.s3.c0ac1db5701c from=translated src=- shape=06f63001 vocab=0cc59abe
-/
theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

/-- The edge as a face of the full complex.-/
def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

/--
@isnad1 id=eq.0h0v.s5.a29ebdf1168c from=translated src=- shape=bc65f690 vocab=e6821644
-/
theorem dist_pts : dist (pts 0) (pts 1) = 2 := by
  norm_num [pts, Real.dist_eq]

/-- The closed boundary: the midpoint witnesses the edge at radius exactly one.
@isnad1 id=mem.0h0v.s5.c19216d644a4 from=translated src=- shape=579ed0cf vocab=2925d521
-/
theorem edge_mem_complex_one : edge ∈ complex pts 1 := by
  refine (mem_complex_iff _ _ _).2 ⟨edge_nonempty, 1, ?_⟩
  intro v hv
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> norm_num [pts, Real.dist_eq]

/--
@isnad1 id=not.1h1v.s5.bb2862699843 from=translated src=- shape=991d3a41 vocab=89f894d1
-/
theorem edge_not_mem_complex {r : ℝ} (hr : r < 1) : edge ∉ complex pts r := by
  intro h
  have h2 := dist_le_two_mul_of_mem_complex pts h (v := 0) (w := 1)
    (by simp [edge]) (by simp [edge])
  rw [dist_pts] at h2
  linarith

/--
@isnad1 id=not.0h0v.s6.39991f5c13eb from=translated src=- shape=5014814b vocab=b8aaa159
-/
theorem edge_not_mem_rips_one : edge ∉ (Rips.filter metric).sublevel 1 := by
  intro h
  have h1 := ((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge]) 1 (by simp [edge])
  rw [metric_dist, dist_pts] at h1
  norm_num at h1

/--
@isnad1 id=mem.0h0v.s6.d2ee6c577637 from=translated src=- shape=ce5e6f3b vocab=b8aaa159
-/
theorem edge_mem_rips_two : edge ∈ (Rips.filter metric).sublevel 2 := by
  refine (Rips.mem_sublevel_iff _ _ _).2 ⟨edge_nonempty, ?_⟩
  intro v hv w hw
  rw [metric_dist]
  simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num [pts, Real.dist_eq]

/--
@isnad1 id=eq.0h0v.s5.8dccea2519f0 from=translated src=- shape=db85f507 vocab=40d7a982
-/
theorem rips_value : (Rips.filter metric).value edgeFace = 2 := by
  rw [Rips.filter_value]
  change Rips.diameter metric {0, 1} = 2
  rw [Rips.diameter_pair, metric_dist, dist_pts]

/--
@isnad1 id=eq.0h0v.s5.8267e0498e66 from=translated src=- shape=5d4dcd9b vocab=35cf718e
-/
theorem cech_value : (filter pts).value edgeFace = 1 := by
  apply le_antisymm
  · exact (FilterFunction.mem_sublevel_iff_of_mem _ _ _).1
      (complex_le_sublevel pts 1 edge_mem_complex_one)
  · have h := rips_le_two_mul_filter_value metric pts metric_dist edgeFace
    rw [rips_value] at h
    linarith

/-- The lower value bound `rips ≤ 2 * čech` is attained.
@isnad1 id=eq.0h0v.s6.1917dd460f42 from=translated src=- shape=507296ae vocab=095851a4
-/
theorem rips_value_eq_two_mul_cech_value :
    (Rips.filter metric).value edgeFace = 2 * (filter pts).value edgeFace := by
  rw [rips_value, cech_value]
  norm_num

end TwoPoints

/-! ### An acute triangle in the Euclidean plane -/

namespace Triangle

/-- The vertices `(0,0)`, `(2,0)` and `(1,2)` of an acute triangle with circumradius `5/4`.-/
noncomputable def pts : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[2, 0], !₂[1, 2]]

/--
@isnad1 id=eq.0h0v.s6.06d4aaa8b6f4 from=translated src=- shape=1d93898e vocab=5a5d85e8
-/
@[simp] theorem pts_zero : pts 0 = !₂[0, 0] := rfl
/--
@isnad1 id=eq.0h0v.s6.747ff84b4aed from=translated src=- shape=1d93898e vocab=5a5d85e8
-/
@[simp] theorem pts_one : pts 1 = !₂[2, 0] := rfl
/--
@isnad1 id=eq.0h0v.s6.d2f44915dd09 from=translated src=- shape=1d93898e vocab=5a5d85e8
-/
@[simp] theorem pts_two : pts 2 = !₂[1, 2] := rfl

/--
@isnad1 id=eq.0h2v.s9.2e84b9e65d02 from=translated src=- shape=8102d56d vocab=1b3b13e7
-/
theorem dist_sq (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/--
@isnad1 id=le.2h3v.s9.dba0c75dc7f1 from=translated src=- shape=ad8f7002 vocab=342d2659
-/
theorem dist_le_of_sq_le {x y : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (hc : 0 ≤ c)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≤ c ^ 2) : dist x y ≤ c := by
  rw [← dist_sq] at h
  exact (pow_le_pow_iff_left₀ dist_nonneg hc two_ne_zero).1 h

/--
@isnad1 id=le.1h3v.s9.0a268acf5d42 from=translated src=- shape=4b440479 vocab=342d2659
-/
theorem sq_le_of_dist_le {x y : EuclideanSpace ℝ (Fin 2)} {c : ℝ} (h : dist x y ≤ c) :
    (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 ≤ c ^ 2 := by
  rw [← dist_sq]
  exact pow_le_pow_left₀ dist_nonneg h 2

/--
@isnad1 id=injectiv.0h0v.s4.d0ac37e02693 from=translated src=- shape=dffe0065 vocab=9f4e1c3c
-/
theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 : pts i 0 = pts j 0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  have hx : ∀ k : Fin 3, pts k 0 = ![0, 2, 1] k := by
    intro k
    fin_cases k <;> rfl
  rw [hx, hx] at h0
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at h0

/-- The label metric induced by the three vertices.-/
noncomputable abbrev metric : MetricSpace (Fin 3) :=
  MetricSpace.induced pts pts_injective inferInstance

/--
@isnad1 id=eq.0h2v.s6.8a6ea8c13327 from=translated src=- shape=7618669a vocab=24c7beec
-/
theorem metric_dist (v w : Fin 3) : metric.dist v w = dist (pts v) (pts w) := rfl

/-- The three edges and the triangle.-/
def edge01 : Finset (Fin 3) := {0, 1}
def edge02 : Finset (Fin 3) := {0, 2}
def edge12 : Finset (Fin 3) := {1, 2}
def tri : Finset (Fin 3) := {0, 1, 2}

/--
@isnad1 id=mem.0h0v.s6.4b231ad3d46e from=translated src=- shape=ab49dff3 vocab=fe997943
-/
theorem edge01_mem_complex : edge01 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨0, by simp [edge01]⟩, !₂[1, 0], ?_⟩
  intro v hv
  simp only [edge01, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

/--
@isnad1 id=mem.0h0v.s6.10a2b44204b2 from=translated src=- shape=ab49dff3 vocab=550b0ad7
-/
theorem edge02_mem_complex : edge02 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨0, by simp [edge02]⟩, !₂[1 / 2, 1], ?_⟩
  intro v hv
  simp only [edge02, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

/--
@isnad1 id=mem.0h0v.s6.55662b857a50 from=translated src=- shape=ab49dff3 vocab=0aaf5672
-/
theorem edge12_mem_complex : edge12 ∈ complex pts (6 / 5) := by
  refine (mem_complex_iff _ _ _).2 ⟨⟨1, by simp [edge12]⟩, !₂[3 / 2, 1], ?_⟩
  intro v hv
  simp only [edge12, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

/-- No point is within `6/5` of all three vertices: a weighted sum of squared distances
equals `|x - (1, 3/4)|² + 25/16`, and `25/16 > 36/25`.
@isnad1 id=not.0h0v.s6.3f929a4b081f from=translated src=- shape=c1f30b2c vocab=ac174b2f
-/
theorem tri_not_mem_complex : tri ∉ complex pts (6 / 5) := by
  intro h
  obtain ⟨-, x, hx⟩ := (mem_complex_iff _ _ _).1 h
  have ha := sq_le_of_dist_le (hx 0 (by simp [tri]))
  have hb := sq_le_of_dist_le (hx 1 (by simp [tri]))
  have hc := sq_le_of_dist_le (hx 2 (by simp [tri]))
  norm_num [pts_zero, pts_one, pts_two] at ha hb hc
  nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 1 - 3 / 4)]

/--
@isnad1 id=mem.0h0v.s6.56e9975b0ae7 from=translated src=- shape=50cf70bf vocab=7bb3c6d0
-/
theorem tri_mem_rips : tri ∈ (Rips.filter metric).sublevel (12 / 5) := by
  refine (Rips.mem_sublevel_iff _ _ _).2 ⟨⟨0, by simp [tri]⟩, ?_⟩
  intro v hv w hw
  rw [metric_dist]
  simp only [tri, Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    exact dist_le_of_sq_le (by norm_num) (by norm_num [pts_zero, pts_one, pts_two])

private theorem not_le_of_sq {v w : Fin 3} (h : (6 / 5 : ℝ) ^ 2 <
    (pts v 0 - pts w 0) ^ 2 + (pts v 1 - pts w 1) ^ 2) : ¬ metric.dist v w ≤ 6 / 5 :=
  fun hle => absurd (sq_le_of_dist_le (metric_dist v w ▸ hle)) (not_le.2 h)

/--
@isnad1 id=not.0h0v.s6.68931b43cf89 from=translated src=- shape=5273dbe4 vocab=33fd9358
-/
theorem edge01_not_mem_rips : edge01 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge01]) 1 (by simp [edge01]))

/--
@isnad1 id=not.0h0v.s6.c877b1c03f03 from=translated src=- shape=5273dbe4 vocab=92ff1d83
-/
theorem edge02_not_mem_rips : edge02 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 0 (by simp [edge02]) 2 (by simp [edge02]))

/--
@isnad1 id=not.0h0v.s6.33089c9295bd from=translated src=- shape=5273dbe4 vocab=be5352b1
-/
theorem edge12_not_mem_rips : edge12 ∉ (Rips.filter metric).sublevel (6 / 5) := fun h =>
  not_le_of_sq (by norm_num [pts_zero, pts_one, pts_two])
    (((Rips.mem_sublevel_iff _ _ _).1 h).2 1 (by simp [edge12]) 2 (by simp [edge12]))

/-- The first sandwich inclusion is strict on this family.
@isnad1 id=lt.0h0v.s7.d2909e8fd2ae from=translated src=- shape=1f1ebc8b vocab=634288d8
-/
theorem rips_lt_complex : (Rips.filter metric).sublevel (6 / 5) < complex pts (6 / 5) :=
  lt_of_le_not_ge (ripsSublevel_le_complex metric pts metric_dist _)
    fun h => edge01_not_mem_rips (h edge01_mem_complex)

/-- The second sandwich inclusion is strict on this family.
@isnad1 id=lt.0h0v.s7.680bd7b94634 from=translated src=- shape=a9cf212b vocab=808ca13b
-/
theorem complex_lt_rips : complex pts (6 / 5) < (Rips.filter metric).sublevel (2 * (6 / 5)) :=
  lt_of_le_not_ge (complex_le_ripsSublevel_two_mul metric pts metric_dist _)
    fun h => tri_not_mem_complex (h (by norm_num; exact tri_mem_rips))

end Triangle

/-! ### Attainment fails in the punctured line -/

namespace Punctured

/-- The labelled points `-1` and `1` in the punctured line, which is not proper.-/
def pts : Fin 2 → {x : ℝ // x ≠ 0} := ![⟨-1, by norm_num⟩, ⟨1, by norm_num⟩]

/--
@isnad1 id=injectiv.0h0v.s4.216a506b42fa from=translated src=- shape=1bd3ead5 vocab=701a98e5
-/
theorem pts_injective : Function.Injective pts := by
  intro i j h
  have h0 := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [pts] at h0

noncomputable abbrev metric : MetricSpace (Fin 2) :=
  MetricSpace.induced pts pts_injective inferInstance

/--
@isnad1 id=eq.0h2v.s6.85791d4512e4 from=translated src=- shape=7e77e71e vocab=e526a227
-/
theorem metric_dist (v w : Fin 2) : metric.dist v w = dist (pts v) (pts w) := rfl

def edge : Finset (Fin 2) := {0, 1}

/--
@isnad1 id=nonempty.0h0v.s3.f1d6b18a98f7 from=translated src=- shape=06f63001 vocab=f62b7aac
-/
theorem edge_nonempty : edge.Nonempty := ⟨0, by simp [edge]⟩

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, edge_nonempty⟩

/-- The only common point of the two closed unit balls in `ℝ` is the missing origin.
@isnad1 id=not.0h0v.s6.e160b79588dc from=translated src=- shape=32126f41 vocab=22008d88
-/
theorem edge_not_mem_complex_one : edge ∉ complex pts 1 := by
  intro h
  obtain ⟨-, x, hx⟩ := (mem_complex_iff _ _ _).1 h
  have h0 := hx 0 (by simp [edge])
  have h1 := hx 1 (by simp [edge])
  simp only [Subtype.dist_eq, Real.dist_eq, pts] at h0 h1
  norm_num at h0 h1
  obtain ⟨h0l, h0r⟩ := abs_le.1 h0
  obtain ⟨h1l, h1r⟩ := abs_le.1 h1
  exact x.2 (by linarith)

/--
@isnad1 id=eq.0h0v.s5.ba92e55831b0 from=translated src=- shape=14c22147 vocab=e36be6c3
-/
theorem cech_value : (filter pts).value edgeFace = 1 := by
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    set ε := (filter pts).value edgeFace - 1 with hε
    have hpos : (0 : ℝ) < ε / 2 := by linarith
    have hup := filter_value_le_radiusAt pts edgeFace ⟨ε / 2, hpos.ne'⟩
    have hrad : radiusAt pts ⟨ε / 2, hpos.ne'⟩ edge ≤ 1 + ε / 2 := by
      refine (radiusAt_le_iff _ _ _ _).2 ⟨by linarith, fun v hv => ?_⟩
      simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;>
        · simp only [Subtype.dist_eq, Real.dist_eq, pts]
          norm_num
          rw [abs_le]
          constructor <;> linarith
    have : (filter pts).value edgeFace ≤ 1 + ε / 2 := hup.trans hrad
    linarith
  · have h := rips_le_two_mul_filter_value metric pts metric_dist edgeFace
    have hr : (Rips.filter metric).value edgeFace = 2 := by
      rw [Rips.filter_value]
      change Rips.diameter metric {0, 1} = 2
      rw [Rips.diameter_pair, metric_dist]
      norm_num [pts, Subtype.dist_eq, Real.dist_eq]
    rw [hr] at h
    linarith

/--
@isnad1 id=mem.0h0v.s6.2eae431c976c from=translated src=- shape=72dcb83d vocab=e050944f
-/
theorem edge_mem_sublevel_one : edge ∈ (filter pts).sublevel 1 :=
  (FilterFunction.mem_sublevel_iff_of_mem _ _ edgeFace).2 cech_value.le

/-- Without `ProperSpace`, the sublevel can be strictly larger than the Čech complex.
@isnad1 id=ne.0h0v.s6.666bca0f4b01 from=translated src=- shape=462cd435 vocab=343f807e
-/
theorem sublevel_ne_complex : (filter pts).sublevel 1 ≠ complex pts 1 := fun h =>
  edge_not_mem_complex_one (h ▸ edge_mem_sublevel_one)

end Punctured

/-! ### Repeated labels -/

namespace Repeated

/-- Two distinct labels at the same point.-/
def pts : Fin 2 → ℝ := fun _ => 0

def edge : Finset (Fin 2) := {0, 1}

/--
@isnad1 id=eq.0h0v.s3.b88ecc8eae04 from=translated src=- shape=415057c6 vocab=f248c80a
-/
theorem edge_card : edge.card = 2 := rfl

def edgeFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨edge, ⟨0, by simp [edge]⟩⟩

/--
@isnad1 id=mem.0h0v.s5.ce019f72b33b from=translated src=- shape=579ed0cf vocab=c33ed57b
-/
theorem edge_mem_complex_zero : edge ∈ complex pts 0 :=
  mem_complex_of_pairwise pts ⟨0, by simp [edge]⟩ fun _ _ _ _ => by simp [pts]

/--
@isnad1 id=eq.0h0v.s5.dbacbff5ef63 from=translated src=- shape=5d4dcd9b vocab=9ae16703
-/
theorem cech_value : (filter pts).value edgeFace = 0 :=
  le_antisymm ((FilterFunction.mem_sublevel_iff_of_mem _ _ _).1
    (complex_le_sublevel pts 0 edge_mem_complex_zero)) (filter_value_nonneg pts edgeFace)

end Repeated

/-! ### Negative radii -/

section Negative

variable {X : Type u} {V : Type v} [PseudoMetricSpace X]

/--
@isnad1 id=eq.0h3v.s5.98eccb3dfc44 from=translated src=- shape=e4f166f7 vocab=e874fe0a
-/
theorem complex_neg_one_eq_bot (p : V → X) : complex p (-1) = ⊥ :=
  complex_eq_bot_of_neg p (by norm_num)

/--
@isnad1 id=not.0h4v.s5.4b0bec01059e from=translated src=- shape=98a96677 vocab=866ede93
-/
theorem singleton_not_mem_complex_neg_one (p : V → X) (v : V) :
    ({v} : Finset V) ∉ complex p (-1) := fun h => by
  have := (singleton_mem_complex_iff p (-1) v).1 h
  norm_num at this

end Negative

end TDA.Filtration.Cech.Examples
