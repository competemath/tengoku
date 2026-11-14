import Tengoku.TdaLib.TDA.Persistence.SupportInterval
import Tengoku.TdaLib.TDA.Persistence.AlgebraicFamily
import Tengoku.Seed.Analysis.SpecificLimits.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real interval examples

Whole-line, left-tail and singleton supports exhibit the endpoint conventions.
A disjoint infinite interval family accumulates at zero and has at most one
active occurrence at each parameter.
-/

set_option autoImplicit false

namespace TDA.Persistence.RealIntervalExamples

open CategoryTheory
open Filter Topology

/-- The whole-line interval module retains every coefficient along every map.-/
noncomputable abbrev wholeLine : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.univ : Set ℝ) Set.ordConnected_univ

/--
@isnad1 id=eq.1h3v.s9.49f7bd02d13f from=translated src=- shape=80c133b0 vocab=b2befa74
-/
theorem wholeLine_map_preserves_coefficients {s t : ℝ} (h : s ≤ t)
    (x : SupportInterval.fiber (k := ℚ) (Set.univ : Set ℝ) s) :
    ((structureMapLinear wholeLine h x :
      SupportInterval.fiber (k := ℚ) (Set.univ : Set ℝ) t) : ℚ) = (x : ℚ) := by
  simpa [wholeLine] using
    (SupportInterval.structureMap_val (k := ℚ) (Set.univ : Set ℝ)
      Set.ordConnected_univ h x)

noncomputable abbrev leftClosedRay (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.Iic a) inferInstance

noncomputable abbrev leftOpenRay (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) (Set.Iio a) inferInstance

/-- Every point strictly below the endpoint still carries a nonzero open-tail fiber.
@isnad1 id=ex.1h2v.s8.36866f8fc09d from=translated src=- shape=68de2c92 vocab=e6487603
-/
theorem leftOpen_fiber_nonzero_below (a p : ℝ) (h : p < a) :
    ∃ x : SupportInterval.fiber (k := ℚ) (Set.Iio a) p, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) (Set.Iio a) (p := p)
    (Set.mem_Iio.mpr h), ?_⟩
  simp [SupportInterval.one]

/-- A closed left tail includes its finite endpoint and carries a nonzero fiber there.
@isnad1 id=ex.0h1v.s8.89f2e4943173 from=translated src=- shape=4c16ec43 vocab=f958cc49
-/
theorem leftClosed_endpoint_nonzero (a : ℝ) :
    ∃ x : SupportInterval.fiber (k := ℚ) (Set.Iic a) a, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) (Set.Iic a) (p := a)
    (Set.mem_Iic.mpr le_rfl), ?_⟩
  simp [SupportInterval.one]

/-- The closed tail's map to the endpoint preserves the unit coefficient.
@isnad1 id=eq.1h2v.s9.d70173f59038 from=translated src=- shape=d999ee37 vocab=3d4d6122
-/
theorem leftClosed_map_to_endpoint (a p : ℝ) (h : p ≤ a) :
    structureMapLinear (leftClosedRay a) h
      (SupportInterval.one (k := ℚ) (Set.Iic a) (p := p) (Set.mem_Iic.mpr h)) =
    SupportInterval.one (k := ℚ) (Set.Iic a) (p := a) (Set.mem_Iic.mpr le_rfl) := by
  apply Subtype.ext
  rw [SupportInterval.structureMap_val]
  simp [SupportInterval.one]

/-- The open tail omits its finite endpoint, even though it is nonempty arbitrarily near it.
@isnad1 id=subsingl.0h1v.s4.876dc8652da6 from=translated src=- shape=9700edba vocab=502fc89c
-/
theorem leftOpen_endpoint_is_zero (a : ℝ) :
    Subsingleton ((leftOpenRay a).obj a) := by
  change Subsingleton (SupportInterval.fiber (k := ℚ) (Set.Iio a) a)
  constructor
  intro x y
  apply Subtype.ext
  have hx := SupportInterval.val_eq_zero (k := ℚ) (Set.Iio a)
    (show a ∉ Set.Iio a by simp) x
  have hy := SupportInterval.val_eq_zero (k := ℚ) (Set.Iio a)
    (show a ∉ Set.Iio a by simp) y
  exact hx.trans hy.symm

/-- Its transition into the omitted endpoint is the zero map.
@isnad1 id=eq.1h2v.s9.b6a64560b0e7 from=translated src=- shape=3cec67c9 vocab=969dfab0
-/
theorem leftOpen_map_to_endpoint_is_zero (a p : ℝ) (h : p < a) :
    structureMapLinear (leftOpenRay a) (le_of_lt h) = 0 := by
  apply (SupportInterval.structureMap_eq_zero_iff (k := ℚ) (Set.Iio a)
    (inferInstance : (Set.Iio a).OrdConnected) (le_of_lt h)).2
  rintro ⟨_, ha⟩
  simp only [Set.mem_Iio] at ha
  exact (lt_irrefl a) ha

noncomputable abbrev singletonInterval (a : ℝ) : PModule ℚ ℝ :=
  SupportInterval.module (k := ℚ) ({a} : Set ℝ) inferInstance

/-- A singleton interval remains visible as a nonzero fiber.
@isnad1 id=ex.0h1v.s8.59fba6c85933 from=translated src=- shape=483e4fd2 vocab=0537b4ed
-/
theorem singleton_fiber_nonzero (a : ℝ) :
    ∃ x : SupportInterval.fiber (k := ℚ) ({a} : Set ℝ) a, (x : ℚ) = 1 := by
  refine ⟨SupportInterval.one (k := ℚ) ({a} : Set ℝ) (p := a) (by simp), ?_⟩
  simp [SupportInterval.one]

/-- Every strict map in a singleton-supported module vanishes.
@isnad1 id=eq.1h3v.s9.76562407c2eb from=translated src=- shape=a2cdddbc vocab=04edf6fc
-/
theorem singleton_strict_map_zero {s t a : ℝ} (h : s < t) :
    structureMapLinear (singletonInterval a) (le_of_lt h) = 0 := by
  apply (SupportInterval.structureMap_eq_zero_iff (k := ℚ) ({a} : Set ℝ)
    (inferInstance : ({a} : Set ℝ).OrdConnected) (le_of_lt h)).2
  rintro ⟨hs, ht⟩
  simp only [Set.mem_singleton_iff] at hs ht
  subst s
  subst t
  exact (lt_irrefl a) h

/-- An empty indexing type gives an actually zero algebraic family at each parameter.-/
noncomputable def emptyFamily : Empty → PModule ℚ ℝ := fun e => Empty.elim e

/--
@isnad1 id=subsingl.0h1v.s5.dcbaad302e19 from=translated src=- shape=dd6df3da vocab=704e28ed
-/
theorem empty_family_fiber_is_subsingleton (t : ℝ) :
    Subsingleton ((AlgebraicFamily.familyModule emptyFamily).obj t) := by
  change Subsingleton (DirectSum Empty (fun e => (emptyFamily e).obj t))
  infer_instance

/-- Reciprocal endpoints decrease strictly to zero.-/
noncomputable def endpoint (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/--
@isnad1 id=lt.0h1v.s3.0ceadfcc407c from=translated src=- shape=b9369acb vocab=997f7c5e
-/
theorem endpoint_pos (n : ℕ) : 0 < endpoint n := by
  simpa [endpoint] using (Nat.one_div_pos_of_nat (α := ℝ) (n := n))

/--
@isnad1 id=lt.0h1v.s4.fe48bf715cdf from=translated src=- shape=490b3ecf vocab=9d3c5d90
-/
theorem endpoint_strict_antitone (n : ℕ) : endpoint (n + 1) < endpoint n := by
  simpa [endpoint] using
    (Nat.one_div_lt_one_div (α := ℝ) (Nat.lt_succ_self n))

/--
@isnad1 id=le.1h2v.s4.6e36b0244e69 from=translated src=- shape=3f8b8077 vocab=a08ccbcc
-/
theorem endpoint_antitone {m n : ℕ} (h : m ≤ n) : endpoint n ≤ endpoint m := by
  simpa [endpoint] using (Nat.one_div_le_one_div (α := ℝ) h)

/-- Pairwise disjoint positive intervals with endpoints converging to zero.-/
def accumulatingInterval (n : ℕ) : Set ℝ := Set.Ioc (endpoint (n + 1)) (endpoint n)

/--
@isnad1 id=nonempty.0h1v.s2.c975925fe60d from=translated src=- shape=1a6c1393 vocab=c5c5f2ec
-/
theorem accumulatingInterval_nonempty (n : ℕ) : (accumulatingInterval n).Nonempty := by
  refine ⟨endpoint n, ?_⟩
  exact ⟨endpoint_strict_antitone n, le_rfl⟩

/--
@isnad1 id=disjoint.1h2v.s5.c90eab83a732 from=translated src=- shape=d61bf0ea vocab=c8e33174
-/
theorem accumulatingInterval_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (accumulatingInterval i) (accumulatingInterval j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hj : endpoint j ≤ endpoint (i + 1) := endpoint_antitone (Nat.succ_le_of_lt hij)
  exact (not_lt_of_ge (hy.2.trans hj)) hx.1

/--
@isnad1 id=disjoint.1h2v.s5.a46219f55a12 from=translated src=- shape=d61bf0ea vocab=811ec376
-/
theorem accumulatingInterval_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (accumulatingInterval i) (accumulatingInterval j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact accumulatingInterval_disjoint_of_lt h
  · exact (accumulatingInterval_disjoint_of_lt h).symm

def activeIndices (x : ℝ) : Set ℕ := {n | x ∈ accumulatingInterval n}

/-- Each parameter belongs to at most one interval in the family.
@isnad1 id=subsingl.0h1v.s2.c5f7d5bfe3a4 from=translated src=- shape=1a6c1393 vocab=73897467
-/
theorem activeIndices_subsingleton (x : ℝ) : Set.Subsingleton (activeIndices x) := by
  intro i hi j hj
  by_contra hij
  exact (Set.disjoint_left.mp (accumulatingInterval_disjoint hij)) hi hj

/-- Thus the family satisfies pointwise finite activity.
@isnad1 id=finite.0h1v.s2.44c785242dd7 from=translated src=- shape=1a6c1393 vocab=f9bbc2d8
-/
theorem activeIndices_finite (x : ℝ) : (activeIndices x).Finite := by
  classical
  by_cases hne : (activeIndices x).Nonempty
  · rcases hne with ⟨n, hn⟩
    refine Set.Finite.subset (Set.finite_singleton n) ?_
    intro m hm
    have hmn : m = n := activeIndices_subsingleton x hm hn
    simp [hmn]
  · have hempty : activeIndices x = ∅ := by
      ext n
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hn => hne ⟨n, hn⟩
    simp [hempty]

/-- Every index is a nonempty occurrence, so infinitely many distinct intervals occur.
@isnad1 id=infinite.0h0v.s3.f8810c2e8a37 from=translated src=- shape=1d474fdd vocab=2a8492fa
-/
theorem infinitely_many_nonempty_occurrences :
    Set.Infinite {n : ℕ | (accumulatingInterval n).Nonempty} := by
  have hset : {n : ℕ | (accumulatingInterval n).Nonempty} = Set.univ := by
    ext n
    simp [accumulatingInterval_nonempty]
  rw [hset]
  exact Set.infinite_univ

/-- The chosen point from each occurrence converges to the accumulation parameter zero.
@isnad1 id=tendsto.0h0v.s4.14439de60a69 from=translated src=- shape=8e2810f0 vocab=80e7447a
-/
theorem occurrence_points_accumulate_at_zero :
    Tendsto endpoint atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/--
@isnad1 id=mem.0h1v.s3.43da72f1ff2b from=translated src=- shape=b5ca9b95 vocab=2d81b7a1
-/
theorem occurrence_point_lies_in_interval (n : ℕ) : endpoint n ∈ accumulatingInterval n :=
  ⟨endpoint_strict_antitone n, le_rfl⟩

end TDA.Persistence.RealIntervalExamples
