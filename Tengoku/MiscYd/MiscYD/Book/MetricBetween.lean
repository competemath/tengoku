module

public import Tengoku

/-!
### TODO

Axiomatic betweenness
-/

@[expose] public section

variable {V : Type*} [MetricSpace V] {u v w : V}

@[implicit_reducible]
def MetricSBtw : SBtw V where
  sbtw u v w := u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ dist u v + dist v w = dist u w

scoped[MetricBetweenness] attribute [instance] MetricSBtw

open MetricBetweenness

/--
@isnad1 id=iff.0h4v.s6.42d6b3a512de from=translated src=- shape=498c882b vocab=ff725788
-/
lemma MetricSpace.sbtw_iff :
  sbtw u v w ↔ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ dist u v + dist v w = dist u w := Iff.rfl

/--
@isnad1 id=ne.1h4v.s4.a2558a5152b3 from=translated src=- shape=0ebb643f vocab=d12b8ea5
-/
lemma SBtw.sbtw.ne12 (h : sbtw u v w) : u ≠ v := h.1
/--
@isnad1 id=ne.1h4v.s4.52465bd1c8ad from=translated src=- shape=10433387 vocab=d12b8ea5
-/
lemma SBtw.sbtw.ne13 (h : sbtw u v w) : u ≠ w := h.2.1
/--
@isnad1 id=ne.1h4v.s4.df8f97e68479 from=translated src=- shape=f5cb9c4e vocab=d12b8ea5
-/
lemma SBtw.sbtw.ne23 (h : sbtw u v w) : v ≠ w := h.2.2.1
/--
@isnad1 id=eq.1h4v.s5.cbd97b152b21 from=translated src=- shape=61145a51 vocab=ff725788
-/
lemma SBtw.sbtw.dist (h : sbtw u v w) : dist u v + dist v w = dist u w := h.2.2.2

/--
@isnad1 id=sbtw.1h4v.s4.03009d85e13d from=translated src=- shape=dc490b2b vocab=d12b8ea5
-/
lemma SBtw.sbtw.symm : sbtw u v w → sbtw w v u
| ⟨huv, huw, hvw, d⟩ => ⟨hvw.symm, huw.symm, huv.symm, by simpa [dist_comm, add_comm] using d⟩
/--
@isnad1 id=iff.0h4v.s4.60cdbd60c34e from=translated src=- shape=354ec248 vocab=d12b8ea5
-/
lemma SBtw.comm : sbtw u v w ↔ sbtw w v u :=
⟨.symm, .symm⟩

/--
@isnad1 id=iff.3h4v.s6.2ce23fae8111 from=translated src=- shape=346f0ddd vocab=ff725788
-/
lemma sbtw_iff_of_ne (h12 : u ≠ v) (h13 : u ≠ w) (h23 : v ≠ w) :
    sbtw u v w ↔ dist u v + dist v w = dist u w :=
  by simp [MetricSpace.sbtw_iff, h12, h13, h23]

/--
@isnad1 id=sbtw.3h4v.s6.fc78bdd81e92 from=translated src=- shape=3950ad51 vocab=1c68fc1e
-/
lemma sbtw_mk (h12 : u ≠ v) (h23 : v ≠ w) (h : dist u v + dist v w ≤ dist u w) : sbtw u v w := by
  refine ⟨h12, ?_, h23, h.antisymm (dist_triangle _ _ _)⟩
  rintro rfl
  rw [dist_self] at h
  replace h : dist v u ≤ 0 := by linarith [dist_comm v u]
  simp only [dist_le_zero] at h
  exact h23 h

/--
@isnad1 id=sbtw.2h5v.s5.9f1b6848c0e4 from=translated src=- shape=24f31b16 vocab=d12b8ea5
-/
lemma SBtw.sbtw.right_cancel {u v w x : V} (h : sbtw u v x) (h' : sbtw v w x) : sbtw u v w :=
  sbtw_mk h.ne12 h'.ne12 (by linarith [h.dist, h'.dist, dist_triangle u w x, dist_triangle u v w])

/--
@isnad1 id=false.2h4v.s4.e7388ae84e5b from=translated src=- shape=e583e545 vocab=d12b8ea5
-/
lemma SBtw.sbtw.asymm_right {u v x : V} (h : sbtw u v x) (h' : sbtw v u x) : False := by
  have := h'.dist
  rw [dist_comm] at this
  have : Dist.dist u v = 0 := by linarith [h.dist]
  simp [h.ne12] at this

/--
@isnad1 id=sbtw.2h5v.s5.c2f899a052f2 from=translated src=- shape=df9d8fc3 vocab=d12b8ea5
-/
lemma SBtw.sbtw.trans_right' {u v w x : V} (h : sbtw u v x) (h' : sbtw v w x) : sbtw u w x :=
  have : u ≠ w := by rintro rfl; exact h.asymm_right h'
  sbtw_mk this h'.ne23 <| by linarith [h.dist, h'.dist, dist_triangle u v w]
