import Tengoku.NsP23.P23.OneTie.CoverShapes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: the H5 symbolic cover

This file follows the two unbounded coordinate regimes in the human H5 proof.
The first lemmas expose the exact structural facts used repeatedly in that
case split; no finite enumeration or computational certificate is imported.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

/-- A standard monomial is below a selected root.-/
theorem exists_root_above_of_mem_standardSet {S : Finset (Normal a b c)}
    {p : Normal a b c} (hp : p ∈ standardSet S) :
    ∃ R ∈ S, p ∣ R := by
  exact (mem_standardSet_iff S p).1 hp

/-- Distinct socle roots cannot lie above one another.-/
theorem root_eq_of_dvd {S : Finset (Normal a b c)}
    (hanti : IsRootAntichain S) {R Q : Normal a b c}
    (hR : R ∈ S) (hQ : Q ∈ S) (hRQ : R ∣ Q) : R = Q := by
  by_contra hne
  exact (hanti R hR Q hQ hne) hRQ

/-- Human case I.1: relative to an x-centre below the last layer, every
distinct root is either the exact ordinary upper root or has no wrapped
x-predecessor.-/
theorem root_shape_below_last {S : Finset (Normal a b c)}
    (hanti : IsRootAntichain S) {C R : Normal a b c}
    (hcentre : IsDirectionalCentre S .x C) (hR : R ∈ S)
    (hne : R ≠ C) (hbelow : C.x < a - 1) :
    (R.x = C.x + 1 ∧ R.y ≤ C.y ∧ R.z ≤ C.z) ∨
      (R.x = 0 ∧ ¬(b ≤ R.y ∧ c ≤ R.z)) := by
  by_cases hx : 0 < R.x
  · exact Or.inl (h4_x_edge_ordinary_exact hanti hcentre hR hne hx)
  · have hx0 : R.x = 0 := by omega
    refine Or.inr ⟨hx0, ?_⟩
    rintro ⟨hy, hz⟩
    have hw := h4_x_edge_wrapped_exact hanti hcentre hR hne hx0 hy hz
    have hClt := C.x_lt
    omega

/-- Human case II: relative to an x-centre in the last layer, every distinct
root has x-coordinate zero.-/
theorem root_x_zero_at_last {S : Finset (Normal a b c)}
    (hanti : IsRootAntichain S) {C R : Normal a b c}
    (hcentre : IsDirectionalCentre S .x C) (hR : R ∈ S)
    (hne : R ≠ C) (hlast : C.x = a - 1) : R.x = 0 := by
  by_contra hx0
  have hx : 0 < R.x := by omega
  have hordinary := h4_x_edge_ordinary_exact hanti hcentre hR hne hx
  have hRlt := R.x_lt
  omega

/-- In case I, liveness of the normalized tie forces the x-centre to be at
least `(b,c)` in the transverse coordinates (human equation I.2).-/
theorem below_last_live_bounds {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) {C : Normal a b c}
    (hcentre : IsDirectionalCentre S .x C)
    (hbelow : C.x < a - 1) : b ≤ C.y ∧ c ≤ C.z := by
  rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
    ⟨R, hRS, htR⟩
  have htcrit := (Normal.exact_divides_iff (liveTiePoint : Normal a b c) R).1 htR
  by_cases hRC : R = C
  · subst R
    simpa [liveTiePoint, Normal.DividesCriterion] using htcrit
  · rcases root_shape_below_last h.antichain hcentre hRS hRC hbelow with
      hupper | hlower
    · simp [liveTiePoint, Normal.DividesCriterion] at htcrit
      omega
    · simp [liveTiePoint, Normal.DividesCriterion] at htcrit
      exact False.elim (hlower.2 ⟨by omega, by omega⟩)

/-- The three selected centres cannot all coincide in the non-dominant case.-/
theorem directional_centres_not_all_equal {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) {X Y Z : Normal a b c}
    (hx : IsDirectionalCentre S .x X)
    (hy : IsDirectionalCentre S .y Y)
    (hz : IsDirectionalCentre S .z Z) :
    ¬(X = Y ∧ X = Z) := by
  rintro ⟨hXY, hXZ⟩
  subst Y
  subst Z
  have hall : ∀ e : Direction, IsDirectionalCentre S e X := by
    intro e
    cases e <;> assumption
  have hdom : IsDominantRoot S X :=
    (isDominantRoot_iff_all_directionalCentre S X h.a_ge_two h.antichain).2
      ⟨hx.1, hall⟩
  exact h.no_dominant X hx.1 hdom

/-! The next two predicates are merely readable names for the symbolic
coordinate leaves of the human case split.  They do not add hypotheses and
are not certificates: the classification lemmas below derive them from H4. -/

def MixedTwoCoordinateCase (C P : Normal a b c) : Prop :=
  -- M2
  (b = 1 ∧ c = 1 ∧ C.x ≤ a - 2 ∧ 1 ≤ C.y ∧ 1 ≤ C.z ∧
    P.x = C.x + 1 ∧ P.y = C.y - 1 ∧ P.z = C.z) ∨
  -- reflected M2
  (b = 1 ∧ c = 1 ∧ C.x ≤ a - 2 ∧ 1 ≤ C.y ∧ 1 ≤ C.z ∧
    P.x = C.x + 1 ∧ P.y = C.y ∧ P.z = C.z - 1) ∨
  -- M3
  (C.x = 0 ∧ C.y = b ∧ c ≤ C.z ∧
    P.x = 0 ∧ P.y = b - 1 ∧ P.z = C.z + 1) ∨
  -- reflected M3
  (C.x = 0 ∧ C.z = c ∧ b ≤ C.y ∧
    P.x = 0 ∧ P.y = C.y + 1 ∧ P.z = c - 1) ∨
  -- M4
  (b = 1 ∧ c = 1 ∧ C.x = a - 1 ∧ 1 ≤ C.y ∧
    P.x = 0 ∧ P.y = C.y ∧ P.z = C.z + 1) ∨
  -- reflected M4
  (b = 1 ∧ c = 1 ∧ C.x = a - 1 ∧ 1 ≤ C.z ∧
    P.x = 0 ∧ P.y = C.y + 1 ∧ P.z = C.z) ∨
  -- M5
  (C.x = a - 1 ∧ C.y = 0 ∧ 1 ≤ C.z ∧
    P.x = 0 ∧ P.y = b ∧ P.z = C.z + c - 1) ∨
  -- reflected M5
  (C.x = a - 1 ∧ C.z = 0 ∧ 1 ≤ C.y ∧
    P.x = 0 ∧ P.y = C.y + b - 1 ∧ P.z = c)

def PureTwoCoordinateCase (C P : Normal a b 0) : Prop :=
  -- P3
  (C.x = 0 ∧ C.y = b ∧
    P.x = 0 ∧ P.y = b - 1 ∧ P.z = C.z + 1) ∨
  -- P4
  (C.x = 0 ∧ C.y = b ∧ C.z = 0 ∧
    P.x = 0 ∧ P.y = b - 1 ∧ 1 ≤ P.z) ∨
  -- P5
  (C.x = a - 1 ∧ C.y = 0 ∧ 1 ≤ C.z ∧
    P.x = 0 ∧ P.y = b ∧ P.z = 0) ∨
  -- P6
  (C.x = a - 1 ∧ C.y = 0 ∧ 1 ≤ C.z ∧
    P.x = 0 ∧ P.y = b ∧ P.z = C.z - 1) ∨
  -- fibre-product orientation
  (C.x = 0 ∧ C.y = 0 ∧ 1 ≤ C.z ∧ P.z = 0) ∨
  (P.x = 0 ∧ P.y = 0 ∧ 1 ≤ P.z ∧ C.z = 0)

/-! Small Presburger leaves for the human two-root split.  Keeping these
separate prevents proof search from seeing the finite-set and centre records. -/

theorem mixed_below_upper_direct_arithmetic
    {u v U V b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hU : U ≤ u) (hV : V ≤ v)
    (ey : u = U + 1 ∧ v ≤ V)
    (ez : V + c = v + 1 ∧ U + b ≤ u) :
    b = 1 ∧ c = 1 ∧ U = u - 1 ∧ V = v := by
  omega

theorem mixed_below_lower_direct_arithmetic
    {r u v U V b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v)
    (hnw : ¬(b ≤ U ∧ c ≤ V))
    (ey : u + (if 0 < r then b else 0) = U + 1 ∧
      v + (if 0 < r then c else 0) ≤ V)
    (ez : V = v + 1 ∧ U ≤ u) :
    r = 0 ∧ u = b ∧ U = b - 1 ∧ V = v + 1 := by
  by_cases hr : 0 < r <;> simp [hr] at ey <;> omega

theorem mixed_last_direct_m4_arithmetic
    {u v U V b c : ℕ} (hb : 1 ≤ b) (hc : 1 ≤ c)
    (ey : u + b = U + 1 ∧ v + c ≤ V)
    (ez : V = v + 1 ∧ U ≤ u) :
    b = 1 ∧ c = 1 ∧ U = u ∧ V = v + 1 := by
  omega

/-- The direct below-last two-root branch (`Cy=P`, `Cz=C`) is M2 or M3.-/
theorem mixed_two_below_direct
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y P)
    (hzC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z C)
    (hbelow : C.x < a - 1) :
    (b = 1 ∧ c = 1 ∧ C.x ≤ a - 2 ∧ 1 ≤ C.y ∧ 1 ≤ C.z ∧
      P.x = C.x + 1 ∧ P.y = C.y - 1 ∧ P.z = C.z) ∨
    (C.x = 0 ∧ C.y = b ∧ c ≤ C.z ∧
      P.x = 0 ∧ P.y = b - 1 ∧ P.z = C.z + 1) := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hbounds := below_last_live_bounds h hxC hbelow
  have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
  have hxshape := root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow
  rcases hxshape with hu | hl
  · have hPz : 0 < P.z := by omega
    have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
    left
    have har := mixed_below_upper_direct_arithmetic hb hc hbounds.1 hbounds.2
      hu.2.1 hu.2.2 (by simpa [hu.1, show ¬C.x + 1 < C.x by omega] using hey)
      (by simpa [hu.1] using hez)
    omega
  · have hPz : 0 < P.z := by
      by_cases hr : 0 < C.x
      · simp [hl.1, hr] at hey
        omega
      · simp [hl.1, hr] at hey
        omega
    have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
    right
    have har := mixed_below_lower_direct_arithmetic hb hc hbounds.1 hbounds.2
      hl.2 (by simpa [hl.1] using hey) (by simpa [hl.1] using hez)
    omega

/-- The direct last-layer two-root branch (`Cy=P`, `Cz=C`) is M4.-/
theorem mixed_two_last_direct
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y P)
    (hzC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z C)
    (hlast : C.x = a - 1) :
    b = 1 ∧ c = 1 ∧ C.x = a - 1 ∧ 1 ≤ C.y ∧
      P.x = 0 ∧ P.y = C.y ∧ P.z = C.z + 1 := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
  have hPC : P.x < C.x := by
    have := h.a_ge_two
    omega
  have hnotCP : ¬C.x < P.x := by omega
  have hCy : 0 < C.y := by
    by_contra hy0
    have hy0' : C.y = 0 := by omega
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨R, hRS, htR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    have htie : Normal.DividesCriterion (liveTiePoint : Normal a b c) C ∨
        Normal.DividesCriterion (liveTiePoint : Normal a b c) P := by
      rcases hRC with hRC | hRP
      · subst R; exact Or.inl ((Normal.exact_divides_iff _ _).1 htR)
      · subst R; exact Or.inr ((Normal.exact_divides_iff _ _).1 htR)
    simp [liveTiePoint, Normal.DividesCriterion] at htie
    rcases htie with htC | htP
    · omega
    · have hPz : 0 < P.z := by omega
      have ez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
      simp [hnotCP, hy0'] at ez
      omega
  have ey := h4_y_edge_exact h.antichain hyP hCS hne hCy
  have hPz : 0 < P.z := by
    simp [hPC] at ey
    omega
  have ez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
  have har := mixed_last_direct_m4_arithmetic hb hc
    (by simpa [hPC] using ey) (by simpa [hnotCP] using ez)
  omega

/-- The reflected below-last two-root branch (`Cy=C`, `Cz=P`).-/
theorem mixed_two_below_reflected
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y C)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z P)
    (hbelow : C.x < a - 1) :
    (b = 1 ∧ c = 1 ∧ C.x ≤ a - 2 ∧ 1 ≤ C.y ∧ 1 ≤ C.z ∧
      P.x = C.x + 1 ∧ P.y = C.y ∧ P.z = C.z - 1) ∨
    (C.x = 0 ∧ C.z = c ∧ b ≤ C.y ∧
      P.x = 0 ∧ P.y = C.y + 1 ∧ P.z = c - 1) := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hbounds := below_last_live_bounds h hxC hbelow
  have hez := h4_z_edge_exact h.antichain hzP hCS hne (by omega)
  have hxshape := root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow
  rcases hxshape with hu | hl
  · have hPy : 0 < P.y := by omega
    have hey := h4_y_edge_exact h.antichain hyC hPS (Ne.symm hne) hPy
    left
    have har := mixed_below_upper_direct_arithmetic hc hb hbounds.2 hbounds.1
      hu.2.2 hu.2.1 (by simpa [hu.1, show ¬C.x + 1 < C.x by omega] using hez)
      (by simpa [hu.1] using hey)
    omega
  · have hPy : 0 < P.y := by
      by_cases hr : 0 < C.x
      · simp [hl.1, hr] at hez
        omega
      · simp [hl.1, hr] at hez
        omega
    have hey := h4_y_edge_exact h.antichain hyC hPS (Ne.symm hne) hPy
    right
    have har := mixed_below_lower_direct_arithmetic hc hb hbounds.2 hbounds.1
      (by tauto : ¬(c ≤ P.z ∧ b ≤ P.y))
      (by simpa [hl.1] using hez) (by simpa [hl.1] using hey)
    omega

/-- The reflected last-layer two-root branch (`Cy=C`, `Cz=P`) is reflected M4.-/
theorem mixed_two_last_reflected
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y C)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z P)
    (hlast : C.x = a - 1) :
    b = 1 ∧ c = 1 ∧ C.x = a - 1 ∧ 1 ≤ C.z ∧
      P.x = 0 ∧ P.y = C.y + 1 ∧ P.z = C.z := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
  have hPC : P.x < C.x := by have := h.a_ge_two; omega
  have hnotCP : ¬C.x < P.x := by omega
  have hCz : 0 < C.z := by
    by_contra hz0
    have hz0' : C.z = 0 := by omega
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨R, hRS, htR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    have htie : Normal.DividesCriterion (liveTiePoint : Normal a b c) C ∨
        Normal.DividesCriterion (liveTiePoint : Normal a b c) P := by
      rcases hRC with hRC | hRP
      · subst R; exact Or.inl ((Normal.exact_divides_iff _ _).1 htR)
      · subst R; exact Or.inr ((Normal.exact_divides_iff _ _).1 htR)
    simp [liveTiePoint, Normal.DividesCriterion] at htie
    rcases htie with htC | htP
    · omega
    · have hPy : 0 < P.y := by omega
      have ey := h4_y_edge_exact h.antichain hyC hPS (Ne.symm hne) hPy
      simp [hnotCP, hz0'] at ey
      omega
  have ez := h4_z_edge_exact h.antichain hzP hCS hne hCz
  have hPy : 0 < P.y := by simp [hPC] at ez; omega
  have ey := h4_y_edge_exact h.antichain hyC hPS (Ne.symm hne) hPy
  have har := mixed_last_direct_m4_arithmetic hc hb
    (by simpa [hPC] using ez) (by simpa [hnotCP] using ey)
  omega

theorem mixed_two_below_common_impossible
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y P)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z P)
    (hbelow : C.x < a - 1) : False := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
  have hez := h4_z_edge_exact h.antichain hzP hCS hne (by omega)
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow with hu | hl
  · simp [hu.1, show ¬C.x + 1 < C.x by omega] at hey hez
    omega
  · by_cases hr : 0 < C.x
    · simp [hl.1, hr] at hey hez
      omega
    · simp [hl.1, hr] at hey hez
      omega

/-- At the last layer a common y/z centre is M5 or its reflection.-/
theorem mixed_two_last_common
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .y P)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .z P)
    (hlast : C.x = a - 1) :
    (C.y = 0 ∧ 1 ≤ C.z ∧ P.x = 0 ∧ P.y = b ∧ P.z = C.z + c - 1) ∨
    (C.z = 0 ∧ 1 ≤ C.y ∧ P.x = 0 ∧ P.y = C.y + b - 1 ∧ P.z = c) := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b c)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
  have hPC : P.x < C.x := by have := h.a_ge_two; omega
  rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
    ⟨R, hRS, htR⟩
  have hRC : R = C ∨ R = P := by simpa using hRS
  have htie : Normal.DividesCriterion (liveTiePoint : Normal a b c) C ∨
      Normal.DividesCriterion (liveTiePoint : Normal a b c) P := by
    rcases hRC with hRC | hRP
    · subst R; exact Or.inl ((Normal.exact_divides_iff _ _).1 htR)
    · subst R; exact Or.inr ((Normal.exact_divides_iff _ _).1 htR)
  simp [liveTiePoint, Normal.DividesCriterion] at htie
  by_cases hCy : C.y = 0
  · left
    have hpTie : b ≤ P.y ∧ c ≤ P.z := by
      rcases htie with htC | htP
      · omega
      · exact ⟨by omega, by omega⟩
    have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hne)
      hxP hpTie.1 hpTie.2
    have hnCP : ¬Normal.DividesCriterion C P := by
      intro hd
      exact (h.antichain C hCS P hPS hne) ((Normal.exact_divides_iff C P).2 hd)
    unfold Normal.DividesCriterion at hnCP
    have hCz : 0 < C.z := by omega
    have hez := h4_z_edge_exact h.antichain hzP hCS hne hCz
    simp [hPC, hCy] at hez
    omega
  · right
    have hCz : C.z = 0 := by
      by_contra hz0
      have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
      have hez := h4_z_edge_exact h.antichain hzP hCS hne (by omega)
      simp [hPC] at hey hez
      omega
    have hpTie : b ≤ P.y ∧ c ≤ P.z := by
      rcases htie with htC | htP
      · omega
      · exact ⟨by omega, by omega⟩
    have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
    have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hne)
      hxP hpTie.1 hpTie.2
    simp [hPC, hCz] at hey
    omega

/-- Complete mixed two-root core classification.-/
theorem h5_mixed_two_coordinate_cover
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C) :
    MixedTwoCoordinateCase C P := by
  rcases h.centres .y with ⟨Y, hY⟩
  rcases h.centres .z with ⟨Z, hZ⟩
  have hYm : Y = C ∨ Y = P := by simpa using hY.1
  have hZm : Z = C ∨ Z = P := by simpa using hZ.1
  rcases hYm with hYC | hYP
  · subst Y
    rcases hZm with hZC | hZP
    · subst Z
      exact False.elim ((directional_centres_not_all_equal h hxC hY hZ) ⟨rfl, rfl⟩)
    · subst Z
      by_cases hlast : C.x = a - 1
      · have hm := mixed_two_last_reflected C P hne h hb hc hxC hY hZ hlast
        simp only [MixedTwoCoordinateCase]
        right; right; right; right; right; left
        exact hm
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        rcases mixed_two_below_reflected C P hne h hb hc hxC hY hZ hbelow with hm2 | hm3
        · simp only [MixedTwoCoordinateCase]
          right; left; exact hm2
        · simp only [MixedTwoCoordinateCase]
          right; right; right; left; exact hm3
  · subst Y
    rcases hZm with hZC | hZP
    · subst Z
      by_cases hlast : C.x = a - 1
      · have hm := mixed_two_last_direct C P hne h hb hc hxC hY hZ hlast
        simp only [MixedTwoCoordinateCase]
        right; right; right; right; left
        exact hm
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        rcases mixed_two_below_direct C P hne h hb hc hxC hY hZ hbelow with hm2 | hm3
        · simp only [MixedTwoCoordinateCase]
          left; exact hm2
        · simp only [MixedTwoCoordinateCase]
          right; right; left; exact hm3
    · subst Z
      by_cases hlast : C.x = a - 1
      · rcases mixed_two_last_common C P hne h hb hc hxC hY hZ hlast with hm5 | hm5r
        · simp only [MixedTwoCoordinateCase]
          right; right; right; right; right; right; left
          exact ⟨hlast, hm5.1, hm5.2.1, hm5.2.2.1, hm5.2.2.2.1, hm5.2.2.2.2⟩
        · simp only [MixedTwoCoordinateCase]
          right; right; right; right; right; right; right
          exact ⟨hlast, hm5r.1, hm5r.2.1, hm5r.2.2.1, hm5r.2.2.2.1,
            hm5r.2.2.2.2⟩
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        exact False.elim (mixed_two_below_common_impossible C P hne h hb hc hxC hY hZ hbelow)

theorem pure_below_lower_direct_arithmetic
    {r u v U V b : ℕ} (hb : 2 ≤ b) (hu : b ≤ u)
    (hnw : ¬b ≤ U)
    (ey : u + (if 0 < r then b else 0) = U + 1 ∧ v ≤ V)
    (ez : V = v + 1 ∧ U ≤ u) :
    r = 0 ∧ u = b ∧ U = b - 1 ∧ V = v + 1 := by
  by_cases hr : 0 < r <;> simp [hr] at ey <;> omega

/-- Pure direct below-last branch is P3; the apparent upper branch is impossible.-/
theorem pure_two_below_direct
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .y P)
    (hzC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .z C)
    (hbelow : C.x < a - 1) :
    C.x = 0 ∧ C.y = b ∧ P.x = 0 ∧ P.y = b - 1 ∧ P.z = C.z + 1 := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have hzlive : 0 < C.z ∨ 0 < P.z := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨R, hRS, hzR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · exact Or.inl ((Normal.zGenerator_dvd_iff C).1 (by simpa [hRC] using hzR))
    · exact Or.inr ((Normal.zGenerator_dvd_iff P).1 (by simpa [hRP] using hzR))
  have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow with hu | hl
  · have hPz : 0 < P.z := by omega
    have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
    simp [hu.1, show ¬C.x + 1 < C.x by omega] at hey hez
    omega
  · have hPz : 0 < P.z := by
      by_cases hr : 0 < C.x <;> simp [hl.1, hr] at hey <;> omega
    have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hPz
    have hnw : ¬b ≤ P.y := by simpa using hl.2
    have har := pure_below_lower_direct_arithmetic hb hbnd.1 hnw
      (by simpa [hl.1] using hey) (by simpa [hl.1] using hez)
    omega

/-- Pure direct last-layer branch is P5.-/
theorem pure_two_last_direct
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .y P)
    (hzC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .z C)
    (hlast : C.x = a - 1) :
    C.y = 0 ∧ 1 ≤ C.z ∧ P.x = 0 ∧ P.y = b ∧ P.z = 0 := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
  have hPC : P.x < C.x := by have := h.a_ge_two; omega
  have hzlive : 0 < C.z ∨ 0 < P.z := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨R, hRS, hzR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · exact Or.inl ((Normal.zGenerator_dvd_iff C).1 (by simpa [hRC] using hzR))
    · exact Or.inr ((Normal.zGenerator_dvd_iff P).1 (by simpa [hRP] using hzR))
  have hCy : C.y = 0 := by
    by_contra hy0
    have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
    by_cases hpz : 0 < P.z
    · have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) hpz
      simp [hPC, show ¬C.x < P.x by omega] at hey hez
      omega
    · have hCz : 0 < C.z := by omega
      simp [hPC] at hey
      have hpTie : b ≤ P.y := by
        rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
          ⟨R, hRS, htR⟩
        have hRC : R = C ∨ R = P := by simpa using hRS
        rcases hRC with hRC | hRP
        · have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1
              (by simpa [hRC] using htR)
          simp [liveTiePoint, Normal.DividesCriterion] at ht
          omega
        · have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) P).1
              (by simpa [hRP] using htR)
          simp [liveTiePoint, Normal.DividesCriterion] at ht
          omega
      omega
  have hpTie : b ≤ P.y := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨R, hRS, htR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    have htie : Normal.DividesCriterion (liveTiePoint : Normal a b 0) C ∨
        Normal.DividesCriterion (liveTiePoint : Normal a b 0) P := by
      rcases hRC with hRC | hRP
      · subst R; exact Or.inl ((Normal.exact_divides_iff _ _).1 htR)
      · subst R; exact Or.inr ((Normal.exact_divides_iff _ _).1 htR)
    simp [liveTiePoint, Normal.DividesCriterion] at htie
    rcases htie with htC | htP
    · omega
    · omega
  have hPz : P.z = 0 := by
    by_contra hpz0
    have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hne) (by omega)
    simp [hCy, show ¬C.x < P.x by omega] at hez
    omega
  have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hne)
    hxP hpTie (by simp)
  omega

/-- Pure common-centre below-last branch is P4.-/
theorem pure_two_below_common
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .y P)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .z P)
    (hbelow : C.x < a - 1) :
    C.x = 0 ∧ C.y = b ∧ C.z = 0 ∧ P.x = 0 ∧ P.y = b - 1 ∧ 1 ≤ P.z := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
  have hzlive : 0 < C.z ∨ 0 < P.z := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨R, hRS, hzR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · exact Or.inl ((Normal.zGenerator_dvd_iff C).1 (by simpa [hRC] using hzR))
    · exact Or.inr ((Normal.zGenerator_dvd_iff P).1 (by simpa [hRP] using hzR))
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow with hu | hl
  · by_cases hCz : 0 < C.z
    · have hez := h4_z_edge_exact h.antichain hzP hCS hne hCz
      simp [hu.1, show ¬C.x + 1 < C.x by omega] at hey hez
      omega
    · simp [hu.1, show ¬C.x + 1 < C.x by omega] at hey
      omega
  · by_cases hCz : 0 < C.z
    · have hez := h4_z_edge_exact h.antichain hzP hCS hne hCz
      by_cases hr : 0 < C.x <;> simp [hl.1, hr] at hey hez <;> omega
    · by_cases hr : 0 < C.x <;> simp [hl.1, hr] at hey <;> omega

/-- Pure common-centre last-layer branch is P6.-/
theorem pure_two_last_common
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .y P)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .z P)
    (hlast : C.x = a - 1) :
    C.y = 0 ∧ 1 ≤ C.z ∧ P.x = 0 ∧ P.y = b ∧ P.z = C.z - 1 := by
  have hCS : C ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
  have hCz : 0 < C.z := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨R, hRS, hzR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · exact (Normal.zGenerator_dvd_iff C).1 (by simpa [hRC] using hzR)
    · have hPz := (Normal.zGenerator_dvd_iff P).1 (by simpa [hRP] using hzR)
      have hpTie : b ≤ P.y := by
        by_cases hCy : 0 < C.y
        · have hey := h4_y_edge_exact h.antichain hyP hCS hne hCy
          have hPC : P.x < C.x := by have := h.a_ge_two; omega
          simp [hPC] at hey
          omega
        · rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
            ⟨Q, hQS, htQ⟩
          have hQC : Q = C ∨ Q = P := by simpa using hQS
          rcases hQC with hQC | hQP
          · have ht :=
                (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1
                  (by simpa [hQC] using htQ)
            simp [liveTiePoint, Normal.DividesCriterion] at ht
            omega
          · have ht :=
                (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) P).1
                  (by simpa [hQP] using htQ)
            simp [liveTiePoint, Normal.DividesCriterion] at ht
            omega
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hne)
        hxP hpTie (by simp)
      omega
  have hez := h4_z_edge_exact h.antichain hzP hCS hne hCz
  have hPC : P.x < C.x := by have := h.a_ge_two; omega
  have hCy : C.y = 0 := by
    by_contra hy0
    have hey := h4_y_edge_exact h.antichain hyP hCS hne (by omega)
    have hez' := hez
    simp [hPC] at hey hez'
    omega
  have hpTie : b ≤ P.y := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨R, hRS, htR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1
          (by simpa [hRC] using htR)
      simp [liveTiePoint, Normal.DividesCriterion] at ht
      omega
    · have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) P).1
          (by simpa [hRP] using htR)
      simp [liveTiePoint, Normal.DividesCriterion] at ht
      omega
  have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hne)
    hxP hpTie (by simp)
  simp [hPC] at hez
  omega

/- With `Cy=C` and `Cz=P`, the pure two-root configuration is the
fibre-product shape. -/
set_option maxHeartbeats 800000 in
theorem pure_two_fibre_coordinate
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0)))
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C)
    (hyC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .y C)
    (hzP : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .z P) :
    (C.x = 0 ∧ C.y = 0 ∧ 1 ≤ C.z ∧ P.z = 0) ∨
      (P.x = 0 ∧ P.y = 0 ∧ 1 ≤ P.z ∧ C.z = 0) := by
  have ha2 := h.a_ge_two
  have hb2 : 2 ≤ b := by
    rcases h.live_domain with hm | hp
    · omega
    · exact hp.1
  have hC_lt := C.x_lt
  have hP_lt := P.x_lt
  have hCS : C ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P} : Finset (Normal a b 0)) := by simp
  have hzlive : 0 < C.z ∨ 0 < P.z := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨R, hRS, hzR⟩
    have hRC : R = C ∨ R = P := by simpa using hRS
    rcases hRC with hRC | hRP
    · subst R; exact Or.inl ((Normal.zGenerator_dvd_iff C).1 hzR)
    · subst R; exact Or.inr ((Normal.zGenerator_dvd_iff P).1 hzR)
  have hyEdge : 0 < P.y →
      P.y + (if C.x < P.x then b else 0) = C.y + 1 ∧ P.z ≤ C.z := by
    intro hp
    simpa using h4_y_edge_exact h.antichain hyC hPS (Ne.symm hne) hp
  have hzEdge : 0 < C.z →
      C.z + (if P.x < C.x then 0 else 0) = P.z + 1 ∧
        C.y + (if P.x < C.x then b else 0) ≤ P.y := by
    intro hc
    simpa using h4_z_edge_exact h.antichain hzP hCS hne hc
  by_cases hlast : C.x = a - 1
  · have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hne) hlast
    have hPC : P.x < C.x := by omega
    have hCz : C.z = 0 := by
      by_contra hc0
      have hz := hzEdge (by omega)
      by_cases hpY : 0 < P.y
      · have hy := hyEdge hpY
        simp [hPC, show ¬C.x < P.x by omega] at hz hy
        omega
      · simp [hPC] at hz
        omega
    right
    have hPz : 0 < P.z := by omega
    have hPy : P.y = 0 := by
      by_contra hp0
      have hy := hyEdge (by omega)
      simp [show ¬C.x < P.x by omega, hCz] at hy
      omega
    exact ⟨hxP, hPy, hPz, hCz⟩
  · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
    have hbnd := below_last_live_bounds h hxC hbelow
    rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hne) hbelow with hu | hl
    · have hCz : C.z = 0 := by
        by_contra hc0
        have hz := hzEdge (by omega)
        by_cases hpY : 0 < P.y
        · have hy := hyEdge hpY
          simp [hu.1, show ¬C.x + 1 < C.x by omega] at hz hy
          omega
        · simp [hu.1, show ¬C.x + 1 < C.x by omega] at hz
          omega
      have : False := by omega
      contradiction
    · have hCz : C.z = 0 := by
        by_contra hc0
        have hz := hzEdge (by omega)
        by_cases hr : 0 < C.x
        · simp [hl.1, hr] at hz
          omega
        · simp [hl.1, hr] at hz
          omega
      right
      have hPz : 0 < P.z := by omega
      have hPy : P.y = 0 := by
        by_contra hp0
        have hy := hyEdge (by omega)
        simp [hl.1, hCz] at hy
        omega
      exact ⟨hl.1, hPy, hPz, hCz⟩

/-- Complete pure two-root coordinate classification with a fixed x-centre.-/
theorem h5_pure_two_coordinate_cover
    (C P : Normal a b 0) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b 0)))
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b 0)) .x C) :
    PureTwoCoordinateCase C P := by
  have hb : 2 ≤ b := by
    rcases h.live_domain with hm | hp
    · omega
    · exact hp.1
  obtain ⟨Y, hy⟩ := h.centres .y
  obtain ⟨Z, hz⟩ := h.centres .z
  have hY : Y = C ∨ Y = P := by simpa using hy.1
  have hZ : Z = C ∨ Z = P := by simpa using hz.1
  rcases hY with hYC | hYP
  · subst Y
    rcases hZ with hZC | hZP
    · subst Z
      exact False.elim
        (directional_centres_not_all_equal h hxC hy hz ⟨rfl, rfl⟩)
    · subst Z
      rcases pure_two_fibre_coordinate C P hne h hxC hy hz with hf | hf
      · simp only [PureTwoCoordinateCase]
        right; right; right; right; left
        exact hf
      · simp only [PureTwoCoordinateCase]
        right; right; right; right; right
        exact hf
  · subst Y
    rcases hZ with hZC | hZP
    · subst Z
      by_cases hlast : C.x = a - 1
      · have hp5 := pure_two_last_direct C P hne h hb hxC hy hz hlast
        simp only [PureTwoCoordinateCase]
        right; right; left
        exact ⟨hlast, hp5.1, hp5.2.1, hp5.2.2.1, hp5.2.2.2.1,
          hp5.2.2.2.2⟩
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        have hp3 := pure_two_below_direct C P hne h hb hxC hy hz hbelow
        simp only [PureTwoCoordinateCase]
        left
        exact hp3
    · subst Z
      by_cases hlast : C.x = a - 1
      · have hp6 := pure_two_last_common C P hne h hb hxC hy hz hlast
        simp only [PureTwoCoordinateCase]
        right; right; right; left
        exact ⟨hlast, hp6.1, hp6.2.1, hp6.2.2.1, hp6.2.2.2.1,
          hp6.2.2.2.2⟩
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        have hp4 := pure_two_below_common C P hne h hb hxC hy hz hbelow
        simp only [PureTwoCoordinateCase]
        right; left
        exact hp4

theorem swapYZFinset_pair (C P : Normal a b c) :
    swapYZFinset ({C, P} : Finset (Normal a b c)) = {swapYZ C, swapYZ P} := by
  unfold swapYZFinset
  rw [Finset.map_insert, Finset.map_singleton]
  rfl

theorem swapYZFinset_triple (C P R : Normal a b c) :
    swapYZFinset ({C, P, R} : Finset (Normal a b c)) =
      {swapYZ C, swapYZ P, swapYZ R} := by
  unfold swapYZFinset
  rw [Finset.map_insert, Finset.map_insert, Finset.map_singleton]
  rfl

theorem swapYZFinset_swapYZFinset (S : Finset (Normal a b c)) :
    swapYZFinset (swapYZFinset S) = S := by
  ext p
  simp only [swapYZFinset, Finset.mem_map]
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hqp⟩
    change swapYZ (swapYZ r) = p at hqp
    simpa using hqp ▸ hr
  · intro hp
    refine ⟨swapYZ p, ⟨p, hp, rfl⟩, ?_⟩
    change swapYZ (swapYZ p) = p
    simp

theorem directionalCentre_swapYZ_x {S : Finset (Normal a b c)}
    {C : Normal a b c} (hC : IsDirectionalCentre S .x C) :
    IsDirectionalCentre (swapYZFinset S) .x (swapYZ C) := by
  refine ⟨Finset.mem_map.mpr ⟨C, hC.1, rfl⟩, ?_⟩
  intro s hs q hq
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change Normal.predecessor .x (swapYZ t) = some q at hq
  rw [swapYZ_predecessor_x] at hq
  rcases Option.map_eq_some_iff.mp hq with ⟨r, hr, rfl⟩
  exact (swapYZ_divides_iff r C).2 (hC.2 t ht r hr)

theorem directionalCentre_swapYZ_y {S : Finset (Normal a b c)}
    {C : Normal a b c} (hC : IsDirectionalCentre S .z C) :
    IsDirectionalCentre (swapYZFinset S) .y (swapYZ C) := by
  refine ⟨Finset.mem_map.mpr ⟨C, hC.1, rfl⟩, ?_⟩
  intro s hs q hq
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change Normal.predecessor .y (swapYZ t) = some q at hq
  rw [swapYZ_predecessor_y] at hq
  rcases Option.map_eq_some_iff.mp hq with ⟨r, hr, rfl⟩
  exact (swapYZ_divides_iff r C).2 (hC.2 t ht r hr)

theorem directionalCentre_swapYZ_z {S : Finset (Normal a b c)}
    {C : Normal a b c} (hC : IsDirectionalCentre S .y C) :
    IsDirectionalCentre (swapYZFinset S) .z (swapYZ C) := by
  refine ⟨Finset.mem_map.mpr ⟨C, hC.1, rfl⟩, ?_⟩
  intro s hs q hq
  rcases Finset.mem_map.mp hs with ⟨t, ht, rfl⟩
  change Normal.predecessor .z (swapYZ t) = some q at hq
  rw [swapYZ_predecessor_z] at hq
  rcases Option.map_eq_some_iff.mp hq with ⟨r, hr, rfl⟩
  exact (swapYZ_divides_iff r C).2 (hC.2 t ht r hr)

theorem coverHypotheses_swapYZ {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    CoverHypotheses (swapYZFinset S) := by
  have ha1 : a ≠ 1 := by have := h.a_ge_two; omega
  have hanti : IsRootAntichain (swapYZFinset S) := by
    intro p hp q hq hpq hd
    rcases Finset.mem_map.mp hp with ⟨p0, hp0, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨q0, hq0, rfl⟩
    have hpq0 : p0 ≠ q0 := by
      intro heq
      subst q0
      exact hpq rfl
    exact h.antichain p0 hp0 q0 hq0 hpq0 ((swapYZ_divides_iff p0 q0).1 hd)
  have hcentres : HasDirectionalCentres (swapYZFinset S) := by
    intro e
    cases e with
    | x =>
        rcases h.centres .x with ⟨C, hC⟩
        exact ⟨swapYZ C, directionalCentre_swapYZ_x hC⟩
    | y =>
        rcases h.centres .z with ⟨C, hC⟩
        exact ⟨swapYZ C, directionalCentre_swapYZ_y hC⟩
    | z =>
        rcases h.centres .y with ⟨C, hC⟩
        exact ⟨swapYZ C, directionalCentre_swapYZ_z hC⟩
  refine {
    a_ge_two := h.a_ge_two
    live_domain := ?_
    live_tie := ?_
    card_ge_two := ?_
    card_le_three := ?_
    antichain := hanti
    centres := hcentres
    no_dominant := ?_ }
  · exact Or.inl ⟨hc, hb⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Normal.xGenerator, swapYZ, ha1] using
        (mem_standardSet_swapYZFinset_iff S
          (Normal.xGenerator : Normal a b c)).2 h.live_tie.1
    · simpa [Normal.yGenerator, Normal.zGenerator, swapYZ] using
        (mem_standardSet_swapYZFinset_iff S
          (Normal.zGenerator : Normal a b c)).2 h.live_tie.2.2.1
    · simpa [Normal.yGenerator, Normal.zGenerator, swapYZ] using
        (mem_standardSet_swapYZFinset_iff S
          (Normal.yGenerator : Normal a b c)).2 h.live_tie.2.1
    · simpa [liveTiePoint, swapYZ] using
        (mem_standardSet_swapYZFinset_iff S
          (liveTiePoint : Normal a b c)).2 h.live_tie.2.2.2
  · simpa [swapYZFinset] using h.card_ge_two
  · simpa [swapYZFinset] using h.card_le_three
  · intro D hD hdom
    rcases Finset.mem_map.mp hD with ⟨C, hCS, rfl⟩
    have hallSwap :=
      ((isDominantRoot_iff_all_directionalCentre (swapYZFinset S) (swapYZ C)
        h.a_ge_two hanti).1 hdom).2
    have hxBack := directionalCentre_swapYZ_x (hallSwap .x)
    have hyBack := directionalCentre_swapYZ_y (hallSwap .z)
    have hzBack := directionalCentre_swapYZ_z (hallSwap .y)
    have hx : IsDirectionalCentre S .x C := by
      simpa [swapYZFinset_swapYZFinset] using hxBack
    have hy : IsDirectionalCentre S .y C := by
      simpa [swapYZFinset_swapYZFinset] using hyBack
    have hz : IsDirectionalCentre S .z C := by
      simpa [swapYZFinset_swapYZFinset] using hzBack
    apply h.no_dominant C hCS
    exact (isDominantRoot_iff_all_directionalCentre S C h.a_ge_two h.antichain).2
      ⟨hCS, fun e => by cases e <;> assumption⟩

/-- The mixed coordinate leaves give the exact unordered two-root cover shape,
with y/z reflection represented by the public reflection wrapper.-/
theorem mixed_coordinate_case_cover_shape
    (C P : Normal a b c) (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hm : MixedTwoCoordinateCase C P) :
    CoverShape ({C, P} : Finset (Normal a b c)) := by
  have ha := h.a_ge_two
  rcases hm with hm2 | hm2r | hm3 | hm3r | hm4 | hm4r | hm5 | hm5r
  · all_goals
      rcases hm2 with ⟨hb1, hc1, hr, hu, hv, hpx, hpy, hpz⟩
      subst b; subst c
      let r := C.x
      let u := C.y
      let v := C.z
      have hr' : r ≤ a - 2 := by simpa [r] using hr
      have hC : C = m2Core ha r u v hr' := by
        apply Normal.ext <;> simp [m2Core, r, u, v]
      have hP : P = m2Partner ha r u v hr' := by
        apply Normal.ext <;> simp [m2Partner, r, u, v, hpx, hpy, hpz]
      have hS : ({C, P} : Finset (Normal a 1 1)) = m2Socles ha r u v hr' := by
        rw [hC, hP]
        rfl
      rw [hS]
      exact CoverShape.direct (BaseCoverShape.m2 ha (by simpa [u] using hu)
        (by simpa [v] using hv) hr')
  · all_goals
      rcases hm2r with ⟨hb1, hc1, hr, hu, hv, hpx, hpy, hpz⟩
      subst b; subst c
      have hC : swapYZ C = m2Core ha C.x C.z C.y hr := by
        apply Normal.ext <;> simp [swapYZ, m2Core]
      have hP : swapYZ P = m2Partner ha C.x C.z C.y hr := by
        apply Normal.ext <;> simp [swapYZ, m2Partner, hpx, hpy, hpz]
      apply CoverShape.reflected (by omega) (by omega)
      have hS : swapYZFinset ({C, P} : Finset (Normal a 1 1)) =
          m2Socles ha C.x C.z C.y hr := by
        rw [swapYZFinset_pair]
        rw [hC, hP]
        rfl
      rw [hS]
      exact BaseCoverShape.m2 ha hv hu hr
  · all_goals
      rcases hm3 with ⟨hcx, hcy, hv, hpx, hpy, hpz⟩
      have hC : C = m3KCore C.z := by
        apply Normal.ext <;> simp [m3KCore, hcx, hcy]
      have hP : P = m3KPartner C.z := by
        apply Normal.ext <;> simp [m3KPartner, hpx, hpy, hpz]
      have hS : ({C, P} : Finset (Normal a b c)) = m3Socles C.z := by
        rw [hC, hP]
        rfl
      rw [hS]
      exact CoverShape.direct (BaseCoverShape.m3 ha hb hc hv)
  · all_goals
      rcases hm3r with ⟨hcx, hcz, hv, hpx, hpy, hpz⟩
      have hC : swapYZ C = (m3KCore (a := a) (b := c) (c := b) C.y) := by
        apply Normal.ext <;> simp [swapYZ, m3KCore, hcx, hcz]
      have hP : swapYZ P = (m3KPartner (a := a) (b := c) (c := b) C.y) := by
        apply Normal.ext <;> simp [swapYZ, m3KPartner, hpx, hpy, hpz]
      apply CoverShape.reflected hb hc
      have hS : swapYZFinset ({C, P} : Finset (Normal a b c)) =
          m3Socles (a := a) (b := c) (c := b) C.y := by
        rw [swapYZFinset_pair]
        rw [hC, hP]
        rfl
      rw [hS]
      exact BaseCoverShape.m3 ha hc hb hv
  · all_goals
      rcases hm4 with ⟨hb1, hc1, hcx, hu, hpx, hpy, hpz⟩
      subst b; subst c
      have hC : C = m4YCore ha C.y C.z := by
        apply Normal.ext <;> simp [m4YCore, hcx]
      have hP : P = m4YPartner C.y C.z := by
        apply Normal.ext <;> simp [m4YPartner, hpx, hpy, hpz]
      have hS : ({C, P} : Finset (Normal a 1 1)) = m4Socles ha C.y C.z := by
        rw [hC, hP]
        rfl
      rw [hS]
      exact CoverShape.direct (BaseCoverShape.m4 ha hu)
  · all_goals
      rcases hm4r with ⟨hb1, hc1, hcx, hv, hpx, hpy, hpz⟩
      subst b; subst c
      have hC : swapYZ C = m4YCore ha C.z C.y := by
        apply Normal.ext <;> simp [swapYZ, m4YCore, hcx]
      have hP : swapYZ P = m4YPartner C.z C.y := by
        apply Normal.ext <;> simp [swapYZ, m4YPartner, hpx, hpy, hpz]
      apply CoverShape.reflected (by omega) (by omega)
      have hS : swapYZFinset ({C, P} : Finset (Normal a 1 1)) =
          m4Socles ha C.z C.y := by
        rw [swapYZFinset_pair]
        rw [hC, hP]
        rfl
      rw [hS]
      exact BaseCoverShape.m4 ha hv
  · all_goals
      rcases hm5 with ⟨hcx, hcy, hv, hpx, hpy, hpz⟩
      have hC : C = m5Core ha C.z := by
        apply Normal.ext <;> simp [m5Core, hcx, hcy]
      have hP : P = m5Partner C.z c := by
        apply Normal.ext <;> simp [m5Partner, hpx, hpy, hpz]
      have hS : ({C, P} : Finset (Normal a b c)) = m5Socles ha C.z := by
        rw [hC, hP]
        rfl
      rw [hS]
      exact CoverShape.direct (BaseCoverShape.m5 ha hb hc hv)
  · all_goals
      rcases hm5r with ⟨hcx, hcz, hv, hpx, hpy, hpz⟩
      have hC : swapYZ C = (m5Core (b := c) (c := b) ha C.y) := by
        apply Normal.ext <;> simp [swapYZ, m5Core, hcx, hcz]
      have hP : swapYZ P = (m5Partner (a := a) (b := c) C.y b) := by
        apply Normal.ext <;> simp [swapYZ, m5Partner, hpx, hpy, hpz]
      apply CoverShape.reflected hb hc
      have hS : swapYZFinset ({C, P} : Finset (Normal a b c)) =
          m5Socles (a := a) (b := c) (c := b) ha C.y := by
        rw [swapYZFinset_pair]
        rw [hC, hP]
        rfl
      rw [hS]
      exact BaseCoverShape.m5 ha hc hb hv

/-- The pure coordinate leaves give the exact unordered two-root cover shape.-/
theorem pure_coordinate_case_cover_shape
    (C P : Normal a b 0) (h : CoverHypotheses ({C, P} : Finset (Normal a b 0)))
    (hp : PureTwoCoordinateCase C P) :
    CoverShape ({C, P} : Finset (Normal a b 0)) := by
  have ha := h.a_ge_two
  have hb : 2 ≤ b := by
    rcases h.live_domain with hm | hpure
    · omega
    · exact hpure.1
  rcases hp with hp3 | hp4 | hp5 | hp6 | hf | hf
  · rcases hp3 with ⟨hcx, hcy, hpx, hpy, hpz⟩
    have hC : C = (⟨0, b, C.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hcx, hcy]
    have hP : P = (⟨0, b - 1, C.z + 1, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hpx, hpy, hpz]
    have hS : ({C, P} : Finset (Normal a b 0)) = p3Socles C.z := by
      rw [hC, hP]
      rfl
    rw [hS]
    exact CoverShape.direct (BaseCoverShape.p3 ha hb)
  · rcases hp4 with ⟨hcx, hcy, hcz, hpx, hpy, hpz⟩
    have hC : C = (⟨0, b, 0, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hcx, hcy, hcz]
    have hP : P = (⟨0, b - 1, P.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hpx, hpy]
    have hS : ({C, P} : Finset (Normal a b 0)) = p4Socles P.z := by
      rw [hC, hP]
      rfl
    rw [hS]
    exact CoverShape.direct (BaseCoverShape.p4 ha hb hpz)
  · rcases hp5 with ⟨hcx, hcy, hcz, hpx, hpy, hpz⟩
    have hC : C = (⟨a - 1, 0, C.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hcx, hcy]
    have hP : P = (⟨0, b, 0, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hpx, hpy, hpz]
    have hS : ({C, P} : Finset (Normal a b 0)) = p5Socles ha C.z := by
      rw [hC, hP]
      rfl
    rw [hS]
    exact CoverShape.direct (BaseCoverShape.p5 ha hb hcz)
  · rcases hp6 with ⟨hcx, hcy, hcz, hpx, hpy, hpz⟩
    have hC : C = (⟨a - 1, 0, C.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hcx, hcy]
    have hP : P = (⟨0, b, C.z - 1, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hpx, hpy, hpz]
    have hS : ({C, P} : Finset (Normal a b 0)) = p6Socles ha C.z := by
      rw [hC, hP]
      rfl
    rw [hS]
    exact CoverShape.direct (BaseCoverShape.p6 ha hb hcz)
  · refine CoverShape.direct (BaseCoverShape.pureFibreProduct ?_)
    refine ⟨rfl, C.z, hf.2.2.1, ?_, ?_⟩
    · apply Finset.mem_insert.mpr
      left
      apply Normal.ext <;> simp [hf.1, hf.2.1]
    · intro R hR hRC
      have hRP : R = C ∨ R = P := by simpa using hR
      rcases hRP with rfl | rfl
      · exact False.elim
          (hRC (by apply Normal.ext <;> simp [hf.1, hf.2.1]))
      · exact hf.2.2.2
  · refine CoverShape.direct (BaseCoverShape.pureFibreProduct ?_)
    refine ⟨rfl, P.z, hf.2.2.1, ?_, ?_⟩
    · apply Finset.mem_insert.mpr
      right
      simp only [Finset.mem_singleton]
      apply Normal.ext <;> simp [hf.1, hf.2.1]
    · intro R hR hRP
      have hRC : R = C ∨ R = P := by simpa using hR
      rcases hRC with rfl | rfl
      · exact hf.2.2.2
      · exact False.elim
          (hRP (by apply Normal.ext <;> simp [hf.1, hf.2.1]))

/-- Complete exact-shape theorem for a two-root configuration with a selected
x-centre.  The mixed and pure live domains are separated before invoking the
coordinate classifications.-/
theorem h5_two_root_cover
    (C P : Normal a b c) (hne : C ≠ P)
    (h : CoverHypotheses ({C, P} : Finset (Normal a b c)))
    (hxC : IsDirectionalCentre ({C, P} : Finset (Normal a b c)) .x C) :
    CoverShape ({C, P} : Finset (Normal a b c)) := by
  rcases h.live_domain with hmix | hpure
  · exact mixed_coordinate_case_cover_shape C P h hmix.1 hmix.2
      (h5_mixed_two_coordinate_cover C P hne h hmix.1 hmix.2 hxC)
  · rcases hpure with ⟨hb, hc⟩
    subst c
    exact pure_coordinate_case_cover_shape C P h
      (h5_pure_two_coordinate_cover C P hne h hxC)

/-- Human I.b, direct orientation: with a third root present, the M2/M3
core extends only to M2K, M2Z, or M3K.-/
theorem mixed_below_direct_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y P)
    (hzC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z C)
    (hbelow : C.x < a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have hey := h4_y_edge_exact h.antichain hyP hCS hCP (by omega)
  have hxP := root_shape_below_last h.antichain hxC hPS (Ne.symm hCP) hbelow
  have hcore :
      (b = 1 ∧ c = 1 ∧ C.x ≤ a - 2 ∧ 1 ≤ C.y ∧ 1 ≤ C.z ∧
        P.x = C.x + 1 ∧ P.y = C.y - 1 ∧ P.z = C.z) ∨
      (C.x = 0 ∧ C.y = b ∧ c ≤ C.z ∧
        P.x = 0 ∧ P.y = b - 1 ∧ P.z = C.z + 1) := by
    rcases hxP with hu | hl
    · have hPz : 0 < P.z := by omega
      have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) hPz
      left
      have har := mixed_below_upper_direct_arithmetic hb hc hbnd.1 hbnd.2
        hu.2.1 hu.2.2 (by simpa [hu.1, show ¬C.x + 1 < C.x by omega] using hey)
        (by simpa [hu.1] using hez)
      omega
    · have hPz : 0 < P.z := by
        by_cases hr : 0 < C.x <;> simp [hl.1, hr] at hey <;> omega
      have hez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) hPz
      right
      have har := mixed_below_lower_direct_arithmetic hb hc hbnd.1 hbnd.2
        hl.2 (by simpa [hl.1] using hey) (by simpa [hl.1] using hez)
      omega
  have hnRC : ¬Normal.DividesCriterion R C := by
    intro hd
    exact (h.antichain R hRS C hCS (Ne.symm hCR))
      ((Normal.exact_divides_iff R C).2 hd)
  have hnRP : ¬Normal.DividesCriterion R P := by
    intro hd
    exact (h.antichain R hRS P hPS (Ne.symm hPR))
      ((Normal.exact_divides_iff R P).2 hd)
  have hnPR : ¬Normal.DividesCriterion P R := by
    intro hd
    exact (h.antichain P hPS R hRS hPR)
      ((Normal.exact_divides_iff P R).2 hd)
  rcases hcore with hm2 | hm3
  · rcases hm2 with ⟨hb1, hc1, hr, hu, hv, hpx, hpy, hpz⟩
    subst b; subst c
    rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
    · by_cases hRz : R.z = 0
      · have hRy : R.y = C.y := by
          by_cases hRy0 : R.y = 0
          · unfold Normal.DividesCriterion at hnRP
            omega
          · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
            simp [hRu.1, hpx] at eRy
            omega
        let r := C.x
        let u := C.y
        let v := C.z
        have hr' : r ≤ a - 2 := by simpa [r] using hr
        have hC : C = m2Core ha r u v hr' := by
          apply Normal.ext <;> simp [m2Core, r, u, v]
        have hP : P = m2Partner ha r u v hr' := by
          apply Normal.ext <;> simp [m2Partner, r, u, v, hpx, hpy, hpz]
        have hR : R = m2KRoot ha r u hr' := by
          apply Normal.ext <;> simp [m2KRoot, r, u, hRu.1, hRy, hRz]
        have hS : ({C, P, R} : Finset (Normal a 1 1)) =
            m2KSocles ha r u v hr' := by
          rw [hC, hP, hR]
          rfl
        rw [hS]
        exact BaseCoverShape.m2K ha (by simpa [u] using hu)
          (by simpa [v] using hv) hr'
      · have hRzp : 0 < R.z := by omega
        by_cases hRy0 : R.y = 0
        · unfold Normal.DividesCriterion at hnRP
          omega
        · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) hRzp
          simp [hRu.1] at eRy eRz
          omega
    · by_cases hRy0 : R.y = 0
      · by_cases hRz0 : R.z = 0
        · unfold Normal.DividesCriterion at hnRC
          omega
        · have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
          have hRz : R.z = C.z + 1 := by simpa [hRl.1] using eRz.1
          let r := C.x
          let u := C.y
          let v := C.z
          have hr' : r ≤ a - 2 := by simpa [r] using hr
          have hC : C = m2Core ha r u v hr' := by
            apply Normal.ext <;> simp [m2Core, r, u, v]
          have hP : P = m2Partner ha r u v hr' := by
            apply Normal.ext <;> simp [m2Partner, r, u, v, hpx, hpy, hpz]
          have hR : R = m2ZRoot v := by
            apply Normal.ext <;> simp [m2ZRoot, v, hRl.1, hRy0, hRz]
          have hS : ({C, P, R} : Finset (Normal a 1 1)) =
              m2ZSocles ha r u v hr' := by
            rw [hC, hP, hR]
            rfl
          rw [hS]
          exact BaseCoverShape.m2Z ha (by simpa [u] using hu)
            (by simpa [v] using hv) hr'
      · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRl.1] at eRy
        unfold Normal.DividesCriterion at hnRC
        omega
  · rcases hm3 with ⟨hcx, hcy, hv, hpx, hpy, hpz⟩
    clear hey
    rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
    · have hRy0 : R.y = 0 := by
        by_contra hy0
        have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRu.1, hpx] at eRy
        omega
      have hRzp : 0 < R.z := by
        by_contra hz0
        unfold Normal.DividesCriterion at hnRC
        omega
      have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) hRzp
      have hRz : R.z = m3D C.z c := by
        simp [hRu.1, hcx] at eRz
        unfold m3D
        omega
      have hC : C = m3KCore C.z := by
        apply Normal.ext <;> simp [m3KCore, hcx, hcy]
      have hP : P = m3KPartner C.z := by
        apply Normal.ext <;> simp [m3KPartner, hpx, hpy, hpz]
      have hR : R = m3KRoot ha C.z c := by
        apply Normal.ext <;> simp [m3KRoot, hRu.1, hcx, hRy0, hRz]
      have hS : ({C, P, R} : Finset (Normal a b c)) =
          m3KSocles ha C.z := by
        rw [hC, hP, hR]
        rfl
      rw [hS]
      exact BaseCoverShape.m3K ha hb hc hv
    · by_cases hRy0 : R.y = 0
      · by_cases hRz0 : R.z = 0
        · unfold Normal.DividesCriterion at hnRC
          omega
        · have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
          simp [hRl.1, hcx] at eRz
          simp [Normal.DividesCriterion, hpx, hpy, hpz, hRl.1, hcx] at hnRP
          omega
      · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRl.1, hpx, hcx] at eRy
        simp [Normal.DividesCriterion, hcy, hpx, hpy, hpz, hRl.1, hcx] at hnRC hnPR
        omega

theorem mixed_below_common_impossible_three
    (C P R : Normal a b c) (hCP : C ≠ P)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y P)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z P)
    (hbelow : C.x < a - 1) : False := by
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have ey := h4_y_edge_exact h.antichain hyP hCS hCP (by omega)
  have ez := h4_z_edge_exact h.antichain hzP hCS hCP (by omega)
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hCP) hbelow with hu | hl
  · simp [hu.1, show ¬C.x + 1 < C.x by omega] at ey ez
    omega
  · by_cases hr : 0 < C.x <;> simp [hl.1, hr] at ey ez <;> omega

/-- Human I.b top-deletion branch: three distinct directional centres below
the last layer are the three immediate predecessors of one top.-/
theorem mixed_below_distinct_centres_top
    (C Y Z : Normal a b c) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .z Z)
    (hbelow : C.x < a - 1) (hCyPos : 0 < C.y) (hCzPos : 0 < C.z) :
    BaseCoverShape ({C, Y, Z} : Finset (Normal a b c)) := by
  have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hZS : Z ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have eyC := h4_y_edge_exact h.antichain hyY hCS hCY (by omega)
  have ezC := h4_z_edge_exact h.antichain hzZ hCS hCZ (by omega)
  rcases root_shape_below_last h.antichain hxC hYS (Ne.symm hCY) hbelow with hYu | hYl
  · rcases root_shape_below_last h.antichain hxC hZS (Ne.symm hCZ) hbelow with hZu | hZl
    · have hYy : Y.y = C.y - 1 := by
        simp [hYu.1, show ¬C.x + 1 < C.x by omega] at eyC
        omega
      have hYz : Y.z = C.z := by
        simp [hYu.1, show ¬C.x + 1 < C.x by omega] at eyC
        omega
      have hZy : Z.y = C.y := by
        simp [hZu.1, show ¬C.x + 1 < C.x by omega] at ezC
        omega
      have hZz : Z.z = C.z - 1 := by
        simp [hZu.1, show ¬C.x + 1 < C.x by omega] at ezC
        omega
      let T : Normal a b c := ⟨C.x + 1, C.y, C.z, by omega⟩
      have hxT : 0 < T.x := by simp [T]
      have hyT : 0 < T.y := by simp [T]; omega
      have hzT : 0 < T.z := by simp [T]; omega
      have hpredX : Normal.predecessor .x T = some C := by
        rw [Normal.predecessor_x_of_pos T hxT]
        congr 1
      have hpredY : Normal.predecessor .y T = some Y := by
        rw [Normal.predecessor_y_of_pos T hyT]
        congr 1
        apply Normal.ext <;> simp [Normal.yPredecessor, T, hYu.1, hYy, hYz]
      have hpredZ : Normal.predecessor .z T = some Z := by
        rw [Normal.predecessor_z_of_pos T hzT]
        congr 1
        apply Normal.ext <;> simp [Normal.zPredecessor, T, hZu.1, hZy, hZz]
      have hroots : predecessorRootFinset T = ({C, Y, Z} : Finset (Normal a b c)) := by
        ext q
        rw [mem_predecessorRootFinset_iff]
        simp [hpredX, hpredY, hpredZ, eq_comm]
      have hproper : ∀ q ∈ predecessorRootFinset T, ¬T ∣ q := by
        intro q hq hTq
        rw [hroots] at hq
        have hqmem : q = C ∨ q = Y ∨ q = Z := by simpa using hq
        have hd := (Normal.exact_divides_iff T q).1 hTq
        rcases hqmem with rfl | rfl | rfl <;>
          simp [Normal.DividesCriterion, T, hYu.1, hYy, hYz, hZu.1, hZy, hZz] at hd <;>
          omega
      apply BaseCoverShape.topDeletion
      refine ⟨T, ?_, hroots.symm, ?_⟩
      · simp [hCY, hCZ, hYZ]
      · rw [← hroots]
        exact standardSet_predecessorRootFinset T hproper
    · by_cases hCx : C.x = 0
      · have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ (by omega)
        simp [hYu.1, hZl.1, hCx] at eyC ezC ezY
        omega
      · have hCxPos : 0 < C.x := by omega
        simp [hZl.1, hCxPos] at ezC
        have hnw : ¬(b ≤ Z.y ∧ c ≤ Z.z) := hZl.2
        exact False.elim (hnw ⟨by omega, by omega⟩)
  · rcases root_shape_below_last h.antichain hxC hZS (Ne.symm hCZ) hbelow with hZu | hZl
    · by_cases hCx : C.x = 0
      · have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) (by omega)
        simp [hYl.1, hZu.1, hCx] at eyC ezC eyZ
        omega
      · have hCxPos : 0 < C.x := by omega
        simp [hYl.1, hCxPos] at eyC
        have hnw : ¬(b ≤ Y.y ∧ c ≤ Y.z) := hYl.2
        exact False.elim (hnw ⟨by omega, by omega⟩)
    · by_cases hCx : C.x = 0
      · have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) (by omega)
        have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ (by omega)
        simp [hYl.1, hZl.1, hCx] at eyC ezC eyZ ezY
        have hnYC : ¬Normal.DividesCriterion Y C := by
          intro hd
          exact (h.antichain Y hYS C hCS (Ne.symm hCY))
            ((Normal.exact_divides_iff Y C).2 hd)
        simp [Normal.DividesCriterion, hYl.1, hCx] at hnYC
        omega
      · have hCxPos : 0 < C.x := by omega
        simp [hYl.1, hZl.1, hCxPos] at eyC ezC
        exact False.elim (hYl.2 ⟨by omega, by omega⟩)

/-- The reflected I.b branch is obtained by the exact y/z equivalence, not by
duplicating the coordinate argument.-/
theorem mixed_below_reflected_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y C)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z P)
    (hbelow : C.x < a - 1) :
    CoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have hCP' : swapYZ C ≠ swapYZ P := by
    intro heq
    exact hCP (by have := congrArg swapYZ heq; simpa using this)
  have hCR' : swapYZ C ≠ swapYZ R := by
    intro heq
    exact hCR (by have := congrArg swapYZ heq; simpa using this)
  have hPR' : swapYZ P ≠ swapYZ R := by
    intro heq
    exact hPR (by have := congrArg swapYZ heq; simpa using this)
  have hs := coverHypotheses_swapYZ h hb hc
  rw [swapYZFinset_triple] at hs
  have hx := directionalCentre_swapYZ_x hxC
  have hy := directionalCentre_swapYZ_y hzP
  have hz := directionalCentre_swapYZ_z hyC
  rw [swapYZFinset_triple] at hx hy hz
  have hbase := mixed_below_direct_three (swapYZ C) (swapYZ P) (swapYZ R)
    hCP' hCR' hPR' hs hc hb hx hy hz (by simpa using hbelow)
  exact CoverShape.reflected hb hc (by
    rw [swapYZFinset_triple]
    exact hbase)

/-- Human II.a, direct orientation: a third root over the M4 core is exactly
the M4Y root.-/
theorem mixed_last_direct_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y P)
    (hzC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z C)
    (hlast : C.x = a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hCP) hlast
  have hxR := root_x_zero_at_last h.antichain hxC hRS (Ne.symm hCR) hlast
  have hPC : P.x < C.x := by omega
  have hRC : R.x < C.x := by omega
  have hCy : 0 < C.y := by
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨Q, hQS, htQ⟩
    have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b c) Q).1 htQ
    simp [liveTiePoint, Normal.DividesCriterion] at ht
    by_cases hQC : Q = C
    · subst Q
      omega
    · have hzQ := h4_z_edge_exact h.antichain hzC hQS hQC (by omega)
      omega
  have ey := h4_y_edge_exact h.antichain hyP hCS hCP hCy
  have hPz : 0 < P.z := by simp [hPC] at ey; omega
  have ez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) hPz
  have har := mixed_last_direct_m4_arithmetic hb hc
    (by simpa [hPC] using ey) (by simpa [show ¬C.x < P.x by omega] using ez)
  have hb1 : b = 1 := har.1
  have hc1 : c = 1 := har.2.1
  have hPy : P.y = C.y := har.2.2.1
  have hPzEq : P.z = C.z + 1 := har.2.2.2
  subst b; subst c
  have hnRP : ¬Normal.DividesCriterion R P := by
    intro hd
    exact (h.antichain R hRS P hPS (Ne.symm hPR))
      ((Normal.exact_divides_iff R P).2 hd)
  have hnPR : ¬Normal.DividesCriterion P R := by
    intro hd
    exact (h.antichain P hPS R hRS hPR)
      ((Normal.exact_divides_iff P R).2 hd)
  by_cases hRz : R.z = 0
  · have hRy : R.y = C.y + 1 := by
      by_cases hRy0 : R.y = 0
      · unfold Normal.DividesCriterion at hnRP
        omega
      · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hxR, hxP] at eRy
        omega
    have hC : C = m4YCore ha C.y C.z := by
      apply Normal.ext <;> simp [m4YCore, hlast]
    have hP : P = m4YPartner C.y C.z := by
      apply Normal.ext <;> simp [m4YPartner, hxP, hPy, hPzEq]
    have hR : R = m4YRoot C.y := by
      apply Normal.ext <;> simp [m4YRoot, hxR, hRy, hRz]
    have hS : ({C, P, R} : Finset (Normal a 1 1)) =
        m4YSocles ha C.y C.z := by
      rw [hC, hP, hR]
      rfl
    rw [hS]
    exact BaseCoverShape.m4Y ha (by omega)
  · have hRzp : 0 < R.z := by omega
    by_cases hRy0 : R.y = 0
    · have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) hRzp
      simp [hxR] at eRz
      unfold Normal.DividesCriterion at hnRP
      omega
    · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
      have eRz := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) hRzp
      simp [hxR, hxP] at eRy eRz
      omega

/-- Human II top-deletion branch: at the last x-layer, three distinct centres
are the wrapped-x, y, and z predecessors of one top.-/
theorem mixed_last_distinct_centres_top
    (C Y Z : Normal a b c) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .z Z)
    (hlast : C.x = a - 1) (hCyPos : 0 < C.y) (hCzPos : 0 < C.z) :
    BaseCoverShape ({C, Y, Z} : Finset (Normal a b c)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hZS : Z ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hxY := root_x_zero_at_last h.antichain hxC hYS (Ne.symm hCY) hlast
  have hxZ := root_x_zero_at_last h.antichain hxC hZS (Ne.symm hCZ) hlast
  have hYC : Y.x < C.x := by omega
  have hZC : Z.x < C.x := by omega
  have eyC := h4_y_edge_exact h.antichain hyY hCS hCY hCyPos
  have ezC := h4_z_edge_exact h.antichain hzZ hCS hCZ hCzPos
  have hYzPos : 0 < Y.z := by simp [hYC] at eyC; omega
  have hZyPos : 0 < Z.y := by simp [hZC] at ezC; omega
  have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ hYzPos
  have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) hZyPos
  have hYy : Y.y = C.y + b - 1 := by simp [hYC] at eyC; omega
  have hYz : Y.z = C.z + c := by
    have h1 := ezC.1
    have h2 := ezY.1
    simp [hZC] at h1
    simp [hxY, hxZ] at h2
    omega
  have hZy : Z.y = C.y + b := by
    have h1 := eyC.1
    have h2 := eyZ.1
    simp [hYC] at h1
    simp [hxY, hxZ] at h2
    omega
  have hZz : Z.z = C.z + c - 1 := by simp [hZC] at ezC; omega
  let T : Normal a b c := ⟨0, C.y + b, C.z + c, by
    exact Nat.pos_of_ne_zero (NeZero.ne a)⟩
  have hTx : T.x = 0 := rfl
  have hTy : b ≤ T.y := by simp [T]
  have hTz : c ≤ T.z := by simp [T]
  have hyT : 0 < T.y := by simp [T]; omega
  have hzT : 0 < T.z := by simp [T]; omega
  have hpredX : Normal.predecessor .x T = some C := by
    rw [Normal.predecessor_x_wrapped T hTx hTy hTz]
    congr 1
    apply Normal.ext <;> simp [Normal.wrappedXPredecessor, T, hlast]
  have hpredY : Normal.predecessor .y T = some Y := by
    rw [Normal.predecessor_y_of_pos T hyT]
    congr 1
    apply Normal.ext <;> simp [Normal.yPredecessor, T, hxY, hYy, hYz]
  have hpredZ : Normal.predecessor .z T = some Z := by
    rw [Normal.predecessor_z_of_pos T hzT]
    congr 1
    apply Normal.ext <;> simp [Normal.zPredecessor, T, hxZ, hZy, hZz]
  have hroots : predecessorRootFinset T = ({C, Y, Z} : Finset (Normal a b c)) := by
    ext q
    rw [mem_predecessorRootFinset_iff]
    simp [hpredX, hpredY, hpredZ, eq_comm]
  have hproper : ∀ q ∈ predecessorRootFinset T, ¬T ∣ q := by
    intro q hq hTq
    rw [hroots] at hq
    have hqmem : q = C ∨ q = Y ∨ q = Z := by simpa using hq
    have hd := (Normal.exact_divides_iff T q).1 hTq
    rcases hqmem with rfl | rfl | rfl <;>
      simp [Normal.DividesCriterion, T, hlast, hxY, hxZ, hYy, hYz, hZy, hZz] at hd <;>
      omega
  apply BaseCoverShape.topDeletion
  refine ⟨T, ?_, hroots.symm, ?_⟩
  · simp [hCY, hCZ, hYZ]
  · rw [← hroots]
    exact standardSet_predecessorRootFinset T hproper

/-- Human II.b distinct-centre branch with `C.y=0`.-/
theorem mixed_last_yzero_distinct_centres_top
    (C Y Z : Normal a b c) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .z Z)
    (hlast : C.x = a - 1) (hCy : C.y = 0) (hCz : 0 < C.z) :
    BaseCoverShape ({C, Y, Z} : Finset (Normal a b c)) := by
  have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hZS : Z ∈ ({C, Y, Z} : Finset (Normal a b c)) := by simp
  have hxY := root_x_zero_at_last h.antichain hxC hYS (Ne.symm hCY) hlast
  have hxZ := root_x_zero_at_last h.antichain hxC hZS (Ne.symm hCZ) hlast
  have hZC : Z.x < C.x := by have := h.a_ge_two; omega
  have ezC := h4_z_edge_exact h.antichain hzZ hCS hCZ hCz
  have hZz : Z.z = C.z + c - 1 := by simp [hZC] at ezC; omega
  have hZyLower : b ≤ Z.y := by simp [hZC, hCy] at ezC; omega
  have hZzLower : c ≤ Z.z := by omega
  have hxwZ := h4_x_edge_wrapped_exact h.antichain hxC hZS (Ne.symm hCZ)
    hxZ hZyLower hZzLower
  have hZy : Z.y = b := by omega
  have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) (by omega)
  have hYy : Y.y = b - 1 := by simp [hxY, hxZ, hZy] at eyZ; omega
  have hYzPos : 0 < Y.z := by simp [hxY, hxZ] at eyZ; omega
  have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ hYzPos
  have hYz : Y.z = C.z + c := by
    have h1 := ezY.1
    simp [hxY, hxZ, hZz] at h1
    omega
  let T : Normal a b c := ⟨0, b, C.z + c, by
    exact Nat.pos_of_ne_zero (NeZero.ne a)⟩
  have hTx : T.x = 0 := rfl
  have hTy : b ≤ T.y := by simp [T]
  have hTz : c ≤ T.z := by simp [T]
  have hyT : 0 < T.y := by simp [T]; omega
  have hzT : 0 < T.z := by simp [T]; omega
  have hpredX : Normal.predecessor .x T = some C := by
    rw [Normal.predecessor_x_wrapped T hTx hTy hTz]
    congr 1
    apply Normal.ext <;> simp [Normal.wrappedXPredecessor, T, hlast, hCy]
  have hpredY : Normal.predecessor .y T = some Y := by
    rw [Normal.predecessor_y_of_pos T hyT]
    congr 1
    apply Normal.ext <;> simp [Normal.yPredecessor, T, hxY, hYy, hYz]
  have hpredZ : Normal.predecessor .z T = some Z := by
    rw [Normal.predecessor_z_of_pos T hzT]
    congr 1
    apply Normal.ext <;> simp [Normal.zPredecessor, T, hxZ, hZy, hZz]
  have hroots : predecessorRootFinset T = ({C, Y, Z} : Finset (Normal a b c)) := by
    ext q
    rw [mem_predecessorRootFinset_iff]
    simp [hpredX, hpredY, hpredZ, eq_comm]
  have hproper : ∀ q ∈ predecessorRootFinset T, ¬T ∣ q := by
    intro q hq hTq
    rw [hroots] at hq
    have hqmem : q = C ∨ q = Y ∨ q = Z := by simpa using hq
    have hd := (Normal.exact_divides_iff T q).1 hTq
    rcases hqmem with rfl | rfl | rfl <;>
      simp [Normal.DividesCriterion, T, hlast, hCy, hxY, hxZ, hYy, hYz,
        hZy, hZz] at hd <;> omega
  apply BaseCoverShape.topDeletion
  refine ⟨T, ?_, hroots.symm, ?_⟩
  · simp [hCY, hCZ, hYZ]
  · rw [← hroots]
    exact standardSet_predecessorRootFinset T hproper

theorem mixed_last_zzero_distinct_centres_top
    (C Y Z : Normal a b c) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .z Z)
    (hlast : C.x = a - 1) (hCy : 0 < C.y) (hCz : C.z = 0) :
    CoverShape ({C, Y, Z} : Finset (Normal a b c)) := by
  have hCZ' : swapYZ C ≠ swapYZ Z := fun heq =>
    hCZ (by have := congrArg swapYZ heq; simpa using this)
  have hCY' : swapYZ C ≠ swapYZ Y := fun heq =>
    hCY (by have := congrArg swapYZ heq; simpa using this)
  have hZY' : swapYZ Z ≠ swapYZ Y := fun heq =>
    (Ne.symm hYZ) (by have := congrArg swapYZ heq; simpa using this)
  have hs := coverHypotheses_swapYZ h hb hc
  rw [swapYZFinset_triple] at hs
  have hx := directionalCentre_swapYZ_x hxC
  have hy := directionalCentre_swapYZ_y hzZ
  have hz := directionalCentre_swapYZ_z hyY
  rw [swapYZFinset_triple] at hx hy hz
  have hbase := mixed_last_yzero_distinct_centres_top
    (swapYZ C) (swapYZ Z) (swapYZ Y) hCZ' hCY' hZY'
    (by simpa [Finset.pair_comm] using hs) hc hb
    (by simpa [Finset.pair_comm] using hx)
    (by simpa [Finset.pair_comm] using hy)
    (by simpa [Finset.pair_comm] using hz)
    (by simpa using hlast) (by simpa using hCz) (by simpa using hCy)
  apply CoverShape.reflected hb hc
  rw [swapYZFinset_triple]
  simpa [Finset.pair_comm] using hbase

theorem mixed_last_reflected_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y C)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z P)
    (hlast : C.x = a - 1) :
    CoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have hCP' : swapYZ C ≠ swapYZ P := fun heq =>
    hCP (by have := congrArg swapYZ heq; simpa using this)
  have hCR' : swapYZ C ≠ swapYZ R := fun heq =>
    hCR (by have := congrArg swapYZ heq; simpa using this)
  have hPR' : swapYZ P ≠ swapYZ R := fun heq =>
    hPR (by have := congrArg swapYZ heq; simpa using this)
  have hs := coverHypotheses_swapYZ h hb hc
  rw [swapYZFinset_triple] at hs
  have hx := directionalCentre_swapYZ_x hxC
  have hy := directionalCentre_swapYZ_y hzP
  have hz := directionalCentre_swapYZ_z hyC
  rw [swapYZFinset_triple] at hx hy hz
  have hbase := mixed_last_direct_three (swapYZ C) (swapYZ P) (swapYZ R)
    hCP' hCR' hPR' hs hc hb hx hy hz (by simpa using hlast)
  exact CoverShape.reflected hb hc (by
    rw [swapYZFinset_triple]
    exact hbase)

/-- Human II.b, M5 orientation: when the common non-x centre is `P` and
`C.y=0`, the third root is exactly the Y- or Z-extension.-/
theorem mixed_last_common_yzero_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y P)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z P)
    (hlast : C.x = a - 1) (hCy : C.y = 0) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hCP) hlast
  have hxR := root_x_zero_at_last h.antichain hxC hRS (Ne.symm hCR) hlast
  have hPC : P.x < C.x := by omega
  have hCz : 0 < C.z := by
    by_contra hz0
    have hCz0 : C.z = 0 := by omega
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨Q, hQS, htQ⟩
    have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
    have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b c) Q).1 htQ
    simp [liveTiePoint, Normal.DividesCriterion] at ht
    rcases hQmem with hQC | hQP | hQR
    · subst Q
      omega
    · subst Q
      have hnCP : ¬Normal.DividesCriterion C P := by
        intro hd
        exact (h.antichain C hCS P hPS hCP) ((Normal.exact_divides_iff C P).2 hd)
      unfold Normal.DividesCriterion at hnCP
      omega
    · subst Q
      have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
      have eRz := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) (by omega)
      simp [hxR, hxP] at eRy eRz
      omega
  have ez := h4_z_edge_exact h.antichain hzP hCS hCP hCz
  have hPz : P.z = C.z + c - 1 := by simp [hPC] at ez; omega
  have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hCP)
    hxP (by simp [hPC, hCy] at ez; omega) (by omega)
  have hPy : P.y = b := by simp [hPC, hCy] at ez; omega
  have hnRP : ¬Normal.DividesCriterion R P := by
    intro hd
    exact (h.antichain R hRS P hPS (Ne.symm hPR))
      ((Normal.exact_divides_iff R P).2 hd)
  by_cases hRy0 : R.y = 0
  · have hRzp : 0 < R.z := by
      by_contra hz0
      have hnRC : ¬Normal.DividesCriterion R C := by
        intro hd
        exact (h.antichain R hRS C hCS (Ne.symm hCR))
          ((Normal.exact_divides_iff R C).2 hd)
      unfold Normal.DividesCriterion at hnRC
      omega
    have eRz := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) hRzp
    have hRz : R.z = C.z + c := by simp [hxR, hxP, hPz] at eRz; omega
    have hC : C = m5Core ha C.z := by
      apply Normal.ext <;> simp [m5Core, hlast, hCy]
    have hP : P = m5Partner C.z c := by
      apply Normal.ext <;> simp [m5Partner, hxP, hPy, hPz]
    have hR : R = m5ZRoot C.z c := by
      apply Normal.ext <;> simp [m5ZRoot, hxR, hRy0, hRz]
    have hS : ({C, P, R} : Finset (Normal a b c)) = m5ZSocles ha C.z := by
      rw [hC, hP, hR]
      rfl
    rw [hS]
    exact BaseCoverShape.m5Z ha hb hc hCz
  · by_cases hRz0 : R.z = 0
    · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
      have hRy : R.y = b + 1 := by simp [hxR, hxP, hPy] at eRy; omega
      have hC : C = m5Core ha C.z := by
        apply Normal.ext <;> simp [m5Core, hlast, hCy]
      have hP : P = m5Partner C.z c := by
        apply Normal.ext <;> simp [m5Partner, hxP, hPy, hPz]
      have hR : R = m5YRoot := by
        apply Normal.ext <;> simp [m5YRoot, hxR, hRy, hRz0]
      have hS : ({C, P, R} : Finset (Normal a b c)) = m5YSocles ha C.z := by
        rw [hC, hP, hR]
        rfl
      rw [hS]
      exact BaseCoverShape.m5Y ha hb hc hCz
    · have eRy := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
      have eRz := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) (by omega)
      simp [hxR, hxP] at eRy eRz
      omega

theorem mixed_last_common_zzero_three
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .y P)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .z P)
    (hlast : C.x = a - 1) (hCz : C.z = 0) :
    CoverShape ({C, P, R} : Finset (Normal a b c)) := by
  have hCP' : swapYZ C ≠ swapYZ P := fun heq =>
    hCP (by have := congrArg swapYZ heq; simpa using this)
  have hCR' : swapYZ C ≠ swapYZ R := fun heq =>
    hCR (by have := congrArg swapYZ heq; simpa using this)
  have hPR' : swapYZ P ≠ swapYZ R := fun heq =>
    hPR (by have := congrArg swapYZ heq; simpa using this)
  have hs := coverHypotheses_swapYZ h hb hc
  rw [swapYZFinset_triple] at hs
  have hx := directionalCentre_swapYZ_x hxC
  have hy := directionalCentre_swapYZ_y hzP
  have hz := directionalCentre_swapYZ_z hyP
  rw [swapYZFinset_triple] at hx hy hz
  have hbase := mixed_last_common_yzero_three
    (swapYZ C) (swapYZ P) (swapYZ R) hCP' hCR' hPR' hs hc hb hx hy hz
      (by simpa using hlast) (by simpa using hCz)
  exact CoverShape.reflected hb hc (by
    rw [swapYZFinset_triple]
    exact hbase)

/-- In the pure case, zero-z x- and y-centres force every positive-z root to
be the same pure z-power.  This is the common fibre-product argument used in
human cases I.d and II.e.-/
theorem pure_fibre_of_zero_z_centres
    {S : Finset (Normal a b 0)} (C Y : Normal a b 0)
    (h : CoverHypotheses S)
    (hxC : IsDirectionalCentre S .x C) (hyY : IsDirectionalCentre S .y Y)
    (hCz : C.z = 0) (hYz : Y.z = 0) : IsPureFibreProduct S := by
  have purePower {Q : Normal a b 0} (hQS : Q ∈ S) (hQz : 0 < Q.z) :
      Q.x = 0 ∧ Q.y = 0 := by
    have hQC : Q ≠ C := by intro heq; subst Q; omega
    have hQx : Q.x = 0 := by
      by_cases hlast : C.x = a - 1
      · exact root_x_zero_at_last h.antichain hxC hQS hQC hlast
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        rcases root_shape_below_last h.antichain hxC hQS hQC hbelow with hQu | hQl
        · omega
        · exact hQl.1
    have hQY : Q ≠ Y := by intro heq; subst Q; omega
    have hQy : Q.y = 0 := by
      by_contra hqy
      have ey := h4_y_edge_exact h.antichain hyY hQS hQY (by omega)
      simp [hYz] at ey
      omega
    exact ⟨hQx, hQy⟩
  rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
    ⟨Z, hZS, hzZ⟩
  have hZz := (Normal.zGenerator_dvd_iff Z).1 hzZ
  have hZpure := purePower hZS hZz
  have hEq : (⟨0, 0, Z.z, Nat.pos_of_ne_zero (NeZero.ne a)⟩ : Normal a b 0) = Z := by
    apply Normal.ext <;> simp [hZpure.1, hZpure.2]
  refine ⟨rfl, Z.z, hZz, ?_, ?_⟩
  · simpa [hEq] using hZS
  · intro R hRS hRZ
    have hRZ' : R ≠ Z := by simpa [hEq] using hRZ
    by_contra hRz0
    have hRz : 0 < R.z := by omega
    have hRpure := purePower hRS hRz
    by_cases hle : R.z ≤ Z.z
    · have hd : R ∣ Z := (Normal.exact_divides_iff R Z).2 (by
        simp [Normal.DividesCriterion, hRpure.1, hRpure.2, hZpure.1, hZpure.2]
        omega)
      exact h.antichain R hRS Z hZS hRZ' hd
    · have hd : Z ∣ R := (Normal.exact_divides_iff Z R).2 (by
        simp [Normal.DividesCriterion, hRpure.1, hRpure.2, hZpure.1, hZpure.2]
        omega)
      exact h.antichain Z hZS R hRS (Ne.symm hRZ') hd

/-- Human I.c--d: below the last layer the direct pure branch is either the
fibre-product zero-z case, or its positive-z P3 core admits no third root.-/
theorem pure_below_direct_three
    (C P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
    (hzC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z C)
    (hbelow : C.x < a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have ey := h4_y_edge_exact h.antichain hyP hCS hCP (by omega)
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hCP) hbelow with hPu | hPl
  · have hnPC : ¬Normal.DividesCriterion P C := by
      intro hd
      exact (h.antichain P hPS C hCS (Ne.symm hCP))
        ((Normal.exact_divides_iff P C).2 hd)
    have hPz : P.z = C.z := by
      simp [Normal.DividesCriterion, hPu.1] at hnPC
      omega
    by_cases hCz0 : C.z = 0
    · have hPz0 : P.z = 0 := by omega
      rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
        ⟨Q, hQS, hzQ⟩
      have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
      have hQz := (Normal.zGenerator_dvd_iff Q).1 hzQ
      have hRz : 0 < R.z := by
        rcases hQmem with hQC | hQP | hQR
        · rw [hQC] at hQz
          omega
        · rw [hQP] at hQz
          omega
        · simpa [hQR] using hQz
      have hRx : R.x = 0 := by
        rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
        · omega
        · exact hRl.1
      have hRy : R.y = 0 := by
        by_contra hry
        have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRx, hPu.1, hPz0] at eyR
        omega
      refine BaseCoverShape.pureFibreProduct ?_
      refine ⟨rfl, R.z, hRz, ?_, ?_⟩
      · have hZR : (⟨0, 0, R.z, by omega⟩ : Normal a b 0) = R := by
          apply Normal.ext <;> simp [hRx, hRy]
        simp [hZR]
      · intro Q hQS hQR
        have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
        rcases hQmem with rfl | rfl | rfl
        · exact hCz0
        · exact hPz0
        · exact False.elim (hQR (by apply Normal.ext <;> simp [hRx, hRy]))
    · have ez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) (by omega)
      simp [hPu.1, hPz] at ez
  · have hPx0 : P.x = 0 := by
      by_cases hr : 0 < C.x <;> simp [hPl.1, hr] at ey <;> omega
    have hnw : ¬b ≤ P.y := by simpa [hPx0] using hPl.2
    have har := pure_below_lower_direct_arithmetic hb hbnd.1 hnw
      (by simpa [hPl.1] using ey)
      (by
        have hPz : 0 < P.z := by
          by_contra hpz
          have hnPC : ¬Normal.DividesCriterion P C := by
            intro hd
            exact (h.antichain P hPS C hCS (Ne.symm hCP))
              ((Normal.exact_divides_iff P C).2 hd)
          simp [Normal.DividesCriterion, hPx0] at hnPC
          omega
        simpa [hPl.1] using
          h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) hPz)
    have hCx : C.x = 0 := har.1
    have hCy : C.y = b := har.2.1
    have hPy : P.y = b - 1 := har.2.2.1
    have hPz : P.z = C.z + 1 := har.2.2.2
    have hnRC : ¬Normal.DividesCriterion R C := by
      intro hd
      exact (h.antichain R hRS C hCS (Ne.symm hCR))
        ((Normal.exact_divides_iff R C).2 hd)
    have hnRP : ¬Normal.DividesCriterion R P := by
      intro hd
      exact (h.antichain R hRS P hPS (Ne.symm hPR))
        ((Normal.exact_divides_iff R P).2 hd)
    exfalso
    rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
    · by_cases hRy0 : R.y = 0
      · by_cases hRz0 : R.z = 0
        · simp [Normal.DividesCriterion, hCx, hCy, hRu.1, hRy0, hRz0] at hnRC
        · have ezR := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
          simp [hRu.1, hCx] at ezR
          omega
      · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRu.1, hPx0, hPy] at eyR
        omega
    · by_cases hRy0 : R.y = 0
      · by_cases hRz0 : R.z = 0
        · simp [Normal.DividesCriterion, hCx, hCy, hRl.1, hRy0, hRz0] at hnRC
        · have ezR := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
          simp [hRl.1, hCx] at ezR
          simp [Normal.DividesCriterion, hPx0, hPy, hPz, hRl.1, hRy0] at hnRP
          omega
      · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hRl.1, hPx0, hPy] at eyR
        have hnwR := hRl.2
        simp at hnwR
        omega

/-- Human II.d--e: at the last x-layer the direct pure branch is P5Z when
`C.z>0`, and the zero-z branch is the pure fibre-product shape.-/
theorem pure_last_direct_three
    (C P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
    (hzC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z C)
    (hlast : C.x = a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hCP) hlast
  have hxR := root_x_zero_at_last h.antichain hxC hRS (Ne.symm hCR) hlast
  by_cases hCy0 : C.y = 0
  · have hCz : 0 < C.z := by
      by_contra hcz
      have hCz0 : C.z = 0 := by omega
      rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
        ⟨Q, hQS, htQ⟩
      have hQC : Q ≠ C := by
        intro heq
        subst Q
        have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1 htQ
        simp [liveTiePoint, Normal.DividesCriterion, hCy0] at ht
        omega
      have hxQ := root_x_zero_at_last h.antichain hxC hQS hQC hlast
      have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) Q).1 htQ
      have hQy : b ≤ Q.y := by
        simp [liveTiePoint, Normal.DividesCriterion] at ht
        omega
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hQS hQC hxQ
        hQy
        (by simp)
      have hQz : Q.z = 0 := by omega
      have hQyEq : Q.y = b := by omega
      have hCQ : Normal.DividesCriterion C Q := by
        simp [Normal.DividesCriterion, hCy0, hCz0, hQz, hQyEq]
      exact (h.antichain C hCS Q hQS (Ne.symm hQC))
        ((Normal.exact_divides_iff C Q).2 hCQ)
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨Q, hQS, htQ⟩
    have hQC : Q ≠ C := by
      intro heq
      subst Q
      have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1 htQ
      simp [liveTiePoint, Normal.DividesCriterion, hCy0] at ht
      omega
    have hxQ := root_x_zero_at_last h.antichain hxC hQS hQC hlast
    have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) Q).1 htQ
    have hQy : b ≤ Q.y := by
      simp [liveTiePoint, Normal.DividesCriterion] at ht
      omega
    have hxw := h4_x_edge_wrapped_exact h.antichain hxC hQS hQC hxQ hQy (by simp)
    have hQz0 : Q.z = 0 := by
      by_contra hqz
      have ezQ := h4_z_edge_exact h.antichain hzC hQS hQC (by omega)
      simp [hxQ, hlast] at ezQ
      omega
    have hQyEq : Q.y = b := by omega
    have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
    have hQP : Q = P := by
      rcases hQmem with hQCeq | hQP | hQR
      · exact False.elim (hQC hQCeq)
      · exact hQP
      · exfalso
        rw [hQR] at hQyEq hQz0
        have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        have hPC : P.x < C.x := by omega
        have hPyPos : 0 < P.y := by
          simp [hxP, hxR] at eyR
          omega
        have hPz0 : P.z = 0 := by
          by_contra hpz
          have ezP := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) (by omega)
          simp [hPC, show ¬C.x < P.x by omega, hCy0] at ezP
          omega
        have hnPR : ¬Normal.DividesCriterion P R := by
          intro hd
          exact (h.antichain P hPS R hRS hPR)
            ((Normal.exact_divides_iff P R).2 hd)
        simp [hxP, hxR] at eyR
        simp [Normal.DividesCriterion, hxP, hxR, hPz0, hQz0] at hnPR
        omega
    have hPy : P.y = b := by rw [← hQP]; exact hQyEq
    have hPz : P.z = 0 := by rw [← hQP]; exact hQz0
    have hRz : R.z = C.z + 1 := by
      by_cases hrz : R.z = 0
      · by_cases hry : R.y = 0
        · have hnRP : ¬Normal.DividesCriterion R P := by
            intro hd
            exact (h.antichain R hRS P hPS (Ne.symm hPR))
              ((Normal.exact_divides_iff R P).2 hd)
          simp [Normal.DividesCriterion, hxR, hxP, hry, hrz, hPy, hPz] at hnRP
        · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          have hnPR : ¬Normal.DividesCriterion P R := by
            intro hd
            exact (h.antichain P hPS R hRS hPR)
              ((Normal.exact_divides_iff P R).2 hd)
          simp [hxR, hxP, hPy, hPz, hrz, hry] at eyR
          exfalso
          apply hnPR
          simp [Normal.DividesCriterion, hxR, hxP, hPy, hPz, hrz]
          omega
      · have ezR := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
        simp [hxR, hlast] at ezR
        omega
    have hRy : R.y = 0 := by
      have ezR := h4_z_edge_exact h.antichain hzC hRS (Ne.symm hCR) (by omega)
      simp [hxR, hlast] at ezR
      omega
    have hC : C = (⟨a - 1, 0, C.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hlast, hCy0]
    have hP : P = (⟨0, b, 0, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hxP, hPy, hPz]
    have hR : R = (⟨0, 0, C.z + 1, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hxR, hRy, hRz]
    have hS : ({C, P, R} : Finset (Normal a b 0)) = p5ZSocles ha C.z := by
      rw [hC, hP, hR]
      rfl
    rw [hS]
    exact BaseCoverShape.p5Z ha hb hCz
  · have hCy : 0 < C.y := by omega
    have ey := h4_y_edge_exact h.antichain hyP hCS hCP hCy
    have hPC : P.x < C.x := by omega
    have hPz0 : P.z = 0 := by
      by_contra hpz
      have ez := h4_z_edge_exact h.antichain hzC hPS (Ne.symm hCP) (by omega)
      simp [hPC, show ¬C.x < P.x by omega] at ey ez
      omega
    have hCz0 : C.z = 0 := by omega
    exact BaseCoverShape.pureFibreProduct
      (pure_fibre_of_zero_z_centres C P h hxC hyP hCz0 hPz0)

/-- The pure orientation with the x-centre also serving as y-centre is always
the fibre-product branch; a positive `C.z` would force `b = 1`.-/
theorem pure_reflected_three
    (C Z R : Normal a b 0) (hCZ : C ≠ Z) (hCR : C ≠ R) (hZR : Z ≠ R)
    (h : CoverHypotheses ({C, Z, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, Z, R} : Finset (Normal a b 0)) .x C)
    (hyC : IsDirectionalCentre ({C, Z, R} : Finset (Normal a b 0)) .y C)
    (hzZ : IsDirectionalCentre ({C, Z, R} : Finset (Normal a b 0)) .z Z) :
    BaseCoverShape ({C, Z, R} : Finset (Normal a b 0)) := by
  have hCS : C ∈ ({C, Z, R} : Finset (Normal a b 0)) := by simp
  by_cases hCz0 : C.z = 0
  · exact BaseCoverShape.pureFibreProduct
      (pure_fibre_of_zero_z_centres C C h hxC hyC hCz0 hCz0)
  · have hCz : 0 < C.z := by omega
    have ez := h4_z_edge_exact h.antichain hzZ hCS hCZ hCz
    have hZS : Z ∈ ({C, Z, R} : Finset (Normal a b 0)) := by simp
    have hZy : 0 < Z.y := by
      by_cases hlast : C.x = a - 1
      · have hxZ := root_x_zero_at_last h.antichain hxC hZS (Ne.symm hCZ) hlast
        have hZC : Z.x < C.x := by have := h.a_ge_two; omega
        simp [hZC] at ez
        omega
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        have hbnd := below_last_live_bounds h hxC hbelow
        rcases root_shape_below_last h.antichain hxC hZS (Ne.symm hCZ) hbelow with hZu | hZl
        · simp [hZu.1] at ez
          omega
        · by_cases hCx0 : C.x = 0
          · have hnw := hZl.2
            simp [hZl.1, hCx0] at ez hnw
            omega
          · simp [hZl.1, show Z.x < C.x by omega] at ez
            omega
    have ey := h4_y_edge_exact h.antichain hyC hZS (Ne.symm hCZ) hZy
    have hxne : Z.x ≠ C.x := by
      intro hxeq
      by_cases hlast : C.x = a - 1
      · have hxZ := root_x_zero_at_last h.antichain hxC hZS (Ne.symm hCZ) hlast
        have := h.a_ge_two
        omega
      · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
        have hbnd := below_last_live_bounds h hxC hbelow
        rcases root_shape_below_last h.antichain hxC hZS (Ne.symm hCZ) hbelow with hZu | hZl
        · omega
        · have hnw := hZl.2
          simp [hZl.1, hxeq] at ez hnw
          omega
    by_cases hZC : Z.x < C.x <;> by_cases hCZx : C.x < Z.x <;>
      simp [hZC, hCZx] at ey ez <;> omega

/-- Human II.d--e: a common non-x centre at the last layer is either the
zero-z fibre-product branch or the two-root P6 core; the latter cannot have a
third distinct root.-/
theorem pure_last_common_three
    (C P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z P)
    (hlast : C.x = a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hxP := root_x_zero_at_last h.antichain hxC hPS (Ne.symm hCP) hlast
  have hxR := root_x_zero_at_last h.antichain hxC hRS (Ne.symm hCR) hlast
  have hPC : P.x < C.x := by have := h.a_ge_two; omega
  by_cases hCz0 : C.z = 0
  · have hCy : 0 < C.y := by
      by_contra hcy
      have hCy0 : C.y = 0 := by omega
      rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
        ⟨Q, hQS, htQ⟩
      have hQC : Q ≠ C := by
        intro heq
        subst Q
        have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1 htQ
        simp [liveTiePoint, Normal.DividesCriterion, hCy0] at ht
        omega
      have hxQ := root_x_zero_at_last h.antichain hxC hQS hQC hlast
      have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) Q).1 htQ
      simp [liveTiePoint, Normal.DividesCriterion] at ht
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hQS hQC hxQ
        (by omega) (by simp)
      have hCQ : Normal.DividesCriterion C Q := by
        simp [Normal.DividesCriterion, hCy0, hCz0]
        omega
      exact (h.antichain C hCS Q hQS (Ne.symm hQC))
        ((Normal.exact_divides_iff C Q).2 hCQ)
    have ey := h4_y_edge_exact h.antichain hyP hCS hCP hCy
    have hPy : P.y = C.y + b - 1 := by simp [hPC] at ey; omega
    have hPz0 : P.z = 0 := by
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hCP)
        hxP (by omega) (by simp)
      omega
    exact BaseCoverShape.pureFibreProduct
      (pure_fibre_of_zero_z_centres C P h hxC hyP hCz0 hPz0)
  · have hCz : 0 < C.z := by omega
    by_cases hCy0 : C.y = 0
    · have ez := h4_z_edge_exact h.antichain hzP hCS hCP hCz
      have hPyLower : b ≤ P.y := by simp [hPC, hCy0] at ez; omega
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hPS (Ne.symm hCP)
        hxP hPyLower (by simp)
      have hPy : P.y = b := by omega
      have hPz : P.z = C.z - 1 := by simp [hPC] at ez; omega
      by_cases hRz0 : R.z = 0
      · by_cases hRy0 : R.y = 0
        · have hnRC : ¬Normal.DividesCriterion R C := by
            intro hd
            exact (h.antichain R hRS C hCS (Ne.symm hCR))
              ((Normal.exact_divides_iff R C).2 hd)
          simp [Normal.DividesCriterion, hxR, hRy0, hRz0, hCy0] at hnRC
        · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          simp [hxR, hxP, hPy] at eyR
          have hxw := h4_x_edge_wrapped_exact h.antichain hxC hRS (Ne.symm hCR)
            hxR (by omega) (by simp)
          omega
      · have ezR := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) (by omega)
        have hRz : R.z = C.z := by simp [hxR, hxP, hPz] at ezR; omega
        have hRy0 : R.y = 0 := by
          by_contra hry
          have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          simp [hxR, hxP, hPy] at eyR ezR
          omega
        have hnRC : ¬Normal.DividesCriterion R C := by
          intro hd
          exact (h.antichain R hRS C hCS (Ne.symm hCR))
            ((Normal.exact_divides_iff R C).2 hd)
        simp [Normal.DividesCriterion, hxR, hRy0, hRz, hCy0] at hnRC
    · have hCy : 0 < C.y := by omega
      have ey := h4_y_edge_exact h.antichain hyP hCS hCP hCy
      have ez := h4_z_edge_exact h.antichain hzP hCS hCP hCz
      simp [hPC] at ey ez
      omega

/-- Pure II.d with three distinct centres and `C.y=0`: the roots are the
three predecessors of `T=(0,b,C.z)`.-/
theorem pure_last_yzero_distinct_top
    (C Y Z : Normal a b 0) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .z Z)
    (hlast : C.x = a - 1) (hCy : C.y = 0) (hCz : 0 < C.z) :
    BaseCoverShape ({C, Y, Z} : Finset (Normal a b 0)) := by
  have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
  have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
  have hZS : Z ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
  have hxY := root_x_zero_at_last h.antichain hxC hYS (Ne.symm hCY) hlast
  have hxZ := root_x_zero_at_last h.antichain hxC hZS (Ne.symm hCZ) hlast
  have hZC : Z.x < C.x := by have := h.a_ge_two; omega
  have ezC := h4_z_edge_exact h.antichain hzZ hCS hCZ hCz
  have hZz : Z.z = C.z - 1 := by simp [hZC] at ezC; omega
  have hZyLower : b ≤ Z.y := by simp [hZC, hCy] at ezC; omega
  have hxwZ := h4_x_edge_wrapped_exact h.antichain hxC hZS (Ne.symm hCZ)
    hxZ hZyLower (by simp)
  have hZy : Z.y = b := by omega
  have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) (by omega)
  have hYy : Y.y = b - 1 := by simp [hxY, hxZ, hZy] at eyZ; omega
  have hYzPos : 0 < Y.z := by
    by_contra hyz
    have hnYZ : ¬Normal.DividesCriterion Y Z := by
      intro hd
      exact (h.antichain Y hYS Z hZS hYZ)
        ((Normal.exact_divides_iff Y Z).2 hd)
    simp [Normal.DividesCriterion, hxY, hxZ, hYy, hZy] at hnYZ eyZ
    omega
  have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ hYzPos
  have hYz : Y.z = C.z := by simp [hxY, hxZ, hZz] at ezY; omega
  let T : Normal a b 0 := ⟨0, b, C.z, Nat.pos_of_ne_zero (NeZero.ne a)⟩
  have hpredX : Normal.predecessor .x T = some C := by
    rw [Normal.predecessor_x_wrapped T (by rfl) (by simp [T]) (by simp [T])]
    congr 1
    apply Normal.ext <;> simp [Normal.wrappedXPredecessor, T, hlast, hCy]
  have hpredY : Normal.predecessor .y T = some Y := by
    rw [Normal.predecessor_y_of_pos T (by simp [T]; omega)]
    congr 1
    apply Normal.ext <;> simp [Normal.yPredecessor, T, hxY, hYy, hYz]
  have hpredZ : Normal.predecessor .z T = some Z := by
    rw [Normal.predecessor_z_of_pos T (by simp [T]; omega)]
    congr 1
    apply Normal.ext <;> simp [Normal.zPredecessor, T, hxZ, hZy, hZz]
  have hroots : predecessorRootFinset T = ({C, Y, Z} : Finset (Normal a b 0)) := by
    ext q
    rw [mem_predecessorRootFinset_iff]
    simp [hpredX, hpredY, hpredZ, eq_comm]
  have hproper : ∀ q ∈ predecessorRootFinset T, ¬T ∣ q := by
    intro q hq hTq
    rw [hroots] at hq
    have hqmem : q = C ∨ q = Y ∨ q = Z := by simpa using hq
    have hd := (Normal.exact_divides_iff T q).1 hTq
    rcases hqmem with rfl | rfl | rfl <;>
      simp [Normal.DividesCriterion, T, hlast, hCy, hxY, hxZ, hYy, hYz,
        hZy, hZz] at hd <;> omega
  apply BaseCoverShape.topDeletion
  refine ⟨T, ?_, hroots.symm, ?_⟩
  · simp [hCY, hCZ, hYZ]
  · rw [← hroots]
    exact standardSet_predecessorRootFinset T hproper

/-- The complete pure three-centre branch: positive `C.z` gives top deletion;
zero `C.z` gives the fibre-product shape.-/
theorem pure_distinct_three
    (C Y Z : Normal a b 0) (hCY : C ≠ Y) (hCZ : C ≠ Z) (hYZ : Y ≠ Z)
    (h : CoverHypotheses ({C, Y, Z} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .x C)
    (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .y Y)
    (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b 0)) .z Z) :
    BaseCoverShape ({C, Y, Z} : Finset (Normal a b 0)) := by
  by_cases hlast : C.x = a - 1
  · by_cases hCz0 : C.z = 0
    · have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
      have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
      have hxY := root_x_zero_at_last h.antichain hxC hYS (Ne.symm hCY) hlast
      have hCy : 0 < C.y := by
        by_contra hcy
        have hCy0 : C.y = 0 := by omega
        rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
          ⟨Q, hQS, htQ⟩
        have hQC : Q ≠ C := by
          intro heq
          subst Q
          have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) C).1 htQ
          simp [liveTiePoint, Normal.DividesCriterion, hCy0] at ht
          omega
        have hxQ := root_x_zero_at_last h.antichain hxC hQS hQC hlast
        have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b 0) Q).1 htQ
        simp [liveTiePoint, Normal.DividesCriterion] at ht
        have hxw := h4_x_edge_wrapped_exact h.antichain hxC hQS hQC hxQ
          (by omega) (by simp)
        have hCQ : Normal.DividesCriterion C Q := by
          simp [Normal.DividesCriterion, hCy0, hCz0]
          omega
        exact (h.antichain C hCS Q hQS (Ne.symm hQC))
          ((Normal.exact_divides_iff C Q).2 hCQ)
      have ey := h4_y_edge_exact h.antichain hyY hCS hCY hCy
      have hYyLower : b ≤ Y.y := by
        have hYC : Y.x < C.x := by have := h.a_ge_two; omega
        simp [hYC] at ey
        omega
      have hxw := h4_x_edge_wrapped_exact h.antichain hxC hYS (Ne.symm hCY)
        hxY hYyLower (by simp)
      have hYz0 : Y.z = 0 := by omega
      exact BaseCoverShape.pureFibreProduct
        (pure_fibre_of_zero_z_centres C Y h hxC hyY hCz0 hYz0)
    · have hCz : 0 < C.z := by omega
      by_cases hCy0 : C.y = 0
      · exact pure_last_yzero_distinct_top C Y Z hCY hCZ hYZ h hb hxC hyY hzZ
          hlast hCy0 hCz
      · exact mixed_last_distinct_centres_top C Y Z hCY hCZ hYZ h (by omega)
          (by omega) hxC hyY hzZ hlast (by omega) hCz
  · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
    have hbnd := below_last_live_bounds h hxC hbelow
    by_cases hCz0 : C.z = 0
    · have hCS : C ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
      have hYS : Y ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
      have ey := h4_y_edge_exact h.antichain hyY hCS hCY (by omega)
      rcases root_shape_below_last h.antichain hxC hYS (Ne.symm hCY) hbelow with hYu | hYl
      · have hnYC : ¬Normal.DividesCriterion Y C := by
          intro hd
          exact (h.antichain Y hYS C hCS (Ne.symm hCY))
            ((Normal.exact_divides_iff Y C).2 hd)
        have hYz0 : Y.z = 0 := by
          simp [Normal.DividesCriterion, hYu.1] at hnYC ey
          omega
        exact BaseCoverShape.pureFibreProduct
          (pure_fibre_of_zero_z_centres C Y h hxC hyY hCz0 hYz0)
      · have hCx0 : C.x = 0 := by
          by_contra hcx
          have hCxPos : 0 < C.x := by omega
          simp [hYl.1, hCxPos] at ey
          exact False.elim (hYl.2 ⟨by omega, by simp⟩)
        have hYy : Y.y = b - 1 := by simp [hYl.1, hCx0] at ey; omega
        by_cases hYz0 : Y.z = 0
        · exact BaseCoverShape.pureFibreProduct
            (pure_fibre_of_zero_z_centres C Y h hxC hyY hCz0 hYz0)
        · have hYz : 0 < Y.z := by omega
          have hZS : Z ∈ ({C, Y, Z} : Finset (Normal a b 0)) := by simp
          have ezY := h4_z_edge_exact h.antichain hzZ hYS hYZ hYz
          rcases root_shape_below_last h.antichain hxC hZS (Ne.symm hCZ) hbelow with hZu | hZl
          · have hZz0 : Z.z = 0 := by omega
            have hZy : 0 < Z.y := by simp [hZu.1, hYl.1] at ezY; omega
            have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) hZy
            simp [hZu.1, hYl.1, hYy, hZz0] at eyZ ezY
            omega
          · have hZy : 0 < Z.y := by simp [hZl.1, hYl.1] at ezY; omega
            have eyZ := h4_y_edge_exact h.antichain hyY hZS (Ne.symm hYZ) hZy
            have hnw := hZl.2
            simp [hZl.1, hYl.1, hYy] at eyZ ezY hnw
            omega
    · exact mixed_below_distinct_centres_top C Y Z hCY hCZ hYZ h (by omega)
        (by omega) hxC hyY hzZ hbelow (by omega) (by omega)

/-- Human I.d: the pure below-last common-centre triple is exactly P4Z.-/
theorem pure_below_common_three
    (C P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
    (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
    (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z P)
    (hbelow : C.x < a - 1) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
  have ha := h.a_ge_two
  have hCS : C ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hPS : P ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hRS : R ∈ ({C, P, R} : Finset (Normal a b 0)) := by simp
  have hbnd := below_last_live_bounds h hxC hbelow
  have ey := h4_y_edge_exact h.antichain hyP hCS hCP (by omega)
  rcases root_shape_below_last h.antichain hxC hPS (Ne.symm hCP) hbelow with hPu | hPl
  · have hCz0 : C.z = 0 := by
      by_contra hz0
      have ez := h4_z_edge_exact h.antichain hzP hCS hCP (by omega)
      simp [hPu.1] at ey ez
      omega
    have hPz0 : P.z = 0 := by omega
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.1 with
      ⟨Q, hQS, hzQ⟩
    have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
    rcases hQmem with hQC | hQP | hQR
    · subst Q
      exact False.elim (by have := (Normal.zGenerator_dvd_iff C).1 hzQ; omega)
    · subst Q
      exact False.elim (by have := (Normal.zGenerator_dvd_iff P).1 hzQ; omega)
    · subst Q
      have hRz := (Normal.zGenerator_dvd_iff R).1 hzQ
      have ezR := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) hRz
      have hRx0 : R.x = 0 := by
        rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
        · omega
        · exact hRl.1
      by_cases hRy0 : R.y = 0
      · refine BaseCoverShape.pureFibreProduct ?_
        refine ⟨rfl, R.z, hRz, ?_, ?_⟩
        · have hReq :
              (⟨0, 0, R.z, by omega⟩ : Normal a b 0) = R := by
              apply Normal.ext <;> simp [hRx0, hRy0]
          simpa [hReq]
        · intro Q hQS hQne
          have hQmem : Q = C ∨ Q = P ∨ Q = R := by simpa using hQS
          rcases hQmem with rfl | rfl | rfl
          · exact hCz0
          · exact hPz0
          · exact False.elim (hQne (by apply Normal.ext <;> simp [hRx0, hRy0]))
      · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
        simp [hPu.1, hRx0, hPz0] at ey eyR ezR
        omega
  · have hPx0 : P.x = 0 := by
      by_cases hr : 0 < C.x <;> simp [hPl.1, hr] at ey <;> omega
    have hnw : ¬b ≤ P.y := by simpa [hPx0] using hPl.2
    have hCx0 : C.x = 0 := by
      by_contra hc0
      have hCyB : b ≤ C.y := hbnd.1
      have hCxPos : 0 < C.x := by omega
      simp [hPx0, hCxPos] at ey
      omega
    have hCy : C.y = b := by
      simp [hPx0, hCx0] at ey
      omega
    have hPy : P.y = b - 1 := by simp [hPx0, hCx0] at ey; omega
    have hCz0 : C.z = 0 := by
      by_contra hz0
      have ez := h4_z_edge_exact h.antichain hzP hCS hCP (by omega)
      simp [hPx0, hCx0] at ez ey
      omega
    have hPzp : 0 < P.z := by
      by_contra hp0
      have hnPC : ¬Normal.DividesCriterion P C := by
        intro hd
        exact (h.antichain P hPS C hCS hCP.symm)
          ((Normal.exact_divides_iff P C).2 hd)
      simp [Normal.DividesCriterion, hPx0, hCx0, hCy, hPy, hCz0] at hnPC
      omega
    have hRzp : 0 < R.z := by
      by_contra hr0
      rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
      · by_cases hRy0 : R.y = 0
        · have hnRC : ¬Normal.DividesCriterion R C := by
            intro hd
            exact (h.antichain R hRS C hCS (Ne.symm hCR))
              ((Normal.exact_divides_iff R C).2 hd)
          simp [Normal.DividesCriterion, hRy0, hCz0] at hnRC
          omega
        · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          simp [hRu.1, hPx0, hPy] at eyR
          omega
      · by_cases hRy0 : R.y = 0
        · have hnRC : ¬Normal.DividesCriterion R C := by
            intro hd
            exact (h.antichain R hRS C hCS (Ne.symm hCR))
              ((Normal.exact_divides_iff R C).2 hd)
          simp [Normal.DividesCriterion, hRl.1, hRy0, hCz0] at hnRC
          omega
        · have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
          simp [hRl.1, hPx0, hPy] at eyR
          have hnRC : ¬Normal.DividesCriterion R C := by
            intro hd
            exact (h.antichain R hRS C hCS (Ne.symm hCR))
              ((Normal.exact_divides_iff R C).2 hd)
          simp [Normal.DividesCriterion, hRl.1, hCx0, hCy, hCz0] at hnRC
          omega
    have ezR := h4_z_edge_exact h.antichain hzP hRS (Ne.symm hPR) hRzp
    have hRx0 : R.x = 0 := by
      rcases root_shape_below_last h.antichain hxC hRS (Ne.symm hCR) hbelow with hRu | hRl
      · by_contra hrx
        simp [hRu.1, hPx0, hPy] at ezR
        omega
      · exact hRl.1
    have hRz : R.z = P.z + 1 := by simp [hRx0, hPx0] at ezR; omega
    have hRy0 : R.y = 0 := by
      by_contra hry
      have eyR := h4_y_edge_exact h.antichain hyP hRS (Ne.symm hPR) (by omega)
      simp [hRx0, hPx0] at eyR ezR
      omega
    have hC : C = (⟨0, b, 0, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hCx0, hCy, hCz0]
    have hP : P = (⟨0, b - 1, P.z, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hPx0, hPy]
    have hR : R = (⟨0, 0, P.z + 1, by omega⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hRx0, hRy0, hRz]
    have hS : ({C, P, R} : Finset (Normal a b 0)) = p4ZSocles ha P.z := by
      rw [hC, hP, hR]
      rfl
    rw [hS]
    exact BaseCoverShape.p4Z ha hb hPzp

/-- Complete pure three-root cover with a fixed x-centre.-/
theorem h5_pure_three_cover
    (C P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b 0))) (hb : 2 ≤ b)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C) :
    BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
  obtain ⟨Y, hy⟩ := h.centres .y
  obtain ⟨Z, hz⟩ := h.centres .z
  have hYm : Y = C ∨ Y = P ∨ Y = R := by simpa using hy.1
  have hZm : Z = C ∨ Z = P ∨ Z = R := by simpa using hz.1
  have directCase (P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R)
      (hPR : P ≠ R)
      (h' : CoverHypotheses ({C, P, R} : Finset (Normal a b 0)))
      (hx' : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
      (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
      (hzC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z C) :
      BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
    by_cases hlast : C.x = a - 1
    · exact pure_last_direct_three C P R hCP hCR hPR h' hb hx' hyP hzC hlast
    · exact pure_below_direct_three C P R hCP hCR hPR h' hb hx' hyP hzC
        (by have := C.x_lt; omega)
  have commonCase (P R : Normal a b 0) (hCP : C ≠ P) (hCR : C ≠ R)
      (hPR : P ≠ R)
      (h' : CoverHypotheses ({C, P, R} : Finset (Normal a b 0)))
      (hx' : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .x C)
      (hyP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .y P)
      (hzP : IsDirectionalCentre ({C, P, R} : Finset (Normal a b 0)) .z P) :
      BaseCoverShape ({C, P, R} : Finset (Normal a b 0)) := by
    by_cases hlast : C.x = a - 1
    · exact pure_last_common_three C P R hCP hCR hPR h' hb hx' hyP hzP hlast
    · exact pure_below_common_three C P R hCP hCR hPR h' hb hx' hyP hzP
        (by have := C.x_lt; omega)
  rcases hYm with hYC | hYP | hYR
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      exact False.elim (directional_centres_not_all_equal h hxC hy hz ⟨rfl, rfl⟩)
    · subst Z
      exact pure_reflected_three C P R hCP hCR hPR h hb hxC hy hz
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b 0)) = {C, P, R} := by simp [Finset.pair_comm]
      have out := pure_reflected_three C R P hCR hCP (Ne.symm hPR)
        (by simpa [h'] using h) hb (by simpa [h'] using hxC)
        (by simpa [h'] using hy) (by simpa [h'] using hz)
      simpa [h'] using out
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      exact directCase P R hCP hCR hPR h hxC hy hz
    · subst Z
      exact commonCase P R hCP hCR hPR h hxC hy hz
    · subst Z
      exact pure_distinct_three C P R hCP hCR hPR h hb hxC hy hz
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b 0)) = {C, P, R} := by simp [Finset.pair_comm]
      have out := directCase R P hCR hCP (Ne.symm hPR)
        (by simpa [h'] using h) (by simpa [h'] using hxC)
        (by simpa [h'] using hy) (by simpa [h'] using hz)
      simpa [h'] using out
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b 0)) = {C, P, R} := by simp [Finset.pair_comm]
      have out := pure_distinct_three C R P hCR hCP (Ne.symm hPR)
        (by simpa [h'] using h) hb (by simpa [h'] using hxC)
        (by simpa [h'] using hy) (by simpa [h'] using hz)
      simpa [h'] using out
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b 0)) = {C, P, R} := by simp [Finset.pair_comm]
      have out := commonCase R P hCR hCP (Ne.symm hPR)
        (by simpa [h'] using h) (by simpa [h'] using hxC)
        (by simpa [h'] using hy) (by simpa [h'] using hz)
      simpa [h'] using out

/-- Complete mixed three-root cover with a fixed x-centre.-/
theorem h5_mixed_three_cover
    (C P R : Normal a b c) (hCP : C ≠ P) (hCR : C ≠ R) (hPR : P ≠ R)
    (h : CoverHypotheses ({C, P, R} : Finset (Normal a b c)))
    (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hxC : IsDirectionalCentre ({C, P, R} : Finset (Normal a b c)) .x C) :
    CoverShape ({C, P, R} : Finset (Normal a b c)) := by
  obtain ⟨Y, hy⟩ := h.centres .y
  obtain ⟨Z, hz⟩ := h.centres .z
  have hYm : Y = C ∨ Y = P ∨ Y = R := by simpa using hy.1
  have hZm : Z = C ∨ Z = P ∨ Z = R := by simpa using hz.1
  have cornerImpossible : C.x = a - 1 → C.y = 0 → C.z = 0 → False := by
    intro hlast hCy hCz
    rcases exists_root_above_of_mem_standardSet h.live_tie.2.2.2 with
      ⟨Q, hQS, htQ⟩
    have ht := (Normal.exact_divides_iff (liveTiePoint : Normal a b c) Q).1 htQ
    simp [liveTiePoint, Normal.DividesCriterion] at ht
    have hQC : Q ≠ C := by
      intro heq
      subst Q
      omega
    have hxQ := root_x_zero_at_last h.antichain hxC hQS hQC hlast
    have hxw := h4_x_edge_wrapped_exact h.antichain hxC hQS hQC hxQ
      (by omega) (by omega)
    have hCQ : Normal.DividesCriterion C Q := by
      unfold Normal.DividesCriterion
      exact ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
    exact (h.antichain C hxC.1 Q hQS (Ne.symm hQC))
      ((Normal.exact_divides_iff C Q).2 hCQ)
  have topCase (Y Z : Normal a b c) (hCY : C ≠ Y) (hCZ : C ≠ Z)
      (hYZ : Y ≠ Z)
      (hx' : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .x C)
      (hyY : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .y Y)
      (hzZ : IsDirectionalCentre ({C, Y, Z} : Finset (Normal a b c)) .z Z)
      (h' : CoverHypotheses ({C, Y, Z} : Finset (Normal a b c))) :
      CoverShape ({C, Y, Z} : Finset (Normal a b c)) := by
    by_cases hlast : C.x = a - 1
    · by_cases hCy0 : C.y = 0
      · by_cases hCz0 : C.z = 0
        · exact False.elim (cornerImpossible hlast hCy0 hCz0)
        · exact CoverShape.direct (mixed_last_yzero_distinct_centres_top
            C Y Z hCY hCZ hYZ h' hb hc hx' hyY hzZ hlast hCy0 (by omega))
      · by_cases hCz0 : C.z = 0
        · exact mixed_last_zzero_distinct_centres_top
            C Y Z hCY hCZ hYZ h' hb hc hx' hyY hzZ hlast (by omega) hCz0
        · exact CoverShape.direct (mixed_last_distinct_centres_top
            C Y Z hCY hCZ hYZ h' hb (by omega) hx' hyY hzZ hlast (by omega) (by omega))
    · have hbelow : C.x < a - 1 := by have := C.x_lt; omega
      have hbnd := below_last_live_bounds h' hx' hbelow
      exact CoverShape.direct (mixed_below_distinct_centres_top
        C Y Z hCY hCZ hYZ h' hb (by omega) hx' hyY hzZ hbelow
          (by omega) (by omega))
  rcases hYm with hYC | hYP | hYR
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      exact False.elim (directional_centres_not_all_equal h hxC hy hz ⟨rfl, rfl⟩)
    · subst Z
      by_cases hlast : C.x = a - 1
      · exact mixed_last_reflected_three C P R hCP hCR hPR h hb hc hxC hy hz hlast
      · exact mixed_below_reflected_three C P R hCP hCR hPR h hb hc hxC hy hz
          (by have := C.x_lt; omega)
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b c)) = {C, P, R} := by
        simp [Finset.pair_comm]
      have hh : CoverHypotheses ({C, R, P} : Finset (Normal a b c)) := by simpa [h'] using h
      have hx' : IsDirectionalCentre ({C, R, P} : Finset (Normal a b c)) .x C := by simpa [h'] using hxC
      have hy' : IsDirectionalCentre ({C, R, P} : Finset (Normal a b c)) .y C := by simpa [h'] using hy
      have hz' : IsDirectionalCentre ({C, R, P} : Finset (Normal a b c)) .z R := by simpa [h'] using hz
      have out : CoverShape ({C, R, P} : Finset (Normal a b c)) := by
        by_cases hlast : C.x = a - 1
        · exact mixed_last_reflected_three C R P hCR hCP (Ne.symm hPR) hh hb hc hx' hy' hz' hlast
        · exact mixed_below_reflected_three C R P hCR hCP (Ne.symm hPR) hh hb hc hx' hy' hz'
            (by have := C.x_lt; omega)
      simpa [h'] using out
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      by_cases hlast : C.x = a - 1
      · exact CoverShape.direct (mixed_last_direct_three C P R hCP hCR hPR h hb hc hxC hy hz hlast)
      · exact CoverShape.direct (mixed_below_direct_three C P R hCP hCR hPR h hb hc hxC hy hz
          (by have := C.x_lt; omega))
    · subst Z
      by_cases hlast : C.x = a - 1
      · by_cases hCy0 : C.y = 0
        · exact CoverShape.direct (mixed_last_common_yzero_three
            C P R hCP hCR hPR h hb hc hxC hy hz hlast hCy0)
        · have hCz0 : C.z = 0 := by
            by_contra hz0
            have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
            have hxP := root_x_zero_at_last h.antichain hxC hy.1 (Ne.symm hCP) hlast
            have ey := h4_y_edge_exact h.antichain hy hCS hCP (by omega)
            have ez := h4_z_edge_exact h.antichain hz hCS hCP (by omega)
            simp [hxP, hlast] at ey ez
            omega
          exact mixed_last_common_zzero_three
            C P R hCP hCR hPR h hb hc hxC hy hz hlast hCz0
      · exact False.elim (mixed_below_common_impossible_three C P R hCP h hb hc hxC hy hz
          (by have := C.x_lt; omega))
    · subst Z
      exact topCase P R hCP hCR hPR hxC hy hz h
  · subst Y
    rcases hZm with hZC | hZP | hZR
    · subst Z
      have h' : ({C, R, P} : Finset (Normal a b c)) = {C, P, R} := by simp [Finset.pair_comm]
      have out : CoverShape ({C, R, P} : Finset (Normal a b c)) := by
        by_cases hlast : C.x = a - 1
        · exact CoverShape.direct (mixed_last_direct_three C R P hCR hCP (Ne.symm hPR)
            (by simpa [h'] using h) hb hc (by simpa [h'] using hxC)
            (by simpa [h'] using hy) (by simpa [h'] using hz) hlast)
        · exact CoverShape.direct (mixed_below_direct_three C R P hCR hCP (Ne.symm hPR)
            (by simpa [h'] using h) hb hc (by simpa [h'] using hxC)
            (by simpa [h'] using hy) (by simpa [h'] using hz)
            (by have := C.x_lt; omega))
      simpa [h'] using out
    · subst Z
      have out := topCase R P hCR hCP (Ne.symm hPR)
        (by simpa [Finset.pair_comm] using hxC)
        (by simpa [Finset.pair_comm] using hy)
        (by simpa [Finset.pair_comm] using hz)
        (by simpa [Finset.pair_comm] using h)
      simpa [Finset.pair_comm] using out
    · subst Z
      by_cases hlast : C.x = a - 1
      · by_cases hCy0 : C.y = 0
        · have h' : ({C, R, P} : Finset (Normal a b c)) = {C, P, R} := by simp [Finset.pair_comm]
          have out := mixed_last_common_yzero_three C R P hCR hCP (Ne.symm hPR)
            (by simpa [h'] using h) hb hc (by simpa [h'] using hxC)
            (by simpa [h'] using hy) (by simpa [h'] using hz) hlast hCy0
          exact CoverShape.direct (by simpa [h'] using out)
        · have hCz0 : C.z = 0 := by
            by_contra hz0
            have hCS : C ∈ ({C, P, R} : Finset (Normal a b c)) := by simp
            have hxR := root_x_zero_at_last h.antichain hxC hy.1 (Ne.symm hCR) hlast
            have ey := h4_y_edge_exact h.antichain hy hCS hCR (by omega)
            have ez := h4_z_edge_exact h.antichain hz hCS hCR (by omega)
            simp [hxR, hlast] at ey ez
            omega
          have h' : ({C, R, P} : Finset (Normal a b c)) = {C, P, R} := by simp [Finset.pair_comm]
          have out := mixed_last_common_zzero_three C R P hCR hCP (Ne.symm hPR)
            (by simpa [h'] using h) hb hc (by simpa [h'] using hxC)
            (by simpa [h'] using hy) (by simpa [h'] using hz) hlast hCz0
          simpa [h'] using out
      · exact False.elim (mixed_below_common_impossible_three C R P hCR
          (by simpa [Finset.pair_comm] using h) hb hc
          (by simpa [Finset.pair_comm] using hxC)
          (by simpa [Finset.pair_comm] using hy)
          (by simpa [Finset.pair_comm] using hz)
          (by have := C.x_lt; omega))

/-- H5 with a selected x-centre.  The cardinal hypotheses reduce the root
finset to an exact pair or triple; all permutations are handled by finset
commutativity before invoking the coordinate covers above.-/
theorem h5_cover_with_xcentre
    (S : Finset (Normal a b c)) (h : CoverHypotheses S)
    (C : Normal a b c) (hxC : IsDirectionalCentre S .x C) : CoverShape S := by
  have hcard : S.card = 2 ∨ S.card = 3 := by
    have := h.card_ge_two
    have := h.card_le_three
    omega
  rcases hcard with hcard | hcard
  · obtain ⟨P, Q, hPQ, hS⟩ := Finset.card_eq_two.mp hcard
    subst S
    have hCm : C = P ∨ C = Q := by simpa using hxC.1
    rcases hCm with hCP | hCQ
    · subst C
      exact h5_two_root_cover P Q hPQ h hxC
    · subst C
      have hswap : ({Q, P} : Finset (Normal a b c)) = {P, Q} := by simp [Finset.pair_comm]
      have out := h5_two_root_cover Q P (Ne.symm hPQ)
        (by simpa [hswap] using h) (by simpa [hswap] using hxC)
      simpa [hswap] using out
  · obtain ⟨P, Q, R, hPQ, hPR, hQR, hS⟩ := Finset.card_eq_three.mp hcard
    subst S
    have hCm : C = P ∨ C = Q ∨ C = R := by simpa using hxC.1
    rcases h.live_domain with hmix | hpure
    · rcases hmix with ⟨hb, hc⟩
      rcases hCm with hCP | hCQ | hCR
      · subst C
        exact h5_mixed_three_cover P Q R hPQ hPR hQR h hb hc hxC
      · subst C
        have hs : ({Q, P, R} : Finset (Normal a b c)) = {P, Q, R} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have out := h5_mixed_three_cover Q P R (Ne.symm hPQ) hQR hPR
          (by simpa [hs] using h) hb hc (by simpa [hs] using hxC)
        simpa [hs] using out
      · subst C
        have hs : ({R, P, Q} : Finset (Normal a b c)) = {P, Q, R} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have out := h5_mixed_three_cover R P Q (Ne.symm hPR) (Ne.symm hQR) hPQ
          (by simpa [hs] using h) hb hc (by simpa [hs] using hxC)
        simpa [hs] using out
    · rcases hpure with ⟨hb, hc⟩
      subst c
      rcases hCm with hCP | hCQ | hCR
      · subst C
        exact CoverShape.direct (h5_pure_three_cover P Q R hPQ hPR hQR h hb hxC)
      · subst C
        have hs : ({Q, P, R} : Finset (Normal a b 0)) = {P, Q, R} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have out := h5_pure_three_cover Q P R (Ne.symm hPQ) hQR hPR
          (by simpa [hs] using h) hb (by simpa [hs] using hxC)
        exact CoverShape.direct (by simpa [hs] using out)
      · subst C
        have hs : ({R, P, Q} : Finset (Normal a b 0)) = {P, Q, R} := by
          ext x; simp [or_comm, or_left_comm, or_assoc]
        have out := h5_pure_three_cover R P Q (Ne.symm hPR) (Ne.symm hQR) hPQ
          (by simpa [hs] using h) hb (by simpa [hs] using hxC)
        exact CoverShape.direct (by simpa [hs] using out)

/-- Public below-last half of H5.-/
theorem h5_cover_below_last
    (S : Finset (Normal a b c)) (h : CoverHypotheses S)
    (C : Normal a b c) (hxC : IsDirectionalCentre S .x C)
    (hbelow : C.x < a - 1) : CoverShape S := by
  have hnotlast : C.x ≠ a - 1 := by omega
  by_cases hlast : C.x = a - 1
  · exact False.elim (hnotlast hlast)
  · exact h5_cover_with_xcentre S h C hxC

/-- Public last-layer half of H5, including wrapped-x boundary branches.-/
theorem h5_cover_last_layer
    (S : Finset (Normal a b c)) (h : CoverHypotheses S)
    (C : Normal a b c) (hxC : IsDirectionalCentre S .x C)
    (hlast : C.x = a - 1) : CoverShape S := by
  have hnotbelow : ¬ C.x < a - 1 := by omega
  by_cases hbelow : C.x < a - 1
  · exact False.elim (hnotbelow hbelow)
  · exact h5_cover_with_xcentre S h C hxC

/-- Full unbounded symbolic H5 cover.-/
theorem h5_full_symbolic_cover
    (S : Finset (Normal a b c)) (h : CoverHypotheses S) : CoverShape S := by
  obtain ⟨C, hxC⟩ := h.centres .x
  by_cases hlast : C.x = a - 1
  · exact h5_cover_last_layer S h C hxC hlast
  · exact h5_cover_below_last S h C hxC (by have := C.x_lt; omega)

/-- A base H5 shape with exactly three roots cannot be one of the two-root
core constructors.  This uses root-finset cardinality only, never border
cardinality.-/
private theorem pair_card_ne_three {α : Type*} [DecidableEq α] (p q : α) :
    ({p, q} : Finset α).card ≠ 3 := by
  have hle := Finset.card_le_two (a := p) (b := q)
  omega

theorem typeThreeBaseShape_of_base
    {S : Finset (Normal a b c)} (hcard : S.card = 3)
    (hs : BaseCoverShape S) : TypeThreeBaseShape S := by
  cases hs with
  | topDeletion h => exact TypeThreeBaseShape.topDeletion h
  | pureFibreProduct h => exact TypeThreeBaseShape.pureFibreProduct h
  | m2K ha hu hv hr => exact TypeThreeBaseShape.m2K ha hu hv hr
  | m2Z ha hu hv hr => exact TypeThreeBaseShape.m2Z ha hu hv hr
  | m3K ha hb hc hv => exact TypeThreeBaseShape.m3K ha hb hc hv
  | m4Y ha hu => exact TypeThreeBaseShape.m4Y ha hu
  | m5Y ha hb hc hv => exact TypeThreeBaseShape.m5Y ha hb hc hv
  | m5Z ha hb hc hv => exact TypeThreeBaseShape.m5Z ha hb hc hv
  | p4Z ha hb hv => exact TypeThreeBaseShape.p4Z ha hb hv
  | p5Z ha hb hv => exact TypeThreeBaseShape.p5Z ha hb hv
  | m2 ha hu hv hr =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [m2Socles] using hcard)
  | m3 ha hb hc hv =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [m3Socles] using hcard)
  | m4 ha hu =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [m4Socles] using hcard)
  | m5 ha hb hc hv =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [m5Socles] using hcard)
  | p3 ha hb =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [p3Socles] using hcard)
  | p4 ha hb hv =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [p4Socles] using hcard)
  | p5 ha hb hv =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [p5Socles] using hcard)
  | p6 ha hb hv =>
      exfalso
      exact pair_card_ne_three _ _ (by simpa only [p6Socles] using hcard)

/-- Type-three specialization of H5.  Only top deletion, pure fibre product,
and the eight Run-04 extension rows remain (with explicit mixed reflection).-/
theorem h5_typeThree_specialized_cover
    (S : Finset (Normal a b c)) (h : CoverHypotheses S) (hcard : S.card = 3) :
    TypeThreeCoverShape S := by
  cases h5_full_symbolic_cover S h with
  | direct hs =>
    exact TypeThreeCoverShape.direct (typeThreeBaseShape_of_base hcard hs)
  | reflected hb hc hs =>
    apply TypeThreeCoverShape.reflected hb hc
    apply typeThreeBaseShape_of_base
    · simpa [swapYZFinset] using hcard
    · exact hs

end P23.OneTie
