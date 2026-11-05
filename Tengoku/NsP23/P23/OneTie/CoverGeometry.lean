import Tengoku.NsP23.P23.OneTie.SemanticBorder
import Tengoku.NsP23.P23.OneTie.DirectionalCentre

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: root geometry and exact H4 edge equations

This module stays in the normalized one-tie monoid.  It introduces the finite
root hypotheses used by H5 and derives H4 from the frozen predecessor and
divisibility APIs.  No classification or trace statement appears here.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

private theorem cover_a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

/-- Distinct selected roots are incomparable for actual monoid divisibility.-/
def IsRootAntichain (S : Finset (Normal a b c)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ¬p ∣ q

/-- The normalized common monomial `x^a = y^b z^c`.-/
def liveTiePoint : Normal a b c := ⟨0, b, c, cover_a_pos⟩

/-- Variables and the common tie all survive in the finite standard set.-/
def IsLiveTie (S : Finset (Normal a b c)) : Prop :=
  (Normal.xGenerator : Normal a b c) ∈ standardSet S ∧
  (Normal.yGenerator : Normal a b c) ∈ standardSet S ∧
  (Normal.zGenerator : Normal a b c) ∈ standardSet S ∧
  liveTiePoint ∈ standardSet S

/-- A root dominates when the standard set is its full divisor downset plus
the other roots, with no coordinate-box replacement.-/
def IsDominantRoot (S : Finset (Normal a b c)) (C : Normal a b c) : Prop :=
  C ∈ S ∧
    standardSet S =
      Normal.divisorDownset C ∪ (↑(S.erase C) : Set (Normal a b c))

/-- The exact combinatorial assumptions consumed by the H5 cover.-/
structure CoverHypotheses (S : Finset (Normal a b c)) : Prop where
  a_ge_two : 2 ≤ a
  live_domain : (1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0)
  live_tie : IsLiveTie S
  card_ge_two : 2 ≤ S.card
  card_le_three : S.card ≤ 3
  antichain : IsRootAntichain S
  centres : HasDirectionalCentres S
  no_dominant : ∀ C ∈ S, ¬IsDominantRoot S C

private theorem predecessor_ne_self (ha : 2 ≤ a) {e : Direction}
    {s q : Normal a b c} (hq : Normal.predecessor e s = some q) : q ≠ s := by
  intro h
  subst q
  have hmul := (Normal.predecessor_eq_some_iff_mul e s s).1 hq
  have hmul' : s * e.generator = s * 1 := by simpa using hmul
  exact (variableGenerators_ne_one_of_two_le ha e)
    (Normal.mul_left_cancel hmul')

/-- Under an antichain, dominance is exactly being the common x/y/z centre.
@isnad1 id=iff.2h5v.s6.fbebdf7129fd from=translated src=- shape=c6d0f011 vocab=b16f87cd
-/
theorem isDominantRoot_iff_all_directionalCentre
    (S : Finset (Normal a b c)) (C : Normal a b c)
    (ha : 2 ≤ a) (hanti : IsRootAntichain S) :
    IsDominantRoot S C ↔
      C ∈ S ∧ ∀ e : Direction, IsDirectionalCentre S e C := by
  constructor
  · rintro ⟨hCS, hdom⟩
    refine ⟨hCS, ?_⟩
    intro e
    refine ⟨hCS, ?_⟩
    intro s hs q hq
    have hqs : q ∣ s := by
      exact ⟨e.generator,
        ((Normal.predecessor_eq_some_iff_mul e s q).1 hq).symm⟩
    have hqstd : q ∈ standardSet S := ⟨s, hs, hqs⟩
    rw [hdom] at hqstd
    rcases hqstd with hqC | hqroot
    · exact hqC
    · have hqS : q ∈ S := Finset.mem_of_mem_erase hqroot
      have hqneC : q ≠ C := Finset.ne_of_mem_erase hqroot
      have hqnes : q ≠ s := predecessor_ne_self ha hq
      exact False.elim ((hanti q hqS s hs hqnes) hqs)
  · rintro ⟨hCS, hcentres⟩
    refine ⟨hCS, ?_⟩
    ext p
    constructor
    · rintro ⟨s, hs, hps⟩
      by_cases hpself : p = s
      · subst p
        by_cases hsC : s = C
        · subst s
          exact Or.inl dvd_rfl
        · exact Or.inr (Finset.mem_erase.mpr ⟨hsC, hs⟩)
      · rcases properDivisor_factors_through_predecessor hps hpself with
          ⟨e, q, hq, hpq⟩
        have hqC : q ∈ Normal.divisorDownset C :=
          (hcentres e).2 s hs q hq
        exact Or.inl (dvd_trans hpq hqC)
    · intro hp
      rcases hp with hpC | hpRoot
      · exact ⟨C, hCS, hpC⟩
      · have hpS : p ∈ S := Finset.mem_of_mem_erase hpRoot
        exact ⟨p, hpS, dvd_rfl⟩

private theorem not_divides_of_distinct_roots {S : Finset (Normal a b c)}
    (hanti : IsRootAntichain S) {C R : Normal a b c}
    (hC : C ∈ S) (hR : R ∈ S) (hne : R ≠ C) :
    ¬Normal.DividesCriterion R C := by
  intro hdiv
  exact (hanti R hR C hC hne) ((Normal.exact_divides_iff R C).2 hdiv)

/-- H4 y-edge: an existing y-predecessor covered by a distinct root centre
forces the exact indicator equation and the transverse inequality.
@isnad1 id=and.5h6v.s7.2b53c28bcd3d from=translated src=- shape=2061b859 vocab=405e785f
-/
theorem h4_y_edge_exact {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hcentre : IsDirectionalCentre S .y C)
    (hR : R ∈ S) (hne : R ≠ C) (hy : 0 < R.y) :
    R.y + (if C.x < R.x then b else 0) = C.y + 1 ∧
      R.z + (if C.x < R.x then c else 0) ≤ C.z := by
  have hc := ((isDirectionalCentre_y_iff S C).1 hcentre).2 R hR hy
  have hnd := not_divides_of_distinct_roots hanti hcentre.1 hR hne
  unfold Normal.DividesCriterion at hnd
  by_cases hx : C.x < R.x
  · simp [hx]
    omega
  · simp [hx]
    omega

/-- H4 z-edge, symmetric to `h4_y_edge_exact`.
@isnad1 id=and.5h6v.s7.16ea106f427f from=translated src=- shape=dd795666 vocab=81e0ffa9
-/
theorem h4_z_edge_exact {S : Finset (Normal a b c)} {C R : Normal a b c}
    (hanti : IsRootAntichain S) (hcentre : IsDirectionalCentre S .z C)
    (hR : R ∈ S) (hne : R ≠ C) (hz : 0 < R.z) :
    R.z + (if C.x < R.x then c else 0) = C.z + 1 ∧
      R.y + (if C.x < R.x then b else 0) ≤ C.y := by
  have hc := ((isDirectionalCentre_z_iff S C).1 hcentre).2 R hR hz
  have hnd := not_divides_of_distinct_roots hanti hcentre.1 hR hne
  unfold Normal.DividesCriterion at hnd
  by_cases hx : C.x < R.x
  · simp [hx]
    omega
  · simp [hx]
    omega

/-- H4 ordinary x-edge.
@isnad1 id=and.5h6v.s7.53469d3b4aea from=translated src=- shape=12fc7947 vocab=0f0e45a4
-/
theorem h4_x_edge_ordinary_exact {S : Finset (Normal a b c)}
    {C R : Normal a b c} (hanti : IsRootAntichain S)
    (hcentre : IsDirectionalCentre S .x C) (hR : R ∈ S)
    (hne : R ≠ C) (hx : 0 < R.x) :
    R.x = C.x + 1 ∧ R.y ≤ C.y ∧ R.z ≤ C.z := by
  have hc := (((isDirectionalCentre_x_iff S C).1 hcentre).2 R hR).1 hx
  have hnd := not_divides_of_distinct_roots hanti hcentre.1 hR hne
  unfold Normal.DividesCriterion at hnd
  omega

/-- H4 wrapped x-edge. The predecessor guard is explicit, including `c=0`.
@isnad1 id=and.7h6v.s7.fa769dd848eb from=translated src=- shape=c92de6df vocab=fd9840eb
-/
theorem h4_x_edge_wrapped_exact {S : Finset (Normal a b c)}
    {C R : Normal a b c} (hanti : IsRootAntichain S)
    (hcentre : IsDirectionalCentre S .x C) (hR : R ∈ S)
    (hne : R ≠ C) (hx : R.x = 0) (hy : b ≤ R.y) (hz : c ≤ R.z) :
    C.x = a - 1 ∧ R.y ≤ C.y + b ∧ R.z ≤ C.z + c := by
  have hc := (((isDirectionalCentre_x_iff S C).1 hcentre).2 R hR).2 hx hy hz
  have hnd := not_divides_of_distinct_roots hanti hcentre.1 hR hne
  unfold Normal.DividesCriterion at hnd
  have hClt := C.x_lt
  omega

end P23.OneTie
