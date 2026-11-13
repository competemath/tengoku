/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.OccupationPattern
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional occupation profiles

Finite occupation counts supply the sharp raising and preserving multiplicity bounds used in the directional energy estimates.
Ported from `SparseFockFormal.DirectionalBounds` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

namespace Directional

/-- The occupation profile retained by the directional norm arguments.  This
is a count-level abstraction; it does not assert that a site move is valid.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
structure Profile where
  light : ℕ
  heavy : ℕ
  deriving DecidableEq, Repr

namespace Profile

/-- The occupation-profile grade is the light count plus twice the heavy count.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def grade (p : Profile) : ℕ := p.light + 2 * p.heavy

/-- Count transformation for `Y₊`: one light is promoted and one fresh site is
created, so the light count is unchanged and the heavy count increases by one.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def yPlus (p : Profile) : Profile :=
  { light := p.light, heavy := p.heavy + 1 }

/-- Count transformation for `Y₀`: one heavy is demoted and one fresh light is
created, producing two additional light particles and one fewer heavy particle.
The theorem using this definition explicitly assumes `1 ≤ p.heavy`.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def yZero (p : Profile) : Profile :=
  { light := p.light + 2, heavy := p.heavy - 1 }

/-- A transpose light hop only moves a light particle.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def lightHop (p : Profile) : Profile := p

/-- The directional raising profile retains the light count.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.4adb95c100d4 from=translated src=- shape=8d4cac31 vocab=afdc5f30
-/
@[simp] theorem yPlus_light (p : Profile) : p.yPlus.light = p.light := rfl

/-- The directional raising profile increases the heavy count by one.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.168467de3870 from=translated src=- shape=ac0b5851 vocab=45f043f0
-/
@[simp] theorem yPlus_heavy (p : Profile) : p.yPlus.heavy = p.heavy + 1 := rfl

/-- The directional raising profile increases the total grade by two.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.23c9d1263fbe from=translated src=- shape=ac0b5851 vocab=ae808e60
-/
@[simp] theorem yPlus_grade (p : Profile) : p.yPlus.grade = p.grade + 2 := by
  simp [yPlus, grade]
  omega

/-- The directional preserving profile increases the light count by two.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.67f8019c2b8d from=translated src=- shape=ac0b5851 vocab=a74fc0ed
-/
@[simp] theorem yZero_light (p : Profile) : p.yZero.light = p.light + 2 := rfl

/-- The directional preserving profile decreases the heavy count by one.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s4.39a0722c421a from=translated src=- shape=ac0b5851 vocab=3f526348
-/
@[simp] theorem yZero_heavy (p : Profile) : p.yZero.heavy = p.heavy - 1 := rfl

/-- With a heavy particle available, the directional preserving profile keeps the total grade.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h1v.s4.c3e90259c3b4 from=translated src=- shape=812eb910 vocab=cea62356
-/
theorem yZero_grade (p : Profile) (hheavy : 1 ≤ p.heavy) :
    p.yZero.grade = p.grade := by
  simp [yZero, grade]
  omega

/-- A light hop preserves the profile grade.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.a591564f01fc from=translated src=- shape=8d4cac31 vocab=8690d3c1
-/
@[simp] theorem lightHop_grade (p : Profile) : p.lightHop.grade = p.grade := rfl

/-- A light hop preserves the profile light count.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.414461794aaf from=translated src=- shape=8d4cac31 vocab=a2be6792
-/
@[simp] theorem lightHop_light (p : Profile) : p.lightHop.light = p.light := rfl

/-- The light count is bounded by the total occupation grade.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h1v.s3.aa94787db429 from=translated src=- shape=b70c6bb1 vocab=6b5144b4
-/
theorem light_le_grade (p : Profile) : p.light ≤ p.grade := by
  simp [grade]

/-- Twice the heavy count is bounded by the total occupation grade.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h1v.s4.3c684c6c90b7 from=translated src=- shape=856694a9 vocab=84337725
-/
theorem two_mul_heavy_le_grade (p : Profile) : 2 * p.heavy ≤ p.grade := by
  simp [grade]

end Profile

/-- Extract the count profile of a concrete finite sparse-Fock pattern.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def profile {m n : ℕ} (p : Pattern m n) : Profile :=
  { light := p.light.card, heavy := p.heavy.card }

/-- The concrete profile light count is the pattern's light-site cardinality.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s4.ed4cd8152e4e from=translated src=- shape=eccf05b8 vocab=418e4937
-/
@[simp] theorem profile_light {m n : ℕ} (p : Pattern m n) :
    (profile p).light = p.light.card := rfl

/-- The concrete profile heavy count is the pattern's heavy-site cardinality.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s4.d8d8be7276d8 from=translated src=- shape=eccf05b8 vocab=9c8a5d54
-/
@[simp] theorem profile_heavy {m n : ℕ} (p : Pattern m n) :
    (profile p).heavy = p.heavy.card := rfl

/-- The concrete profile grade equals the pattern occupation grade.
Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h3v.s4.060232527bcd from=translated src=- shape=6eedec9e vocab=81bd717d
-/
theorem profile_grade {m n : ℕ} (p : Pattern m n) :
    (profile p).grade = p.grade := by
  simp [profile, Profile.grade, Pattern.grade_eq_card_light_add_two_mul_card_heavy]

/-- The total number of row-local light indices is bounded by the grade.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h3v.s5.880851af920c from=translated src=- shape=913b75a9 vocab=65b4a413
-/
theorem sum_card_lightInRow_le_grade {m n : ℕ} (p : Pattern m n) :
    (∑ r, (p.lightInRow r).card) ≤ p.grade := by
  rw [← Pattern.card_light_eq_sum_card_lightInRow]
  exact p.card_light_le_grade

/-- Twice the total number of row-local heavy indices is bounded by the grade.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h3v.s5.54a203dd4954 from=translated src=- shape=1ad35375 vocab=c212d3df
-/
theorem two_mul_sum_card_heavyInRow_le_grade {m n : ℕ} (p : Pattern m n) :
    2 * (∑ r, (p.heavyInRow r).card) ≤ p.grade := by
  rw [← Pattern.card_heavy_eq_sum_card_heavyInRow]
  exact p.two_mul_card_heavy_le_grade

/-- Any row-indexed family injected into the light sites has total multiplicity
at most the grade.  This is the exact combinatorial premise used after the
row-local Gram/Parseval resummation.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h4v.s5.93af2fc1b8d0 from=translated src=- shape=f6dc4326 vocab=65b4a413
-/
theorem rowLocal_light_multiplicity_le_grade {m n : ℕ}
    (p : Pattern m n) (multiplicity : Fin m → ℕ)
    (hlocal : ∀ r, multiplicity r ≤ (p.lightInRow r).card) :
    (∑ r, multiplicity r) ≤ p.grade := by
  calc
    (∑ r, multiplicity r) ≤ ∑ r, (p.lightInRow r).card := by
      apply Finset.sum_le_sum
      intro r _
      exact hlocal r
    _ ≤ p.grade := sum_card_lightInRow_le_grade p

/-- Any row-indexed family injected into the heavy sites has doubled total
multiplicity at most the grade.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h4v.s6.4d1feced9050 from=translated src=- shape=09ab0310 vocab=c212d3df
-/
theorem two_mul_rowLocal_heavy_multiplicity_le_grade {m n : ℕ}
    (p : Pattern m n) (multiplicity : Fin m → ℕ)
    (hlocal : ∀ r, multiplicity r ≤ (p.heavyInRow r).card) :
    2 * (∑ r, multiplicity r) ≤ p.grade := by
  have hsum : (∑ r, multiplicity r) ≤ ∑ r, (p.heavyInRow r).card := by
    apply Finset.sum_le_sum
    intro r _
    exact hlocal r
  exact le_trans (Nat.mul_le_mul_left 2 hsum)
    (two_mul_sum_card_heavyInRow_le_grade p)

/-- Sharp count consequence for `Y₊`: unlike the coarser grade-only bound,
the move preserves the light count, so both occupation factors are at most `ν`.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h2v.s5.781a8c1dc5e6 from=translated src=- shape=22f29256 vocab=27057391
-/
theorem yPlus_count_sharp {ν : ℕ} (input : Profile)
    (hgrade : input.grade = ν) :
    input.yPlus.light * input.light ≤ ν * ν := by
  rw [Profile.yPlus_light]
  have hle : input.light ≤ ν := by
    simpa [hgrade] using input.light_le_grade
  exact Nat.mul_le_mul hle hle

/-- Denominator-cleared occupation product for `Y₀`.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h2v.s5.d742d910ce7e from=translated src=- shape=dd42ab92 vocab=edd13779
-/
theorem yZero_count {ν : ℕ} (input : Profile) (hheavy : 1 ≤ input.heavy)
    (hgrade : input.grade = ν) :
    2 * (input.yZero.light * input.heavy) ≤ ν * ν := by
  have houtGrade : input.yZero.grade = ν := by
    rw [input.yZero_grade hheavy, hgrade]
  have hout : input.yZero.light ≤ ν := by
    simpa [houtGrade] using input.yZero.light_le_grade
  have hin : 2 * input.heavy ≤ ν := by
    simpa [hgrade] using input.two_mul_heavy_le_grade
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul hout hin

/-- Occupation product for the transpose light hop.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h2v.s5.c70df730069d from=translated src=- shape=22f29256 vocab=01a64a9b
-/
theorem lightHop_count {ν : ℕ} (input : Profile)
    (hgrade : input.grade = ν) :
    input.lightHop.light * input.light ≤ ν * ν := by
  rw [Profile.lightHop_light]
  have hle : input.light ≤ ν := by
    simpa [hgrade] using input.light_le_grade
  exact Nat.mul_le_mul hle hle

/-- Abstract energy closure for `Y₊` and the transpose hop.

`hOutputCS` is the output-side Cauchy--Schwarz/row-Gram estimate and
`hInputParseval` is the reindexed input-side fresh-Parseval estimate.  They are
named hypotheses because this module does not define the Hilbert-space operators.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.4h4v.s6.632e87804146 from=translated src=- shape=516099d7 vocab=150e4428
-/
theorem directional_energy_sq_bound
    {ν inputEnergy reindexedEnergy outputEnergy : ℝ}
    (hν : 0 ≤ ν) (_hinput : 0 ≤ inputEnergy)
    (hOutputCS : outputEnergy ≤ ν * reindexedEnergy)
    (hInputParseval : reindexedEnergy ≤ ν * inputEnergy) :
    outputEnergy ≤ ν ^ 2 * inputEnergy := by
  calc
    outputEnergy ≤ ν * reindexedEnergy := hOutputCS
    _ ≤ ν * (ν * inputEnergy) := by
      exact mul_le_mul_of_nonneg_left hInputParseval hν
    _ = ν ^ 2 * inputEnergy := by ring

/-- Abstract denominator-cleared energy closure for `Y₀`.

The second premise records that twice the reindexed heavy contribution is at
most `ν` times the input energy.

Source: ported from `SparseFockFormal.DirectionalBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h4v.s6.1dda5dfa6dc8 from=translated src=- shape=d917af44 vocab=150e4428
-/
theorem directional_energy_half_sq_bound
    {ν inputEnergy reindexedEnergy outputEnergy : ℝ}
    (hν : 0 ≤ ν)
    (hOutputCS : outputEnergy ≤ ν * reindexedEnergy)
    (hInputHeavy : 2 * reindexedEnergy ≤ ν * inputEnergy) :
    2 * outputEnergy ≤ ν ^ 2 * inputEnergy := by
  calc
    2 * outputEnergy ≤ 2 * (ν * reindexedEnergy) := by linarith
    _ = ν * (2 * reindexedEnergy) := by ring
    _ ≤ ν * (ν * inputEnergy) := by
      exact mul_le_mul_of_nonneg_left hInputHeavy hν
    _ = ν ^ 2 * inputEnergy := by ring

end Directional

end NLAlib.SparseSketch
