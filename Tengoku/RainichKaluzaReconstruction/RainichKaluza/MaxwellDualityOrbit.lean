import Tengoku.RainichKaluzaReconstruction.RainichKaluza.MaxwellPrincipalProjectors
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maxwell duality orbit on a canonical principal frame

Once the two non-null Maxwell principal planes are fixed, a real two-form is
represented in a compatible local orthonormal frame by an electric/magnetic
amplitude pair `(E,B)`.  Its stress magnitude depends only on `E²+B²`.

This file proves constructively that every other nonzero pair with the same
magnitude is obtained by a unique unit-circle duality parameter at the
amplitude level.  Trigonometric angle choices are unnecessary: the parameter
is recovered by normalized dot and determinant pairings.
-/

namespace RainichKaluza

/-- Algebraic duality parameter `(c,s)` with `c²+s²=1`.-/
structure DualityParameter where
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

/--
@isnad1 id=eq.2h2v.s4.5439149c0e82 from=translated src=- shape=04c0b690 vocab=438467e7
-/
@[ext]
theorem DualityParameter.ext
    (p r : DualityParameter) (hc : p.c = r.c) (hs : p.s = r.s) :
    p = r := by
  cases p
  cases r
  simp_all

/-- Electric amplitude after a duality rotation.-/
def dualityElectric (p : DualityParameter) (E B : ℝ) : ℝ :=
  p.c * E - p.s * B

/-- Magnetic amplitude after a duality rotation.-/
def dualityMagnetic (p : DualityParameter) (E B : ℝ) : ℝ :=
  p.s * E + p.c * B

/-- Canonical stress magnitude determined by a principal-frame amplitude
pair. Overall normalization can be restored separately.-/
def canonicalMaxwellMagnitude (E B : ℝ) : ℝ :=
  E ^ 2 + B ^ 2

/-- Duality preserves the canonical Maxwell stress magnitude.
@isnad1 id=eq.0h3v.s4.b705ae43172c from=translated src=- shape=7841e249 vocab=19f96d93
-/
theorem canonicalMaxwellMagnitude_duality
    (p : DualityParameter) (E B : ℝ) :
    canonicalMaxwellMagnitude (dualityElectric p E B)
      (dualityMagnetic p E B) = canonicalMaxwellMagnitude E B := by
  unfold canonicalMaxwellMagnitude dualityElectric dualityMagnetic
  calc
    (p.c * E - p.s * B) ^ 2 + (p.s * E + p.c * B) ^ 2 =
        (p.c ^ 2 + p.s ^ 2) * (E ^ 2 + B ^ 2) := by ring
    _ = E ^ 2 + B ^ 2 := by rw [p.unit]; ring

/-- Constructive normalized dot product between two equal-magnitude pairs.-/
noncomputable def dualityCosineBetween (E B E' B' : ℝ) : ℝ :=
  (E * E' + B * B') / canonicalMaxwellMagnitude E B

/-- Constructive normalized determinant between two equal-magnitude pairs.-/
noncomputable def dualitySineBetween (E B E' B' : ℝ) : ℝ :=
  (E * B' - B * E') / canonicalMaxwellMagnitude E B

/-- The normalized dot/determinant pair lies on the unit circle whenever the
two nonzero amplitude pairs have equal magnitude.
@isnad1 id=eq.2h4v.s6.f50ba8aa9a0c from=translated src=- shape=04158864 vocab=79ec65ac
-/
theorem dualityBetween_unit
    (E B E' B' : ℝ)
    (hmag : canonicalMaxwellMagnitude E B ≠ 0)
    (heq : canonicalMaxwellMagnitude E' B' =
      canonicalMaxwellMagnitude E B) :
    dualityCosineBetween E B E' B' ^ 2 +
      dualitySineBetween E B E' B' ^ 2 = 1 := by
  unfold dualityCosineBetween dualitySineBetween canonicalMaxwellMagnitude at *
  field_simp [hmag]
  nlinarith [sq_nonneg (E * E' + B * B'),
    sq_nonneg (E * B' - B * E')]

/-- The constructive parameter maps the source electric amplitude to the
target amplitude.
@isnad1 id=eq.1h4v.s5.7f97bdbf033a from=translated src=- shape=d41fc512 vocab=b6e751f8
-/
theorem dualityBetween_electric
    (E B E' B' : ℝ)
    (hmag : canonicalMaxwellMagnitude E B ≠ 0) :
    dualityCosineBetween E B E' B' * E -
      dualitySineBetween E B E' B' * B = E' := by
  have hN : E ^ 2 + B ^ 2 ≠ 0 := by
    simpa [canonicalMaxwellMagnitude] using hmag
  unfold dualityCosineBetween dualitySineBetween canonicalMaxwellMagnitude
  field_simp [hN]
  ring

/-- The constructive parameter maps the source magnetic amplitude to the
target amplitude.
@isnad1 id=eq.1h4v.s5.095d3dc91a3b from=translated src=- shape=b3705f51 vocab=8dd2ddc1
-/
theorem dualityBetween_magnetic
    (E B E' B' : ℝ)
    (hmag : canonicalMaxwellMagnitude E B ≠ 0) :
    dualitySineBetween E B E' B' * E +
      dualityCosineBetween E B E' B' * B = B' := by
  have hN : E ^ 2 + B ^ 2 ≠ 0 := by
    simpa [canonicalMaxwellMagnitude] using hmag
  unfold dualityCosineBetween dualitySineBetween canonicalMaxwellMagnitude
  field_simp [hN]
  ring

/-- **Canonical non-null Maxwell orbit theorem.** Two amplitude pairs with a
nonzero source magnitude determine the same canonical stress magnitude if and
only if a unit duality parameter maps one pair to the other.
@isnad1 id=iff.1h4v.s5.701428e50460 from=translated src=- shape=ce047f31 vocab=19f96d93
-/
theorem exists_dualityParameter_iff_same_magnitude
    (E B E' B' : ℝ) (hmag : canonicalMaxwellMagnitude E B ≠ 0) :
    (∃ p : DualityParameter,
      dualityElectric p E B = E' ∧ dualityMagnetic p E B = B') ↔
      canonicalMaxwellMagnitude E' B' = canonicalMaxwellMagnitude E B := by
  constructor
  · rintro ⟨p, rfl, rfl⟩
    exact canonicalMaxwellMagnitude_duality p E B
  · intro heq
    let p : DualityParameter :=
      { c := dualityCosineBetween E B E' B'
        s := dualitySineBetween E B E' B'
        unit := dualityBetween_unit E B E' B' hmag heq }
    refine ⟨p, ?_, ?_⟩
    · exact dualityBetween_electric E B E' B' hmag
    · exact dualityBetween_magnetic E B E' B' hmag

/-- A duality parameter acting on a nonzero amplitude pair is unique.
@isnad1 id=eq.3h4v.s5.acdbc0d9f63d from=translated src=- shape=50da0802 vocab=19f96d93
-/
theorem dualityParameter_unique
    (p r : DualityParameter) (E B : ℝ)
    (hmag : canonicalMaxwellMagnitude E B ≠ 0)
    (hE : dualityElectric p E B = dualityElectric r E B)
    (hB : dualityMagnetic p E B = dualityMagnetic r E B) :
    p = r := by
  have hc : p.c = r.c := by
    have hscaled : (p.c - r.c) * canonicalMaxwellMagnitude E B = 0 := by
      unfold dualityElectric dualityMagnetic canonicalMaxwellMagnitude at *
      linear_combination E * hE + B * hB
    exact sub_eq_zero.mp <| (mul_eq_zero.mp hscaled).resolve_right hmag
  have hs : p.s = r.s := by
    have hscaled : (p.s - r.s) * canonicalMaxwellMagnitude E B = 0 := by
      unfold dualityElectric dualityMagnetic canonicalMaxwellMagnitude at *
      linear_combination -B * hE + E * hB
    exact sub_eq_zero.mp <| (mul_eq_zero.mp hscaled).resolve_right hmag
  cases p
  cases r
  simp_all

/-- Composition of two unit duality parameters. The second parameter acts
first.-/
def dualityCompose (p r : DualityParameter) : DualityParameter where
  c := p.c * r.c - p.s * r.s
  s := p.s * r.c + p.c * r.s
  unit := by
    calc
      (p.c * r.c - p.s * r.s) ^ 2 +
          (p.s * r.c + p.c * r.s) ^ 2 =
        (p.c ^ 2 + p.s ^ 2) * (r.c ^ 2 + r.s ^ 2) := by ring
      _ = 1 := by rw [p.unit, r.unit]; ring

/-- Identity duality parameter.-/
def dualityIdentity : DualityParameter where
  c := 1
  s := 0
  unit := by norm_num

/-- Inverse duality parameter.-/
def dualityInverse (p : DualityParameter) : DualityParameter where
  c := p.c
  s := -p.s
  unit := by simpa using p.unit

/-- The amplitude action respects composition.
@isnad1 id=eq.0h4v.s4.92d505335632 from=translated src=- shape=4af7c3c9 vocab=c0c05af2
-/
theorem dualityElectric_compose
    (p r : DualityParameter) (E B : ℝ) :
    dualityElectric p (dualityElectric r E B) (dualityMagnetic r E B) =
      dualityElectric (dualityCompose p r) E B := by
  unfold dualityElectric dualityMagnetic dualityCompose
  ring

/-- The magnetic amplitude action respects composition.
@isnad1 id=eq.0h4v.s4.4a0c44ebe585 from=translated src=- shape=4af7c3c9 vocab=c0c05af2
-/
theorem dualityMagnetic_compose
    (p r : DualityParameter) (E B : ℝ) :
    dualityMagnetic p (dualityElectric r E B) (dualityMagnetic r E B) =
      dualityMagnetic (dualityCompose p r) E B := by
  unfold dualityElectric dualityMagnetic dualityCompose
  ring

/-- Duality composition is associative.
@isnad1 id=eq.0h3v.s4.3dc031f3829a from=translated src=- shape=b8c031c3 vocab=68f9d83b
-/
theorem dualityCompose_assoc (p r t : DualityParameter) :
    dualityCompose (dualityCompose p r) t =
      dualityCompose p (dualityCompose r t) := by
  apply DualityParameter.ext <;> simp [dualityCompose] <;> ring

/-- Identity acts on the left.
@isnad1 id=eq.0h1v.s3.3fcbae9bcad0 from=translated src=- shape=29edb2d9 vocab=f7845ae5
-/
theorem dualityCompose_identity_left (p : DualityParameter) :
    dualityCompose dualityIdentity p = p := by
  apply DualityParameter.ext <;> simp [dualityCompose, dualityIdentity]

/-- Identity acts on the right.
@isnad1 id=eq.0h1v.s3.4ee1adf59d0e from=translated src=- shape=9960b201 vocab=f7845ae5
-/
theorem dualityCompose_identity_right (p : DualityParameter) :
    dualityCompose p dualityIdentity = p := by
  apply DualityParameter.ext <;> simp [dualityCompose, dualityIdentity]

/-- The constructed inverse cancels on the left.
@isnad1 id=eq.0h1v.s3.4bba553d7635 from=translated src=- shape=9d0ab98d vocab=b3997b87
-/
theorem dualityCompose_inverse_left (p : DualityParameter) :
    dualityCompose (dualityInverse p) p = dualityIdentity := by
  apply DualityParameter.ext
  · simp only [dualityCompose, dualityInverse, dualityIdentity]
    nlinarith [p.unit]
  · simp only [dualityCompose, dualityInverse, dualityIdentity]
    ring

/-- **Duality overlap cocycle.** Successive local seed changes compose to the
single parameter `p∘r`.
@isnad1 id=and.4h8v.s6.9a9aaf0d0805 from=translated src=- shape=75730e1f vocab=c0c05af2
-/
theorem duality_overlap_cocycle
    (p r : DualityParameter) (E B E' B' E'' B'' : ℝ)
    (hrE : dualityElectric r E B = E')
    (hrB : dualityMagnetic r E B = B')
    (hpE : dualityElectric p E' B' = E'')
    (hpB : dualityMagnetic p E' B' = B'') :
    dualityElectric (dualityCompose p r) E B = E'' ∧
      dualityMagnetic (dualityCompose p r) E B = B'' := by
  constructor
  · rw [← hpE, ← hrE, ← hrB, dualityElectric_compose]
  · rw [← hpB, ← hrE, ← hrB, dualityMagnetic_compose]

end RainichKaluza
