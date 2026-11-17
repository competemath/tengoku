import Tengoku.TunnellTwoToOneMap.TunnellMap.PrimitiveDirection
import Tengoku.TunnellTwoToOneMap.TunnellMap.GloballyRankedExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primitive midpoint keys

This file formalizes the representative-level part of Lemmas 2.3 and 4.1.
The primitive direction of `E + F` is the same as that of `(E + F) / 2`, so
the raw integral sums avoid division without changing the paper's key.
-/

namespace TunnellMap

def qBilinear (p q : Triple) : ℤ :=
  2 * p.x * q.x + p.y * q.y + 2 * p.z * q.z

def vsub (p q : Triple) : Triple :=
  ⟨p.x - q.x, p.y - q.y, p.z - q.z⟩

/--
@isnad1 id=eq.0h2v.s3.de4e3d04f9ef from=translated src=- shape=1013c0ce vocab=906c72cf
-/
theorem vadd_comm (p q : Triple) : vadd p q = vadd q p := by
  ext <;> simp [vadd] <;> ring

/--
@isnad1 id=eq.0h2v.s3.fc0bf13253b0 from=translated src=- shape=df575a8f vocab=a447ea41
-/
theorem vsub_swap (p q : Triple) : vsub p q = negTriple (vsub q p) := by
  ext <;> simp [vsub, negTriple]

/--
@isnad1 id=eq.0h1v.s3.3b3b89ab4c58 from=translated src=- shape=1a018cbb vocab=780a4a35
-/
@[simp] theorem qBilinear_self (p : Triple) : qBilinear p p = qForm p := by
  simp [qBilinear, qForm]
  ring

/--
@isnad1 id=lt.1h1v.s5.f43c8cd7d767 from=translated src=- shape=d2b60d00 vocab=971c4662
-/
theorem qForm_pos_of_ne_zero {p : Triple} (hp : p ≠ ⟨0, 0, 0⟩) : 0 < qForm p := by
  by_cases hx : p.x = 0
  · by_cases hy : p.y = 0
    · have hz : p.z ≠ 0 := by
        intro hz
        apply hp
        ext <;> simp_all
      have hzsq : 0 < p.z ^ 2 := sq_pos_of_ne_zero hz
      simp [qForm, hx, hy]
      omega
    · have hysq : 0 < p.y ^ 2 := sq_pos_of_ne_zero hy
      have hzsq : 0 ≤ p.z ^ 2 := sq_nonneg p.z
      simp [qForm, hx]
      nlinarith
  · have hxsq : 0 < p.x ^ 2 := sq_pos_of_ne_zero hx
    have hysq : 0 ≤ p.y ^ 2 := sq_nonneg p.y
    have hzsq : 0 ≤ p.z ^ 2 := sq_nonneg p.z
    simp [qForm]
    nlinarith

/--
@isnad1 id=eq.0h3v.s5.921dbc88c351 from=translated src=- shape=7e20eb4a vocab=3a61665b
-/
theorem qBilinear_vsmul_vsmul (a b : ℤ) (p : Triple) :
    qBilinear (vsmul a p) (vsmul b p) = a * b * qForm p := by
  simp [qBilinear, qForm, vsmul]
  ring

/-- The projective key of a direction: the value of the quadratic form on the
primitive direction, followed by its three coordinates.  Keys are compared
lexicographically in that order.

The key is a plain four-integer record rather than a nested lexicographic
product, so that every key manipulation performed by the executable generator
and by record-driven deferred acceptance is a literal integer computation.-/
structure DirectionKey where
  /-- The value of the quadratic form on the primitive direction.-/
  form : ℤ
  /-- The first coordinate of the primitive direction.-/
  x : ℤ
  /-- The second coordinate of the primitive direction.-/
  y : ℤ
  /-- The third coordinate of the primitive direction.-/
  z : ℤ
deriving DecidableEq

namespace DirectionKey

/-- The lexicographic product that defines the order on keys.-/
def toLexKey (k : DirectionKey) : ℤ ×ₗ (ℤ ×ₗ (ℤ ×ₗ ℤ)) :=
  toLex (k.form, toLex (k.x, toLex (k.y, k.z)))

/--
@isnad1 id=injectiv.0h0v.s3.5fc72a462df8 from=translated src=- shape=c23be227 vocab=f3493861
-/
theorem toLexKey_injective : Function.Injective toLexKey := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [toLexKey, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  simp_all

/-- Executable strict comparison of keys: four integer comparisons.-/
def blt (a b : DirectionKey) : Bool :=
  a.form < b.form || (a.form == b.form &&
    (a.x < b.x || (a.x == b.x && (a.y < b.y || (a.y == b.y && a.z < b.z)))))

/-- Executable comparison of keys.-/
def ble (a b : DirectionKey) : Bool := !blt b a

/--
@isnad1 id=iff.0h2v.s5.f19771a43bcc from=translated src=- shape=d630c08f vocab=e6334c63
-/
theorem blt_iff_lex (a b : DirectionKey) :
    blt a b = true ↔ toLexKey a < toLexKey b := by
  simp only [blt, toLexKey, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Prod.Lex.toLex_lt_toLex]

/--
@isnad1 id=iff.0h2v.s5.38d14bdb7eb4 from=translated src=- shape=d630c08f vocab=73ee8f41
-/
theorem ble_iff_lex (a b : DirectionKey) :
    ble a b = true ↔ toLexKey a ≤ toLexKey b := by
  rw [ble, Bool.not_eq_true', ← Bool.not_eq_true, blt_iff_lex, not_lt]

/-- The lexicographic linear order on keys.  Its decision procedures are the
integer comparisons `blt` and `ble`, so deciding a key comparison never
evaluates the auxiliary lexicographic product.-/
instance instLinearOrder : LinearOrder DirectionKey where
  le a b := toLexKey a ≤ toLexKey b
  lt a b := toLexKey a < toLexKey b
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
  le_antisymm _ _ h₁ h₂ := toLexKey_injective (le_antisymm h₁ h₂)
  le_total _ _ := le_total _ _
  toDecidableLE a b := decidable_of_iff (ble a b = true) (ble_iff_lex a b)
  toDecidableLT a b := decidable_of_iff (blt a b = true) (blt_iff_lex a b)
  toDecidableEq := instDecidableEqDirectionKey

/--
@isnad1 id=iff.0h2v.s4.0dfc7d820699 from=translated src=- shape=3e008c5a vocab=8f5088dd
-/
theorem lt_iff_blt (a b : DirectionKey) : a < b ↔ blt a b = true :=
  (blt_iff_lex a b).symm

/--
@isnad1 id=iff.0h2v.s4.6f5b36aaa586 from=translated src=- shape=3e008c5a vocab=c8dfe766
-/
theorem le_iff_ble (a b : DirectionKey) : a ≤ b ↔ ble a b = true :=
  (ble_iff_lex a b).symm

/-- The order on keys is the lexicographic order of the four components.
@isnad1 id=iff.0h2v.s6.1e08f48bc1c2 from=translated src=- shape=3c4e2ee7 vocab=7ce48499
-/
theorem lt_iff (a b : DirectionKey) :
    a < b ↔ a.form < b.form ∨ (a.form = b.form ∧ (a.x < b.x ∨ (a.x = b.x ∧
      (a.y < b.y ∨ (a.y = b.y ∧ a.z < b.z))))) := by
  rw [lt_iff_blt]
  simp only [blt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

/-- The first component of a key is monotone.
@isnad1 id=le.1h2v.s4.b03402709fec from=translated src=- shape=d7721dd6 vocab=2a39564b
-/
theorem form_le_of_le {a b : DirectionKey} (h : a ≤ b) : a.form ≤ b.form := by
  rcases lt_or_ge b a with hba | hab
  · exact absurd (lt_of_lt_of_le hba h) (lt_irrefl _)
  · rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_refl _
    · rcases (lt_iff a b).mp hlt with hform | ⟨hform, _⟩
      · exact hform.le
      · exact hform.le

end DirectionKey

noncomputable def directionKey (v : Triple) : DirectionKey :=
  ⟨qForm (primitiveDirection v), (primitiveDirection v).x,
    (primitiveDirection v).y, (primitiveDirection v).z⟩

/--
@isnad1 id=iff.0h2v.s4.d7569b2c5673 from=translated src=- shape=ff28044b vocab=bfae2aed
-/
theorem directionKey_eq_iff {v w : Triple} :
    directionKey v = directionKey w ↔ primitiveDirection v = primitiveDirection w := by
  constructor
  · intro h
    apply Triple.ext
    · exact congrArg DirectionKey.x h
    · exact congrArg DirectionKey.y h
    · exact congrArg DirectionKey.z h
  · intro h
    simp [directionKey, h]

/--
@isnad1 id=eq.1h1v.s4.92f76f3a93d6 from=translated src=- shape=a295f240 vocab=f0c7e40c
-/
@[simp] theorem directionKey_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (negTriple v) = directionKey v := by
  simp [directionKey, primitiveDirection_negTriple hv]

def residualSourceLift {n : ℤ} (s : BResidual n) : Triple := bLift s.1

def residualTargetLift {n : ℤ} (t : AResidual n) : Triple := aLift t.1

def plusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  vadd (residualSourceLift s) (residualTargetLift t)

def minusVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  vsub (residualSourceLift s) (residualTargetLift t)

/--
@isnad1 id=ne.0h3v.s4.702bc6e0a955 from=translated src=- shape=2f489a85 vocab=9f40ad62
-/
theorem plusVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    plusVector s t ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hz := congrArg Triple.z h
  obtain ⟨k, hk⟩ := s.1.2.2
  dsimp [plusVector, residualSourceLift, residualTargetLift, vadd, bLift, aLift] at hz
  omega

/--
@isnad1 id=ne.0h3v.s4.b6d80a17b67f from=translated src=- shape=2f489a85 vocab=a744bcd9
-/
theorem minusVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector s t ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hz := congrArg Triple.z h
  obtain ⟨k, hk⟩ := s.1.2.2
  dsimp [minusVector, residualSourceLift, residualTargetLift, vsub, bLift, aLift] at hz
  omega

/--
@isnad1 id=eq.0h3v.s4.d61412f6802d from=translated src=- shape=cafc7ea5 vocab=9b44c73c
-/
theorem plus_minus_orthogonal {n : ℤ} (s : BResidual n) (t : AResidual n) :
    qBilinear (plusVector s t) (minusVector s t) = 0 := by
  have hs := qForm_bLift s.1
  have ht := qForm_aLift t.1
  simp [plusVector, minusVector, residualSourceLift, residualTargetLift,
    qBilinear, vadd, vsub, qForm] at hs ht ⊢
  nlinarith

/-- The two signed midpoint lines have distinct primitive directions.
@isnad1 id=ne.0h3v.s4.539b25420b5b from=translated src=- shape=4be2047f vocab=536c3aaa
-/
theorem plus_minus_directions_ne {n : ℤ} (s : BResidual n) (t : AResidual n) :
    primitiveDirection (plusVector s t) ≠ primitiveDirection (minusVector s t) := by
  intro hdir
  let d := primitiveDirection (plusVector s t)
  let a := directionScale (plusVector s t)
  let b := directionScale (minusVector s t)
  have hplus : plusVector s t = vsmul a d := direction_decomposition _
  have hminus : minusVector s t = vsmul b d := by
    rw [direction_decomposition (minusVector s t), ← hdir]
  have ha : a ≠ 0 := directionScale_ne_zero (plusVector_ne_zero s t)
  have hb : b ≠ 0 := directionScale_ne_zero (minusVector_ne_zero s t)
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (plusVector_ne_zero s t)
  have horth := plus_minus_orthogonal s t
  rw [hplus, hminus, qBilinear_vsmul_vsmul] at horth
  have hq : qForm d ≠ 0 := ne_of_gt (qForm_pos_of_ne_zero hd)
  rcases mul_eq_zero.mp horth with hab | hq0
  · exact (mul_ne_zero ha hb) hab
  · exact hq hq0

/--
@isnad1 id=ne.0h3v.s4.4817a62bf00b from=translated src=- shape=4be2047f vocab=13836586
-/
theorem plus_minus_keys_ne {n : ℤ} (s : BResidual n) (t : AResidual n) :
    directionKey (plusVector s t) ≠ directionKey (minusVector s t) := by
  intro h
  exact plus_minus_directions_ne s t (directionKey_eq_iff.mp h)

noncomputable def representativeEdgeKey {n : ℤ} (s : BResidual n) (t : AResidual n) :
    DirectionKey :=
  min (directionKey (plusVector s t)) (directionKey (minusVector s t))

noncomputable def preferredVector {n : ℤ} (s : BResidual n) (t : AResidual n) : Triple :=
  if directionKey (plusVector s t) < directionKey (minusVector s t) then
    plusVector s t
  else
    minusVector s t

/--
@isnad1 id=or.0h3v.s4.4d2f414472ac from=translated src=- shape=9d66673e vocab=17c42778
-/
theorem preferredVector_eq_plus_or_minus {n : ℤ} (s : BResidual n) (t : AResidual n) :
    preferredVector s t = plusVector s t ∨ preferredVector s t = minusVector s t := by
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · exact Or.inl (by simp [preferredVector, h])
  · exact Or.inr (by simp [preferredVector, h])

/--
@isnad1 id=ne.0h3v.s4.a8b2031529f9 from=translated src=- shape=2f489a85 vocab=e88c247c
-/
theorem preferredVector_ne_zero {n : ℤ} (s : BResidual n) (t : AResidual n) :
    preferredVector s t ≠ ⟨0, 0, 0⟩ := by
  rcases preferredVector_eq_plus_or_minus s t with h | h
  · rw [h]
    exact plusVector_ne_zero s t
  · rw [h]
    exact minusVector_ne_zero s t

/--
@isnad1 id=eq.1h1v.s4.a7884d118650 from=translated src=- shape=a295f240 vocab=f97ccded
-/
@[simp] theorem directionKey_primitiveDirection {v : Triple}
    (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (primitiveDirection v) = directionKey v := by
  rw [directionKey_eq_iff]
  exact primitiveDirection_idem hv

/--
@isnad1 id=eq.0h3v.s4.ffc73d32cdb8 from=translated src=- shape=6bd14a94 vocab=4335cbc7
-/
theorem representativeEdgeKey_eq_preferred {n : ℤ} (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s t = directionKey (preferredVector s t) := by
  by_cases h : directionKey (plusVector s t) < directionKey (minusVector s t)
  · simp [representativeEdgeKey, preferredVector, h, min_eq_left h.le]
  · have hle : directionKey (minusVector s t) < directionKey (plusVector s t) :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (plus_minus_keys_ne s t))
    simp [representativeEdgeKey, preferredVector, h, min_eq_right hle.le]

/--
@isnad1 id=eq.0h3v.s4.889e3dc62078 from=translated src=- shape=56924023 vocab=22baf2c9
-/
@[simp] theorem plusVector_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    plusVector (negBResidual s) t = negTriple (minusVector s t) := by
  ext <;> simp [plusVector, minusVector, residualSourceLift, residualTargetLift,
    vadd, vsub, bLift, aLift, negBResidual, negBOdd, negTriple] <;> ring

/--
@isnad1 id=eq.0h3v.s4.1dd3abe7bb29 from=translated src=- shape=56924023 vocab=22baf2c9
-/
@[simp] theorem minusVector_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector (negBResidual s) t = negTriple (plusVector s t) := by
  ext <;> simp [plusVector, minusVector, residualSourceLift, residualTargetLift,
    vadd, vsub, bLift, aLift, negBResidual, negBOdd, negTriple] <;> ring

/--
@isnad1 id=eq.0h3v.s4.604f30761d60 from=translated src=- shape=80d2b824 vocab=3c37000c
-/
@[simp] theorem plusVector_neg_target {n : ℤ} (s : BResidual n) (t : AResidual n) :
    plusVector s (negAResidual t) = minusVector s t := by
  ext <;> simp [plusVector, minusVector, residualSourceLift, residualTargetLift,
    vadd, vsub, bLift, aLift, negAResidual, negA, negTriple] <;> ring

/--
@isnad1 id=eq.0h3v.s4.9c0e33ece819 from=translated src=- shape=80d2b824 vocab=3c37000c
-/
@[simp] theorem minusVector_neg_target {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector s (negAResidual t) = plusVector s t := by
  ext <;> simp [plusVector, minusVector, residualSourceLift, residualTargetLift,
    vadd, vsub, bLift, aLift, negAResidual, negA, negTriple]

/--
@isnad1 id=eq.0h3v.s4.7a83d2f71421 from=translated src=- shape=81ca4e64 vocab=2d192315
-/
@[simp] theorem representativeEdgeKey_neg_source {n : ℤ}
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey (negBResidual s) t = representativeEdgeKey s t := by
  rw [representativeEdgeKey, plusVector_neg_source, minusVector_neg_source,
    directionKey_negTriple (minusVector_ne_zero s t),
    directionKey_negTriple (plusVector_ne_zero s t), representativeEdgeKey, min_comm]

/--
@isnad1 id=eq.0h3v.s4.77381787ed01 from=translated src=- shape=cd60d55a vocab=ea77cd36
-/
@[simp] theorem representativeEdgeKey_neg_target {n : ℤ}
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s (negAResidual t) = representativeEdgeKey s t := by
  simp [representativeEdgeKey, min_comm]

/--
@isnad1 id=eq.3h4v.s6.420bfa055deb from=translated src=- shape=c1ad682c vocab=12072137
-/
theorem endpoint_scale_equation {E F d : Triple} {a : ℤ}
    (hnorm : qForm F = qForm E) (ha : a ≠ 0)
    (hline : vadd E F = vsmul a d ∨ vsub E F = vsmul a d) :
    a * qForm d = 2 * qBilinear E d := by
  have hfactor : a * (a * qForm d - 2 * qBilinear E d) = 0 := by
    rcases hline with hplus | hminus
    · have hx := congrArg Triple.x hplus
      have hy := congrArg Triple.y hplus
      have hz := congrArg Triple.z hplus
      simp [vadd, vsmul] at hx hy hz
      have hfx : F.x = a * d.x - E.x := by linarith
      have hfy : F.y = a * d.y - E.y := by linarith
      have hfz : F.z = a * d.z - E.z := by linarith
      simp [qForm] at hnorm
      rw [hfx, hfy, hfz] at hnorm
      change a * (a * (2 * d.x ^ 2 + d.y ^ 2 + 2 * d.z ^ 2) -
        2 * (2 * E.x * d.x + E.y * d.y + 2 * E.z * d.z)) = 0
      ring_nf at hnorm ⊢
      linear_combination hnorm
    · have hx := congrArg Triple.x hminus
      have hy := congrArg Triple.y hminus
      have hz := congrArg Triple.z hminus
      simp [vsub, vsmul] at hx hy hz
      have hfx : F.x = E.x - a * d.x := by linarith
      have hfy : F.y = E.y - a * d.y := by linarith
      have hfz : F.z = E.z - a * d.z := by linarith
      simp [qForm] at hnorm
      rw [hfx, hfy, hfz] at hnorm
      change a * (a * (2 * d.x ^ 2 + d.y ^ 2 + 2 * d.z ^ 2) -
        2 * (2 * E.x * d.x + E.y * d.y + 2 * E.z * d.z)) = 0
      ring_nf at hnorm ⊢
      linear_combination hnorm
  have hzero := (mul_eq_zero.mp hfactor).resolve_left ha
  linarith

/-- At a fixed endpoint and on a fixed nonzero direction, equal-norm opposite
endpoints are unique up to sign.
@isnad1 id=or.7h6v.s6.83f4a66cd044 from=translated src=- shape=ec4dda3f vocab=43c7e7d6
-/
theorem fixed_endpoint_line_unique {E F₁ F₂ d : Triple} {a b : ℤ}
    (hnorm₁ : qForm F₁ = qForm E) (hnorm₂ : qForm F₂ = qForm E)
    (hd : d ≠ ⟨0, 0, 0⟩) (ha : a ≠ 0) (hb : b ≠ 0)
    (hline₁ : vadd E F₁ = vsmul a d ∨ vsub E F₁ = vsmul a d)
    (hline₂ : vadd E F₂ = vsmul b d ∨ vsub E F₂ = vsmul b d) :
    F₂ = F₁ ∨ F₂ = negTriple F₁ := by
  have haeq := endpoint_scale_equation hnorm₁ ha hline₁
  have hbeq := endpoint_scale_equation hnorm₂ hb hline₂
  have hq : qForm d ≠ 0 := ne_of_gt (qForm_pos_of_ne_zero hd)
  have hab : a = b := by
    apply mul_right_cancel₀ hq
    exact haeq.trans hbeq.symm
  subst b
  rcases hline₁ with hplus₁ | hminus₁ <;>
    rcases hline₂ with hplus₂ | hminus₂
  · left
    apply Triple.ext
    · have h₁ := congrArg Triple.x hplus₁
      have h₂ := congrArg Triple.x hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.y hplus₁
      have h₂ := congrArg Triple.y hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.z hplus₁
      have h₂ := congrArg Triple.z hplus₂
      simp [vadd, vsmul] at h₁ h₂
      linarith
  · right
    apply Triple.ext
    · have h₁ := congrArg Triple.x hplus₁
      have h₂ := congrArg Triple.x hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.y hplus₁
      have h₂ := congrArg Triple.y hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.z hplus₁
      have h₂ := congrArg Triple.z hminus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
  · right
    apply Triple.ext
    · have h₁ := congrArg Triple.x hminus₁
      have h₂ := congrArg Triple.x hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.y hminus₁
      have h₂ := congrArg Triple.y hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
    · have h₁ := congrArg Triple.z hminus₁
      have h₂ := congrArg Triple.z hplus₂
      simp [vadd, vsub, vsmul, negTriple] at h₁ h₂ ⊢
      linarith
  · left
    apply Triple.ext
    · have h₁ := congrArg Triple.x hminus₁
      have h₂ := congrArg Triple.x hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.y hminus₁
      have h₂ := congrArg Triple.y hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith
    · have h₁ := congrArg Triple.z hminus₁
      have h₂ := congrArg Triple.z hminus₂
      simp [vsub, vsmul] at h₁ h₂
      linarith

/--
@isnad1 id=injectiv.0h1v.s3.e053abc1406f from=translated src=- shape=64d36d98 vocab=8bcc6048
-/
theorem residualTargetLift_injective {n : ℤ} :
    Function.Injective (residualTargetLift : AResidual n → Triple) := by
  intro t₁ t₂ h
  apply Subtype.ext
  apply Subtype.ext
  apply Triple.ext
  · have hx := congrArg Triple.x h
    simpa [residualTargetLift, aLift] using hx
  · have hy := congrArg Triple.y h
    simpa [residualTargetLift, aLift] using hy
  · have hz := congrArg Triple.z h
    simp [residualTargetLift, aLift] at hz
    linarith

/--
@isnad1 id=eq.0h2v.s4.83743a68e262 from=translated src=- shape=46892f85 vocab=7c954349
-/
@[simp] theorem residualTargetLift_neg {n : ℤ} (t : AResidual n) :
    residualTargetLift (negAResidual t) = negTriple (residualTargetLift t) := by
  ext <;> simp [residualTargetLift, aLift, negAResidual, negA, negTriple]

/--
@isnad1 id=injectiv.0h1v.s3.6f3f5299ccb7 from=translated src=- shape=64d36d98 vocab=d555094c
-/
theorem residualSourceLift_injective {n : ℤ} :
    Function.Injective (residualSourceLift : BResidual n → Triple) := by
  intro s₁ s₂ h
  apply Subtype.ext
  apply Subtype.ext
  apply Triple.ext
  · have hx := congrArg Triple.x h
    simpa [residualSourceLift, bLift] using hx
  · have hy := congrArg Triple.y h
    simpa [residualSourceLift, bLift] using hy
  · have hz := congrArg Triple.z h
    simp [residualSourceLift, bLift] at hz
    linarith

/--
@isnad1 id=eq.0h2v.s4.b51605430706 from=translated src=- shape=46892f85 vocab=1145bfe4
-/
@[simp] theorem residualSourceLift_neg {n : ℤ} (s : BResidual n) :
    residualSourceLift (negBResidual s) = negTriple (residualSourceLift s) := by
  ext <;> simp [residualSourceLift, bLift, negBResidual, negBOdd, negTriple]

/-- At a fixed residual source, equal preferred keys determine the target
orbit.  This is the source half of Proposition 4.2.
@isnad1 id=eq.2h4v.s5.aeb898d159d8 from=translated src=- shape=69bfcea4 vocab=21a63d4d
-/
theorem representativeEdgeKey_source_orbit_injective {n : ℤ}
    (hnpos : 0 < n) (s : BResidual n) {t₁ t₂ : AResidual n}
    (hkey : representativeEdgeKey s t₁ = representativeEdgeKey s t₂) :
    (aResidualInvolution n hnpos).orbit t₁ =
      (aResidualInvolution n hnpos).orbit t₂ := by
  rw [representativeEdgeKey_eq_preferred, representativeEdgeKey_eq_preferred] at hkey
  have hdir : primitiveDirection (preferredVector s t₁) =
      primitiveDirection (preferredVector s t₂) := directionKey_eq_iff.mp hkey
  let d := primitiveDirection (preferredVector s t₁)
  let a := directionScale (preferredVector s t₁)
  let b := directionScale (preferredVector s t₂)
  have hp₁ := preferredVector_eq_plus_or_minus s t₁
  have hp₂ := preferredVector_eq_plus_or_minus s t₂
  have hdec₁ : preferredVector s t₁ = vsmul a d := direction_decomposition _
  have hdec₂ : preferredVector s t₂ = vsmul b d := by
    have h := direction_decomposition (preferredVector s t₂)
    rw [← hdir] at h
    exact h
  have hline₁ : plusVector s t₁ = vsmul a d ∨ minusVector s t₁ = vsmul a d :=
    hp₁.elim (fun h => Or.inl (h.symm.trans hdec₁))
      (fun h => Or.inr (h.symm.trans hdec₁))
  have hline₂ : plusVector s t₂ = vsmul b d ∨ minusVector s t₂ = vsmul b d :=
    hp₂.elim (fun h => Or.inl (h.symm.trans hdec₂))
      (fun h => Or.inr (h.symm.trans hdec₂))
  have ha : a ≠ 0 := directionScale_ne_zero (by
    rcases hp₁ with h | h
    · rw [h]; exact plusVector_ne_zero s t₁
    · rw [h]; exact minusVector_ne_zero s t₁)
  have hb : b ≠ 0 := directionScale_ne_zero (by
    rcases hp₂ with h | h
    · rw [h]; exact plusVector_ne_zero s t₂
    · rw [h]; exact minusVector_ne_zero s t₂)
  have hd : d ≠ ⟨0, 0, 0⟩ := primitiveDirection_ne_zero (by
    rcases preferredVector_eq_plus_or_minus s t₁ with h | h
    · rw [h]; exact plusVector_ne_zero s t₁
    · rw [h]; exact minusVector_ne_zero s t₁)
  have hnorm₁ : qForm (residualTargetLift t₁) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have hnorm₂ : qForm (residualTargetLift t₂) = qForm (residualSourceLift s) := by
    simp [residualTargetLift, residualSourceLift]
  have horbit := fixed_endpoint_line_unique hnorm₁ hnorm₂ hd ha hb hline₁ hline₂
  let AI := aResidualInvolution n hnpos
  rcases horbit with hsame | hneg
  · have : t₂ = t₁ := residualTargetLift_injective hsame
    subst t₂
    rfl
  · have : t₂ = negAResidual t₁ := by
      apply residualTargetLift_injective
      simpa using hneg
    rw [this]
    exact (AI.orbit_neg t₁).symm

/--
@isnad1 id=ex.0h3v.s5.c29789de662c from=translated src=- shape=8bafb9d8 vocab=ec318b0e
-/
theorem preferred_fixed_target_line {n : ℤ} (s : BResidual n) (t : AResidual n) :
    ∃ c : ℤ, c ≠ 0 ∧
      (vadd (residualTargetLift t) (residualSourceLift s) =
          vsmul c (primitiveDirection (preferredVector s t)) ∨
       vsub (residualTargetLift t) (residualSourceLift s) =
          vsmul c (primitiveDirection (preferredVector s t))) := by
  let a := directionScale (preferredVector s t)
  have hdec : preferredVector s t =
      vsmul a (primitiveDirection (preferredVector s t)) := direction_decomposition _
  have ha : a ≠ 0 := directionScale_ne_zero (by
    rcases preferredVector_eq_plus_or_minus s t with h | h
    · rw [h]; exact plusVector_ne_zero s t
    · rw [h]; exact minusVector_ne_zero s t)
  rcases preferredVector_eq_plus_or_minus s t with hplus | hminus
  · refine ⟨a, ha, Or.inl ?_⟩
    rw [vadd_comm]
    exact hplus.symm.trans hdec
  · refine ⟨-a, neg_ne_zero.mpr ha, Or.inr ?_⟩
    have hraw : minusVector s t =
        vsmul a (primitiveDirection (preferredVector s t)) := hminus.symm.trans hdec
    calc
      vsub (residualTargetLift t) (residualSourceLift s) =
          negTriple (minusVector s t) := by rw [vsub_swap]; rfl
      _ = negTriple (vsmul a (primitiveDirection (preferredVector s t))) :=
        congrArg negTriple hraw
      _ = vsmul (-a) (primitiveDirection (preferredVector s t)) := by
        ext <;> simp [negTriple, vsmul]

/-- At a fixed residual target, equal preferred keys determine the source
orbit.  Together with the source statement this proves Proposition 4.2.
@isnad1 id=eq.1h4v.s5.84e48f3cb639 from=translated src=- shape=4e7b93da vocab=aa379051
-/
theorem representativeEdgeKey_target_orbit_injective {n : ℤ}
    (t : AResidual n) {s₁ s₂ : BResidual n}
    (hkey : representativeEdgeKey s₁ t = representativeEdgeKey s₂ t) :
    (bResidualInvolution n).orbit s₁ = (bResidualInvolution n).orbit s₂ := by
  rw [representativeEdgeKey_eq_preferred, representativeEdgeKey_eq_preferred] at hkey
  have hdir : primitiveDirection (preferredVector s₁ t) =
      primitiveDirection (preferredVector s₂ t) := directionKey_eq_iff.mp hkey
  obtain ⟨a, ha, hline₁⟩ := preferred_fixed_target_line s₁ t
  obtain ⟨b, hb, hline₂⟩ := preferred_fixed_target_line s₂ t
  rw [← hdir] at hline₂
  have hd : primitiveDirection (preferredVector s₁ t) ≠ ⟨0, 0, 0⟩ :=
    primitiveDirection_ne_zero (by
      rcases preferredVector_eq_plus_or_minus s₁ t with h | h
      · rw [h]; exact plusVector_ne_zero s₁ t
      · rw [h]; exact minusVector_ne_zero s₁ t)
  have hnorm₁ : qForm (residualSourceLift s₁) = qForm (residualTargetLift t) := by
    simp [residualSourceLift, residualTargetLift]
  have hnorm₂ : qForm (residualSourceLift s₂) = qForm (residualTargetLift t) := by
    simp [residualSourceLift, residualTargetLift]
  have horbit := fixed_endpoint_line_unique hnorm₁ hnorm₂ hd ha hb hline₁ hline₂
  let BI := bResidualInvolution n
  rcases horbit with hsame | hneg
  · have : s₂ = s₁ := residualSourceLift_injective hsame
    subst s₂
    rfl
  · have : s₂ = negBResidual s₁ := by
      apply residualSourceLift_injective
      simpa using hneg
    rw [this]
    exact (BI.orbit_neg s₁).symm

end TunnellMap
