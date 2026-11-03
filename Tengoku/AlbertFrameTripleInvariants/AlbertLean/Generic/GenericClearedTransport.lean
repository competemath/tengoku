import Tengoku.Seed.Algebra.Field.Equiv
import Tengoku.Seed.Algebra.GroupWithZero.Units.Lemmas
import Tengoku.Seed.Algebra.Ring.Equiv
import Tengoku.Seed.RingTheory.SimpleRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms injective_of_evaluation_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ratio_fixed_comp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ratio_fixed_inverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms agreement_of_generic_cleared_transport` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Generic algebra for composing cleared invariant identities before evaluating
an actual configuration. The intended consumer is the quaternion raw
coefficient/evaluation square and its elementary-generator comparison.
No intermediate pointwise denominator is assumed nonzero.
-/

namespace AlbertLean.Generic.GenericClearedTransport

/-- An evaluation square with an injective bottom composite certifies that
the coefficient map into the independent raw ring is injective.-/
theorem injective_of_evaluation_square
    {R S F L : Type*} [CommRing R] [CommRing S] [Field F] [Field L]
    (i : R →+* F) (hi : Function.Injective i)
    (j : R →+* S) (e : S →+* L) (φ : F →+* L)
    (h : e.comp j = φ.comp i) : Function.Injective j := by
  intro x y hxy
  apply hi
  apply φ.injective
  have hx : e (j x) = φ (i x) := DFunLike.congr_fun h x
  have hy : e (j y) = φ (i y) := DFunLike.congr_fun h y
  rw [← hx, ← hy, hxy]

/-- Cleared invariance is closed under composition in the independent
domain. The inner action is `β`, and the outer action is `α`.-/
theorem ratio_fixed_comp
    {S : Type*} [CommRing S] [IsDomain S]
    (a b : S) (hb : b ≠ 0) (α β : S ≃+* S)
    (hα : α a * b = a * α b)
    (hβ : β a * b = a * β b) :
    α (β a) * b = a * α (β b) := by
  have hαb : α b ≠ 0 := by
    simpa only [map_zero] using α.injective.ne hb
  have hαβ : α (β a) * α b = α a * α (β b) := by
    simpa only [map_mul] using congrArg α hβ
  apply mul_right_cancel₀ hαb
  calc
    (α (β a) * b) * α b = (α (β a) * α b) * b :=
      mul_right_comm _ _ _
    _ = (α a * α (β b)) * b := by rw [hαβ]
    _ = (α a * b) * α (β b) := mul_right_comm _ _ _
    _ = (a * α b) * α (β b) := by rw [hα]
    _ = (a * α (β b)) * α b := mul_right_comm _ _ _

/-- A genuine inverse preserves the same cleared ratio. This needs no
nonzero-denominator premise and supports reversing normalizing actions.-/
theorem ratio_fixed_inverse
    {S : Type*} [CommRing S]
    (a b : S) (α : S ≃+* S)
    (hα : α a * b = a * α b) :
    α.symm a * b = a * α.symm b := by
  apply α.injective
  simpa only [map_mul, RingEquiv.apply_symm_apply] using hα.symm

/-- Evaluate only the final cleared identity. The two endpoint denominators
are nonzero because they are images under field embeddings of the original
nonzero denominator. No domain or injectivity premise is needed for the
evaluation map or its source ring.-/
theorem agreement_of_generic_cleared_transport
    {R S F L : Type*} [CommRing R] [CommRing S] [Field F] [Field L]
    (i : R →+* F) (j : R →+* S) (e : S →+* L)
    (φ ψ : F →+* L) (α : S ≃+* S)
    (hleft : e.comp j = φ.comp i)
    (hright : (e.comp α.toRingHom).comp j = ψ.comp i)
    (a b : R) (hb : i b ≠ 0)
    (hclear : α (j a) * j b = j a * α (j b)) :
    φ (i a / i b) = ψ (i a / i b) := by
  have hl (x : R) : e (j x) = φ (i x) :=
    DFunLike.congr_fun hleft x
  have hr (x : R) : e (α (j x)) = ψ (i x) :=
    DFunLike.congr_fun hright x
  have h := congrArg e hclear
  simp only [map_mul] at h
  rw [hr a, hl b, hl a, hr b] at h
  have hφb : φ (i b) ≠ 0 := by
    simpa only [map_zero] using φ.injective.ne hb
  have hψb : ψ (i b) ≠ 0 := by
    simpa only [map_zero] using ψ.injective.ne hb
  rw [map_div₀, map_div₀]
  exact (div_eq_div_iff hφb hψb).2 h.symm

end AlbertLean.Generic.GenericClearedTransport
