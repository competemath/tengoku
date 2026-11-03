import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticPartnerAlignment
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticFixedWord

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms firstAlignment_preserves` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fourStepPairWord_source` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fourStepPairWord_partner` (it only prints; the queue checks the axioms of every declaration). -/

/-! Four transvections align one hyperbolic pair: two for its first vector and
two for its partner.  The hypotheses expose exactly the detour pivot needed
for the first vector; no root extension or rank argument occurs. -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def firstAlignment
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) : V ≃ₗ[K] V :=
  (equiv omega halt (z - x) (omega z x)⁻¹).trans
    (equiv omega halt (y - z) (omega y z)⁻¹)

/--
@isnad1 id=eq.3h7v.s11.3e4db273e6b9 from=translated src=- shape=a25f63f1 vocab=c91156a4
-/
@[simp] theorem firstAlignment_apply
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) (q : V) :
    firstAlignment omega halt x z y hxz hzy q =
      equiv omega halt (y - z) (omega y z)⁻¹
        (equiv omega halt (z - x) (omega z x)⁻¹ q) := rfl

/--
@isnad1 id=eq.3h6v.s10.092e0a8d52ad from=translated src=- shape=5ceade0e vocab=45b8305c
-/
theorem firstAlignment_source
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) :
    firstAlignment omega halt x z y hxz hzy x = y :=
  two_step_align omega halt x z y hxz hzy

/--
@isnad1 id=eq.3h8v.s11.dc65c0bcc33e from=translated src=- shape=4b5c7e0f vocab=45b8305c
-/
theorem firstAlignment_preserves
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) (q r : V) :
    omega (firstAlignment omega halt x z y hxz hzy q)
      (firstAlignment omega halt x z y hxz hzy r) = omega q r := by
  rw [firstAlignment_apply, firstAlignment_apply,
    equiv_preserves, equiv_preserves]

def fourStepPairWord
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y v f : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0) :
    List (Step (K := K) (V := V)) :=
  let vp := firstAlignment omega halt x z y hxz hzy v
  let a := avoidanceScalar (omega f vp)
  let w := vp + a • y
  [(f - w, (omega f w)⁻¹), (w - vp, (omega w vp)⁻¹),
    (y - z, (omega y z)⁻¹), (z - x, (omega z x)⁻¹)]

/--
@isnad1 id=eq.5h8v.s11.4dd07a1d87d7 from=translated src=- shape=3a6d3e73 vocab=2a2c4810
-/
theorem fourStepPairWord_source
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y v f : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0)
    (hxv : omega x v = 1) (hyf : omega y f = 1) :
    wordMap omega (fourStepPairWord omega halt x z y v f hxz hzy) x = y := by
  let vp := firstAlignment omega halt x z y hxz hzy v
  have hyp : omega y vp = 1 := by
    rw [← firstAlignment_source omega halt x z y hxz hzy,
      firstAlignment_preserves, hxv]
  change equiv omega halt
      (f - (vp + avoidanceScalar (omega f vp) • y))
      (omega f (vp + avoidanceScalar (omega f vp) • y))⁻¹
    (equiv omega halt
      ((vp + avoidanceScalar (omega f vp) • y) - vp)
      (omega (vp + avoidanceScalar (omega f vp) • y) vp)⁻¹
      (firstAlignment omega halt x z y hxz hzy x)) = y
  rw [firstAlignment_source]
  exact partner_two_step_fixes_first omega halt y vp f hyp hyf

/--
@isnad1 id=eq.5h8v.s11.a2193ea425d4 from=translated src=- shape=0b62c9c7 vocab=2a2c4810
-/
theorem fourStepPairWord_partner
    (omega : BilinForm (K := K) (V := V))
    (halt : ∀ x, omega x x = 0) (x z y v f : V)
    (hxz : omega z x ≠ 0) (hzy : omega y z ≠ 0)
    (hxv : omega x v = 1) (hyf : omega y f = 1) :
    wordMap omega (fourStepPairWord omega halt x z y v f hxz hzy) v = f := by
  let vp := firstAlignment omega halt x z y hxz hzy v
  have hyp : omega y vp = 1 := by
    rw [← firstAlignment_source omega halt x z y hxz hzy,
      firstAlignment_preserves, hxv]
  change equiv omega halt
      (f - (vp + avoidanceScalar (omega f vp) • y))
      (omega f (vp + avoidanceScalar (omega f vp) • y))⁻¹
    (equiv omega halt
      ((vp + avoidanceScalar (omega f vp) • y) - vp)
      (omega (vp + avoidanceScalar (omega f vp) • y) vp)⁻¹ vp) = f
  exact partner_two_step_align omega halt y vp f hyp hyf

end AlbertLean.Generic.SymplecticTransvection
