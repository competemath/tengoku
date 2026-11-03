import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.OpenGridIdentity
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eq_zero_of_localizedConstantEval_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms extensionEval_eq_zero_of_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-! Open-grid detection in any chosen model of a principal localization. -/

noncomputable section
namespace AlbertLean.Generic.LocalizedGridIdentity

universe u v w z
variable {σ : Type u}
variable (k : Type v) (K : Type w)
variable [Field k] [Infinite k] [Field K] [Algebra k K]

abbrev Base := MvPolynomial σ K

def mappedDenominator (D : MvPolynomial σ k) : Base (σ := σ) K :=
  D.map (algebraMap k K)

/-- A concrete localization remains available as a convenience, but the main
theorem accepts any localization model `S`.-/
abbrev AwayRing (D : MvPolynomial σ k) :=
  Localization.Away (mappedDenominator k K D)

def constantEval (t : σ → k) : Base (σ := σ) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K) (fun i => algebraMap k K (t i))

theorem constantEval_mappedDenominator (D : MvPolynomial σ k) (t : σ → k) :
    constantEval k K t (mappedDenominator k K D) =
      algebraMap k K (MvPolynomial.eval t D) := by
  simp [constantEval, mappedDenominator, MvPolynomial.map_eval, Function.comp_def]

variable (S : Type z) [CommRing S] [Algebra (Base (σ := σ) K) S]

/-- Legal evaluation from an arbitrary model of the localization.-/
def localizedConstantEval (D : MvPolynomial σ k)
    [IsLocalization.Away (mappedDenominator k K D) S]
    (t : σ → k) (ht : MvPolynomial.eval t D ≠ 0) : S →+* K :=
  IsLocalization.Away.lift (mappedDenominator k K D)
    (show IsUnit (constantEval k K t (mappedDenominator k K D)) by
      rw [constantEval_mappedDenominator]
      apply isUnit_iff_ne_zero.mpr
      simpa only [map_zero] using (algebraMap k K).injective.ne ht)

@[simp] theorem localizedConstantEval_algebraMap
    (D : MvPolynomial σ k)
    [IsLocalization.Away (mappedDenominator k K D) S]
    (t : σ → k) (ht : MvPolynomial.eval t D ≠ 0) (P : Base (σ := σ) K) :
    localizedConstantEval k K S D t ht (algebraMap (Base (σ := σ) K) S P) =
      constantEval k K t P := by
  exact IsLocalization.Away.lift_eq (mappedDenominator k K D) _ P

/-- Legal embedded-base evaluations jointly detect zero in every model of
the localization away from the mapped base polynomial.-/
theorem eq_zero_of_localizedConstantEval_eq_zero
    (D : MvPolynomial σ k) (hD : D ≠ 0)
    [IsLocalization.Away (mappedDenominator k K D) S]
    (x : S)
    (hx : ∀ (t : σ → k) (ht : MvPolynomial.eval t D ≠ 0),
      localizedConstantEval k K S D t ht x = 0) :
    x = 0 := by
  let d : Base (σ := σ) K := mappedDenominator k K D
  let s := IsLocalization.Away.sec d x
  have hs : x * algebraMap (Base (σ := σ) K) S (d ^ s.2) =
      algebraMap (Base (σ := σ) K) S s.1 := IsLocalization.Away.sec_spec d x
  have hs1 : s.1 = 0 := by
    apply OpenGridIdentity.eq_zero_of_eval_algebraMap_eq_zero_of_denominator_ne_zero
      D s.1 hD
    intro t ht
    let ev := localizedConstantEval k K S D t ht
    have hev := congrArg ev hs
    have hx0 : ev x = 0 := hx t ht
    change constantEval k K t s.1 = 0
    simpa [ev, d, s, hx0] using hev.symm
  rw [hs1, map_zero] at hs
  have hu : IsUnit (algebraMap (Base (σ := σ) K) S (d ^ s.2)) :=
    by simpa only [map_pow] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := S) d s.2)
  exact hu.mul_right_injective (by simpa [mul_comm] using hs)

variable {E : Type*} [Field E]

/-- An arbitrary coefficient-field evaluation, when the mapped denominator
is a unit.-/
def extensionEval (D : MvPolynomial σ k)
    [IsLocalization.Away (mappedDenominator k K D) S]
    (φ : K →+* E) (b : σ → E)
    (hDunit : IsUnit
      (MvPolynomial.eval₂Hom φ b (mappedDenominator k K D))) : S →+* E :=
  IsLocalization.Away.lift (mappedDenominator k K D) hDunit

theorem extensionEval_eq_zero_of_eq_zero
    (D : MvPolynomial σ k)
    [IsLocalization.Away (mappedDenominator k K D) S]
    (x : S) (hx : x = 0) (φ : K →+* E) (b : σ → E)
    (hDunit : IsUnit
      (MvPolynomial.eval₂Hom φ b (mappedDenominator k K D))) :
    extensionEval k K S D φ b hDunit x = 0 := by
  rw [hx, map_zero]

end AlbertLean.Generic.LocalizedGridIdentity
