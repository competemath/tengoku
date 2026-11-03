import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FiniteQuadraticRoots
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms away_isTorsionFree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms quadraticRootEval_omega` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms rootOmega_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms quadraticRootAwayEval_rootOmega` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms quadraticRootAway_nontrivial` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms quadraticRootAway_isTorsionFree` (it only prints; the queue checks the axioms of every declaration). -/

/-! Torsion-freeness across a localization whose denominator survives at a
field point, followed by one concrete quadratic-root localization step. -/

noncomputable section
namespace AlbertLean.Generic.GenericRootAwayTorsionFree

universe u v

/-- Arbitrary localization preserves torsion-freeness over the base, even if
the localized algebra is the zero ring.  No domain hypothesis on `B` or `S`
and no nonvanishing hypothesis on `D` is used.
@isnad1 id=istorsio.0h4v.s7.bc1f1de30aa2 from=translated src=- shape=6e6b7a50 vocab=e43b8fd5
-/
theorem away_isTorsionFree
    {A B S : Type u} [CommRing A] [IsDomain A] [CommRing B] [CommRing S]
    [Algebra A B] [Module.IsTorsionFree A B]
    [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (D : B) [IsLocalization.Away D S] :
    Module.IsTorsionFree A S := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a z haz
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨n, b, hzb⟩ := IsLocalization.Away.surj D z
  have habmap : algebraMap B S (a • b) = 0 := by
    calc
      algebraMap B S (a • b) = a • algebraMap B S b :=
        map_smul (IsScalarTower.toAlgHom A B S) a b
      _ = a • (z * algebraMap B S D ^ n) := by rw [hzb]
      _ = (a • z) * algebraMap B S D ^ n := (smul_mul_assoc a z _).symm
      _ = 0 := by rw [haz, zero_mul]
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq D
    (habmap.trans (map_zero (algebraMap B S)).symm)
  have hab : a • (D ^ m * b) = 0 := by
    simpa only [Algebra.smul_def, mul_zero, mul_assoc, mul_comm, mul_left_comm]
      using hm
  have hDb : D ^ m * b = 0 :=
    ((Module.isTorsionFree_iff_smul_eq_zero.mp inferInstance)
      a (D ^ m * b) hab).resolve_left ha
  have hb : algebraMap B S b = 0 := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit (S := S) D m).mul_left_cancel
    simpa only [← map_pow, ← map_mul, hDb, map_zero, mul_zero]
  apply (IsLocalization.Away.algebraMap_pow_isUnit (S := S) D n).mul_left_cancel
  rw [mul_comm (algebraMap B S D ^ n) z, hzb, hb, mul_zero]

variable {A B : Type u} [CommRing A] [IsDomain A] [CommRing B]
  [Algebra A B] [Module.IsTorsionFree A B]
variable {L : Type v} [Field L]

abbrev QuadraticRootRing (c : B) := QuadraticAlgebra B c 0

abbrev QuadraticRootAway (c : B) (D : QuadraticRootRing c) :=
  Localization.Away D

/-- Evaluation of the monic quadratic extension at a supplied square root.-/
def quadraticRootEval (w : B →+* L) (c : B) (r : L)
    (hr : r ^ 2 = w c) : QuadraticRootRing c →+* L := by
  letI : Algebra B L := w.toAlgebra
  have hw : algebraMap B L = w := rfl
  exact (QuadraticAlgebra.lift ⟨r, by
    simpa only [pow_two, Algebra.smul_def, map_zero, zero_mul, add_zero,
      map_one, mul_one, hw] using hr⟩).toRingHom

/--
@isnad1 id=eq.1h5v.s7.78626fed79cb from=translated src=- shape=bcd8acdf vocab=a98713d2
-/
@[simp] theorem quadraticRootEval_omega (w : B →+* L) (c : B) (r : L)
    (hr : r ^ 2 = w c) :
    quadraticRootEval w c r hr QuadraticAlgebra.omega = r := by
  simp [quadraticRootEval, Algebra.smul_def]

/-- Evaluation extends across `Away D` precisely when the witness does not
kill `D`.-/
def quadraticRootAwayEval (w : B →+* L) (c : B) (r : L)
    (hr : r ^ 2 = w c) (D : QuadraticRootRing c)
    (hD : quadraticRootEval w c r hr D ≠ 0) :
    QuadraticRootAway c D →+* L :=
  IsLocalization.Away.lift D (isUnit_iff_ne_zero.mpr hD)

def rootOmega (c : B) (D : QuadraticRootRing c) : QuadraticRootAway c D :=
  algebraMap (QuadraticRootRing c) (QuadraticRootAway c D) QuadraticAlgebra.omega

/--
@isnad1 id=eq.0h3v.s10.a6d8035010fc from=translated src=- shape=a7dcc094 vocab=01d5c75b
-/
theorem rootOmega_sq (c : B) (D : QuadraticRootRing c) :
    rootOmega c D ^ 2 =
      algebraMap (QuadraticRootRing c) (QuadraticRootAway c D)
        (algebraMap B (QuadraticRootRing c) c) := by
  rw [rootOmega, pow_two, ← map_mul]
  simpa only [map_zero, zero_mul, add_zero] using congrArg
    (algebraMap (QuadraticRootRing c) (QuadraticRootAway c D))
    (QuadraticAlgebra.omega_mul_omega_eq_algebraMap
      (R := B) (a := c) (b := 0))

/--
@isnad1 id=eq.2h6v.s9.8f95157446d0 from=translated src=- shape=df652159 vocab=336ca423
-/
@[simp] theorem quadraticRootAwayEval_rootOmega
    (w : B →+* L) (c : B) (r : L) (hr : r ^ 2 = w c)
    (D : QuadraticRootRing c) (hD : quadraticRootEval w c r hr D ≠ 0) :
    quadraticRootAwayEval w c r hr D hD (rootOmega c D) = r := by
  rw [rootOmega, quadraticRootAwayEval, IsLocalization.Away.lift_eq]
  exact quadraticRootEval_omega w c r hr

/-- The same lawful field evaluation simultaneously proves that the localized
quadratic root ring is nontrivial.
@isnad1 id=nontrivi.2h6v.s7.9d27ee7d47a5 from=translated src=- shape=79c11031 vocab=86e0dc3f
-/
theorem quadraticRootAway_nontrivial
    (w : B →+* L) (c : B) (r : L) (hr : r ^ 2 = w c)
    (D : QuadraticRootRing c) (hD : quadraticRootEval w c r hr D ≠ 0) :
    Nontrivial (QuadraticRootAway c D) :=
  (quadraticRootAwayEval w c r hr D hD).domain_nontrivial

/-- One directly iterable step: adjoining an actual square root and then
localizing at a denominator that survives the supplied field point preserves
torsion-freeness over the original base.
@isnad1 id=istorsio.2h7v.s9.9d2304a804a3 from=translated src=- shape=ef268218 vocab=72dc4efa
-/
theorem quadraticRootAway_isTorsionFree
    (w : B →+* L) (c : B) (r : L) (hr : r ^ 2 = w c)
    (D : QuadraticRootRing c) (hD : quadraticRootEval w c r hr D ≠ 0) :
    Module.IsTorsionFree A (QuadraticRootAway c D) := by
  exact away_isTorsionFree D

end AlbertLean.Generic.GenericRootAwayTorsionFree
