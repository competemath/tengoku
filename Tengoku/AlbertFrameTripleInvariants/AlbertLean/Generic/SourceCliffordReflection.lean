import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCliffordLinear
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms C_square` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms C_polar` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms C_sandwich` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms C_reflection` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The joint source Clifford action on `SCoord × CCoord`, through its square,
polar, and anisotropic reflection identities.  No Clifford/Spin group or
global Albert-frame coverage is constructed here.
-/

noncomputable section
namespace AlbertLean.Triality.SourceCliffordReflection

open ExteriorSix CoordinateTensor StructuredAdjoint
open SourceCliffordIdentities SourceCliffordLinear

universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev W (K : Type u) [Field K] := SCoord K × CCoord K

/-- Off-diagonal Clifford multiplication by a vector coordinate.-/
def cliffordEnd (v : VCoord K) : Module.End K (W K) where
  toFun w := (muSLinear v w.2, muCLinear v w.1)
  map_add' x y := by
    apply Prod.ext
    · exact (muSLinear v).map_add x.2 y.2
    · exact (muCLinear v).map_add x.1 y.1
  map_smul' a x := by
    apply Prod.ext
    · exact (muSLinear v).map_smul a x.2
    · exact (muCLinear v).map_smul a x.1

@[simp] theorem cliffordEnd_apply (v : VCoord K) (w : W K) :
    cliffordEnd v w = (sourceMuS w.2 v, sourceMuC v w.1) := rfl

/-- Clifford multiplication depends linearly on the vector argument.-/
def C : VCoord K →ₗ[K] Module.End K (W K) where
  toFun := cliffordEnd
  map_add' v w := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change sourceMuS x.2 (v + w) = sourceMuS x.2 v + sourceMuS x.2 w
      apply SCoord.ext <;> funext i <;> fin_cases i <;>
        simp [sourceMuS] <;> ring
    · change sourceMuC (v + w) x.1 = sourceMuC v x.1 + sourceMuC w x.1
      apply CCoord.ext <;> funext i <;> fin_cases i <;>
        simp [sourceMuC] <;> ring
  map_smul' a v := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change sourceMuS x.2 (a • v) = a • sourceMuS x.2 v
      apply SCoord.ext <;> funext i <;> fin_cases i <;>
        simp [sourceMuS] <;> ring
    · change sourceMuC (a • v) x.1 = a • sourceMuC v x.1
      apply CCoord.ext <;> funext i <;> fin_cases i <;>
        simp [sourceMuC] <;> ring

@[simp] theorem C_apply (v : VCoord K) (w : W K) :
    C v w = (sourceMuS w.2 v, sourceMuC v w.1) := rfl

/-- The joint Clifford square, with the accepted `+nV(v)` normalization.-/
theorem C_square (v : VCoord K) :
    C v * C v = nV v • (1 : Module.End K (W K)) := by
  apply LinearMap.ext
  intro w
  apply Prod.ext
  · exact sourceMuS_sourceMuC v w.1
  · exact sourceMuC_sourceMuS v w.2

/-- The joint polarized Clifford relation.-/
theorem C_polar (v w : VCoord K) :
    C v * C w + C w * C v = BV v w • (1 : Module.End K (W K)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simpa [add_comm] using sourceMuS_sourceMuC_polar v w x.1
  · exact sourceMuC_sourceMuS_polar v w x.2

/-- Sandwiching by an anisotropic vector gives the reflection numerator.-/
theorem C_sandwich (a v : VCoord K) :
    C a * C v * C a = BV a v • C a - nV a • C v := by
  have hp := congrArg (fun E : Module.End K (W K) => E * C a) (C_polar a v)
  simp only [add_mul, mul_assoc, C_square, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul] at hp
  simpa only [mul_assoc] using (eq_sub_of_add_eq hp)

/-- Normalized negative Clifford conjugation realizes the orthogonal
reflection `v ↦ v - BV(a,v)/nV(a) • a`.-/
theorem C_reflection (a v : VCoord K) (ha : nV a ≠ 0) :
    -(nV a)⁻¹ • (C a * C v * C a) =
      C (v - (BV a v / nV a) • a) := by
  have hn : -(nV a)⁻¹ * nV a = -1 := by simp [ha]
  have hb : -(nV a)⁻¹ * BV a v = -(BV a v / nV a) := by
    rw [div_eq_mul_inv]
    ring
  rw [C_sandwich, map_sub, map_smul, smul_sub, smul_smul, smul_smul, hn, hb]
  simp only [neg_smul, one_smul, sub_neg_eq_add]
  abel

end AlbertLean.Triality.SourceCliffordReflection
