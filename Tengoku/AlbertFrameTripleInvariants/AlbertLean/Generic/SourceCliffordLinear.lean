import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCliffordIdentities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms nS_sourceMuS` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nC_sourceMuC` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms muSLinear_comp_muCLinear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms muCLinear_comp_muSLinear` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Linear and norm foundations for the accepted source Clifford action.
This module constructs no Spin group or reflection lift.
-/
noncomputable section
namespace AlbertLean.Triality.SourceCliffordLinear

open ExteriorSix CoordinateTensor StructuredAdjoint SourceCliffordIdentities

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- For fixed vector coordinate `v`, Clifford multiplication from `C` to `S`.-/
def muSLinear (v : VCoord K) : CCoord K →ₗ[K] SCoord K where
  toFun c := sourceMuS c v
  map_add' c d := by
    apply SCoord.ext <;> funext i <;> fin_cases i <;>
      simp [sourceMuS] <;> ring
  map_smul' a c := by
    apply SCoord.ext <;> funext i <;> fin_cases i <;>
      simp [sourceMuS] <;> ring

/-- For fixed vector coordinate `v`, Clifford multiplication from `S` to `C`.-/
def muCLinear (v : VCoord K) : SCoord K →ₗ[K] CCoord K where
  toFun s := sourceMuC v s
  map_add' s t := by
    apply CCoord.ext <;> funext i <;> fin_cases i <;>
      simp [sourceMuC] <;> ring
  map_smul' a s := by
    apply CCoord.ext <;> funext i <;> fin_cases i <;>
      simp [sourceMuC] <;> ring

/--
@isnad1 id=eq.0h3v.s8.84bd8f7f338a from=translated src=- shape=d9d8353b vocab=d2ef103d
-/
@[simp] theorem muSLinear_apply (v : VCoord K) (c : CCoord K) :
    muSLinear v c = sourceMuS c v := rfl

/--
@isnad1 id=eq.0h3v.s8.1a3441ff80b8 from=translated src=- shape=5a8756a7 vocab=4ccae74a
-/
@[simp] theorem muCLinear_apply (v : VCoord K) (s : SCoord K) :
    muCLinear v s = sourceMuC v s := rfl

/-- Exact norm multiplier in the accepted normalization.
@isnad1 id=eq.0h3v.s5.bde3e1337ae3 from=translated src=- shape=d366b993 vocab=b96a2576
-/
theorem nS_sourceMuS (c : CCoord K) (v : VCoord K) :
    nS (sourceMuS c v) = nV v * nC c := by
  simp [nS, nC, evalU, sourceMuS, nV, pf_coordinate]
  ring

/-- The companion half-spin action has the same norm multiplier.
@isnad1 id=eq.0h3v.s5.52c4b48d11bc from=translated src=- shape=efabeac0 vocab=174e2813
-/
theorem nC_sourceMuC (v : VCoord K) (s : SCoord K) :
    nC (sourceMuC v s) = nV v * nS s := by
  simp [nS, nC, evalU, sourceMuC, nV, pf_coordinate]
  ring

/-- The `S`-block square as an equality of linear maps.
@isnad1 id=eq.0h2v.s9.5801a9109841 from=translated src=- shape=1d7c739f vocab=75b13fca
-/
theorem muSLinear_comp_muCLinear (v : VCoord K) :
    (muSLinear v).comp (muCLinear v) = nV v • LinearMap.id := by
  apply LinearMap.ext
  intro s
  exact sourceMuS_sourceMuC v s

/-- The `C`-block square as an equality of linear maps.
@isnad1 id=eq.0h2v.s9.0125cdd6ad7a from=translated src=- shape=1d7c739f vocab=75b13fca
-/
theorem muCLinear_comp_muSLinear (v : VCoord K) :
    (muCLinear v).comp (muSLinear v) = nV v • LinearMap.id := by
  apply LinearMap.ext
  intro c
  exact sourceMuC_sourceMuS v c

end AlbertLean.Triality.SourceCliffordLinear
