import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceEvenReflections
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualPowerMeasurements
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms C_evenV_intertwine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenS_muS_intertwine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms BS_evenS` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms triality_even` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The structural intertwiner and triality identity for a normalized even pair of
source Clifford reflections.  This module deliberately stops before packaging
the three maps into an Albert source automorphism.
-/

noncomputable section
namespace AlbertLean.Triality.SourceEvenTriality

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordIdentities SourceCliffordLinear SourceCliffordReflection
open SourceEvenReflections
open AlbertLean.Generic.ResidualPowerMeasurements

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem C_reflect_mul (a v : VCoord K) (ha : nV a ≠ 0) :
    C (reflectV a v) * C a = -(C a * C v) := by
  have h := congrArg (fun E : Module.End K (SourceCliffordReflection.W K) => E * C a) (C_reflection a v ha)
  simp only [smul_mul_assoc, mul_assoc, C_square, mul_smul_comm, smul_smul,
    mul_one] at h
  have hn : -(nV a)⁻¹ * nV a = -1 := by simp [ha]
  rw [hn, neg_one_smul] at h
  exact h.symm

/-- The raw even Clifford element intertwines Clifford multiplication with the
composition of its two vector reflections.  Keeping this as an identity in the
endomorphism algebra makes both half-spin component identities reusable.-/
theorem C_evenV_intertwine (a b v : VCoord K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0) :
    (C a * C b) * C v = C (evenV a b v) * (C a * C b) := by
  have ha' := C_reflect_mul a (reflectV b v) ha
  have hb' := C_reflect_mul b v hb
  change (C a * C b) * C v = C (reflectV a (reflectV b v)) * (C a * C b)
  symm
  calc
    C (reflectV a (reflectV b v)) * (C a * C b) =
        (C (reflectV a (reflectV b v)) * C a) * C b := (mul_assoc _ _ _).symm
    _ = -(C a * C (reflectV b v)) * C b := congrArg (fun E => E * C b) ha'
    _ = -(C a * (C (reflectV b v) * C b)) := by
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply, LinearMap.neg_apply]
    _ = -(C a * (-(C b * C v))) := by rw [hb']
    _ = (C a * C b) * C v := by
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply, LinearMap.neg_apply, map_neg, neg_neg]

/-- The `S` component of `C_evenV_intertwine`, with the common normalization
factor retained explicitly.-/
theorem evenS_muS_intertwine (a b v : VCoord K) (rho : K)
    (s : SCoord K) (c : CCoord K) (ha : nV a ≠ 0) (hb : nV b ≠ 0) :
    evenS a b rho (sourceMuS c v) =
      sourceMuS (evenC a b rho c) (evenV a b v) := by
  have h := LinearMap.congr_fun (C_evenV_intertwine a b v ha hb) (s, c)
  have hs : sourceMuS (sourceMuC b (sourceMuS c v)) a =
      sourceMuS (sourceMuC a (sourceMuS c b)) (evenV a b v) := by
    simpa only [Module.End.mul_apply, C_apply] using congrArg Prod.fst h
  calc
    evenS a b rho (sourceMuS c v) =
        rho⁻¹ • sourceMuS (sourceMuC b (sourceMuS c v)) a := rfl
    _ = rho⁻¹ • sourceMuS (sourceMuC a (sourceMuS c b))
          (evenV a b v) := congrArg (rho⁻¹ • ·) hs
    _ = sourceMuS (rho⁻¹ • sourceMuC a (sourceMuS c b))
          (evenV a b v) := by
      change rho⁻¹ • muSLinear (evenV a b v) _ =
        muSLinear (evenV a b v) (rho⁻¹ • _)
      exact ((muSLinear (evenV a b v)).map_smul rho⁻¹ _).symm
    _ = sourceMuS (evenC a b rho c) (evenV a b v) := rfl

/-- The companion `C` component of the even Clifford intertwiner.-/
theorem evenC_muC_intertwine (a b v : VCoord K) (rho : K)
    (s : SCoord K) (c : CCoord K) (ha : nV a ≠ 0) (hb : nV b ≠ 0) :
    evenC a b rho (sourceMuC v s) =
      sourceMuC (evenV a b v) (evenS a b rho s) := by
  have h := LinearMap.congr_fun (C_evenV_intertwine a b v ha hb) (s, c)
  have hc : sourceMuC a (sourceMuS (sourceMuC v s) b) =
      sourceMuC (evenV a b v) (sourceMuS (sourceMuC b s) a) := by
    simpa only [Module.End.mul_apply, C_apply] using congrArg Prod.snd h
  calc
    evenC a b rho (sourceMuC v s) =
        rho⁻¹ • sourceMuC a (sourceMuS (sourceMuC v s) b) := rfl
    _ = rho⁻¹ • sourceMuC (evenV a b v)
          (sourceMuS (sourceMuC b s) a) := congrArg (rho⁻¹ • ·) hc
    _ = sourceMuC (evenV a b v)
          (rho⁻¹ • sourceMuS (sourceMuC b s) a) := by
      change rho⁻¹ • muCLinear (evenV a b v) _ =
        muCLinear (evenV a b v) (rho⁻¹ • _)
      exact ((muCLinear (evenV a b v)).map_smul rho⁻¹ _).symm
    _ = sourceMuC (evenV a b v) (evenS a b rho s) := rfl

theorem evenS_add (a b : VCoord K) (rho : K) (s t : SCoord K) :
    evenS a b rho (s + t) = evenS a b rho s + evenS a b rho t := by
  change rho⁻¹ • muSLinear a (muCLinear b (s + t)) =
    rho⁻¹ • muSLinear a (muCLinear b s) + rho⁻¹ • muSLinear a (muCLinear b t)
  rw [map_add, map_add, smul_add]

theorem evenC_add (a b : VCoord K) (rho : K) (c d : CCoord K) :
    evenC a b rho (c + d) = evenC a b rho c + evenC a b rho d := by
  change rho⁻¹ • muCLinear a (muSLinear b (c + d)) =
    rho⁻¹ • muCLinear a (muSLinear b c) + rho⁻¹ • muCLinear a (muSLinear b d)
  rw [map_add, map_add, smul_add]

/-- Polarization of `nS_evenS`.-/
theorem BS_evenS (a b : VCoord K) (rho : K) (s t : SCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    BS (evenS a b rho s) (evenS a b rho t) = BS s t := by
  have hst := nS_evenS a b rho (s + t) hrho hrho0
  rw [evenS_add, nS_add, nS_add,
    nS_evenS a b rho s hrho hrho0,
    nS_evenS a b rho t hrho hrho0] at hst
  linear_combination hst

/-- Polarization of `nC_evenC`.-/
theorem BC_evenC (a b : VCoord K) (rho : K) (c d : CCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    BC (evenC a b rho c) (evenC a b rho d) = BC c d := by
  have hcd := nC_evenC a b rho (c + d) hrho hrho0
  rw [evenC_add, nC_add, nC_add,
    nC_evenC a b rho c hrho hrho0,
    nC_evenC a b rho d hrho hrho0] at hcd
  linear_combination hcd

/-- A normalized even pair preserves the accepted source triality tensor.-/
theorem triality_even (a b : VCoord K) (rho : K)
    (v : VCoord K) (s : SCoord K) (c : CCoord K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    triality (evenV a b v) (evenS a b rho s) (evenC a b rho c) =
      triality v s c := by
  rw [← muS_triality, ← evenS_muS_intertwine a b v rho s c ha hb,
    BS_evenS a b rho (sourceMuS c v) s hrho hrho0, muS_triality]

end AlbertLean.Triality.SourceEvenTriality
