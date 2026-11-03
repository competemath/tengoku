import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCliffordReflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms nV_evenV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nS_evenS` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms nC_evenC` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms C_mul_C_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenS_reverse` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenC_reverse` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Even products of two anisotropic source Clifford reflections, separated into
the `V`, `S`, and `C` slots.  This module stops before a Spin-group or global
frame-coverage construction.
-/

noncomputable section
namespace AlbertLean.Triality.SourceEvenReflections

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordIdentities SourceCliffordLinear SourceCliffordReflection

universe u
variable {K : Type u} [Field K] [CharZero K]

def reflectV (a v : VCoord K) : VCoord K :=
  v - (BV a v / nV a) • a

def evenV (a b v : VCoord K) : VCoord K := reflectV a (reflectV b v)

def evenS (a b : VCoord K) (rho : K) (s : SCoord K) : SCoord K :=
  rho⁻¹ • sourceMuS (sourceMuC b s) a

def evenC (a b : VCoord K) (rho : K) (c : CCoord K) : CCoord K :=
  rho⁻¹ • sourceMuC a (sourceMuS c b)

/--
@isnad1 id=eq.1h3v.s6.a4d051561c5e from=translated src=- shape=8e37ae88 vocab=ae3db609
-/
theorem nV_reflectV (a v : VCoord K) (ha : nV a ≠ 0) :
    nV (reflectV a v) = nV v := by
  rw [reflectV, sub_eq_add_neg, ← neg_smul, nV_add, nV_smul, BV_smul_right, BV_symmetric v a]
  field_simp [ha]
  ring

/--
@isnad1 id=eq.2h4v.s6.a256197ffd4e from=translated src=- shape=7ca1a445 vocab=c1df294f
-/
theorem nV_evenV (a b v : VCoord K) (ha : nV a ≠ 0)
    (hb : nV b ≠ 0) : nV (evenV a b v) = nV v := by
  rw [evenV, nV_reflectV a _ ha, nV_reflectV b v hb]

/--
@isnad1 id=eq.2h5v.s6.c6f3c16c7ecf from=translated src=- shape=667f0216 vocab=6aaa5c7e
-/
theorem nS_evenS (a b : VCoord K) (rho : K) (s : SCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    nS (evenS a b rho s) = nS s := by
  rw [evenS, nS_smul, nS_sourceMuS, nC_sourceMuC]
  calc
    rho⁻¹ ^ 2 * (nV a * (nV b * nS s)) =
        (rho⁻¹ ^ 2 * (nV a * nV b)) * nS s := by ring
    _ = nS s := by rw [← hrho, ← mul_pow]; simp [hrho0]

/--
@isnad1 id=eq.2h5v.s6.9eed90f3215b from=translated src=- shape=667f0216 vocab=27024227
-/
theorem nC_evenC (a b : VCoord K) (rho : K) (c : CCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    nC (evenC a b rho c) = nC c := by
  rw [evenC, nC_smul, nC_sourceMuC, nS_sourceMuS]
  calc
    rho⁻¹ ^ 2 * (nV a * (nV b * nC c)) =
        (rho⁻¹ ^ 2 * (nV a * nV b)) * nC c := by ring
    _ = nC c := by rw [← hrho, ← mul_pow]; simp [hrho0]

/-- The raw even spin action is the diagonal action of `C(a)C(b)` on
`SCoord × CCoord`.
@isnad1 id=eq.0h5v.s12.c5fa3cdcdf60 from=translated src=- shape=c36ae093 vocab=3f88e137
-/
theorem C_mul_C_apply (a b : VCoord K) (s : SCoord K) (c : CCoord K) :
    (C a * C b) (s, c) =
      (sourceMuS (sourceMuC b s) a,
        sourceMuC a (sourceMuS c b)) := rfl

set_option maxHeartbeats 400000 in
/-- The inverse block has the reversed Clifford order.
@isnad1 id=eq.2h5v.s6.01d26e913b53 from=translated src=- shape=e20ffea9 vocab=61475c7a
-/
theorem evenS_reverse (a b : VCoord K) (rho : K) (s : SCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    evenS b a rho (evenS a b rho s) = s := by
  change rho⁻¹ • muSLinear b (muCLinear a (rho⁻¹ • muSLinear a (muCLinear b s))) = s
  rw [(muCLinear a).map_smul, (muSLinear b).map_smul]
  have hc : muCLinear a (muSLinear a (muCLinear b s)) = nV a • muCLinear b s :=
    sourceMuC_sourceMuS a _
  rw [hc, (muSLinear b).map_smul]
  have hs : muSLinear b (muCLinear b s) = nV b • s := sourceMuS_sourceMuC b s
  rw [hs]
  simp only [smul_smul]
  have hn : rho⁻¹ * (rho⁻¹ * (nV a * nV b)) = 1 := by
    rw [← hrho]
    field_simp [hrho0]
  rw [hn, one_smul]

/-- Companion inverse identity on the other half-spin slot.
@isnad1 id=eq.2h5v.s6.a7f235d0b69b from=translated src=- shape=e20ffea9 vocab=c6efde8b
-/
theorem evenC_reverse (a b : VCoord K) (rho : K) (c : CCoord K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    evenC b a rho (evenC a b rho c) = c := by
  change rho⁻¹ • muCLinear b (muSLinear a (rho⁻¹ • muCLinear a (muSLinear b c))) = c
  rw [(muSLinear a).map_smul, (muCLinear b).map_smul]
  have hs : muSLinear a (muCLinear a (muSLinear b c)) = nV a • muSLinear b c :=
    sourceMuS_sourceMuC a _
  rw [hs, (muCLinear b).map_smul]
  have hc : muCLinear b (muSLinear b c) = nV b • c := sourceMuC_sourceMuS b c
  rw [hc]
  simp only [smul_smul]
  have hn : rho⁻¹ * (rho⁻¹ * (nV a * nV b)) = 1 := by
    rw [← hrho]
    field_simp [hrho0]
  rw [hn, one_smul]

end AlbertLean.Triality.SourceEvenReflections
