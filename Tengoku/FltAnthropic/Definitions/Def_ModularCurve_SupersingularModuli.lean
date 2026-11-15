import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve

def ssJSet (p : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set K :=
  {j | ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
    ∀ P : W.toAffine.Point, p • P = 0 → P = 0}

/--
@isnad1 id=iff.0h3v.s7.f0911962914c from=translated src=- shape=c69cf0ad vocab=f1cc2ede
-/
theorem mem_ssJSet_iff {p : ℕ} {K : Type*} [Field K] [DecidableEq K] {j : K} :
    j ∈ ssJSet p K ↔ ∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j →
      ∀ P : W.toAffine.Point, p • P = 0 → P = 0 :=
  Iff.rfl

def ModuliPoint.IsSupersingular (p : ℕ) {N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (x : ModuliPoint N K) : Prop :=
  x.j ∈ ssJSet p K

def ssLocus (p N : ℕ) (K : Type*) [Field K] [DecidableEq K] : Set (ModuliPoint N K) :=
  {x | x.IsSupersingular p}

/--
@isnad1 id=iff.0h4v.s5.cd66601bfac4 from=translated src=- shape=3293e9ab vocab=790d2020
-/
theorem mem_ssLocus_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {x : ModuliPoint N K} :
    x ∈ ssLocus p N K ↔ x.j ∈ ssJSet p K :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.9a03412685f0 from=translated src=- shape=7d9d8e5b vocab=3f14e1fb
-/
theorem isSupersingular_mk_iff {p N : ℕ} {K : Type*} [Field K] [DecidableEq K]
    {P : Gamma0Pair N K} :
    ModuliPoint.IsSupersingular p (Quot.mk _ P : ModuliPoint N K) ↔
      P.toCurve.j ∈ ssJSet p K :=
  Iff.rfl

end ModularCurve
