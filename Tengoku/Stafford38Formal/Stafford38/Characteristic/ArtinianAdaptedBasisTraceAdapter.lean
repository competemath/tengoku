module
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.ArtinianTriangularTrace
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.ArtinianCoefficientField
public import Tengoku.Stafford38Formal.Stafford38.Characteristic.SquareZeroLinearTrace
public import Tengoku.Seed.LinearAlgebra.Basis.Basic
public import Tengoku.Seed.RingTheory.Artinian.Module
public import Tengoku.Seed.RingTheory.LocalRing.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms leftMultiplicationMatrix_isStrictUpperTriangular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms leftMultiplicationMatrix_isNilpotent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms leftMultiplicationMatrix_decomposition` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms quotientEnd_eq_of_parameter_comp_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms strictTriangularSignedSum_isStrictUpperTriangular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adaptedBasis_conditional_trace_assembler` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adaptedBasis_conditional_terminal_inputs` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Adapted bases and square-zero quotient descent

This file formalizes elementary inputs used near Singh--Kumar Proposition 3.2.
The special fibre is a finite-dimensional module over a commutative Artinian
local algebra.  A basis adapted to the powers of the maximal ideal makes left
multiplication by a maximal-ideal element strictly upper triangular.

The square-zero exactness hypothesis is used at the precise point where the
paper uses `cM = Ann_M(c)`: an equality after multiplication by `c` descends
to equality of the induced operators on `M / cM`.

The scalar-plus-maximal-ideal decomposition is converted to a matrix identity.
The final theorem is only a conditional assembler: its matrix-decomposition
hypothesis already implies trace zero. It is not a formalization of equation
(3.3), and neither `q = 0` nor the concrete deformation-ring/right-Rees
adapter is proved here.
-/

namespace Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter

open Matrix
open Stafford38.Characteristic.ArtinianTriangularTrace
open Stafford38.Characteristic.SquareZeroLinearTrace

noncomputable section

universe u

section AdaptedBasis

variable {K R V : Type u}
variable [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
variable {n : ℕ}

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- Left multiplication on the special-fibre module, viewed as a
`K`-linear endomorphism.-/
def leftMultiplicationEnd (r : R) : Module.End K V where
  toFun v := r • v
  map_add' := smul_add r
  map_smul' a v := by exact smul_comm r a v

omit [IsLocalRing R] in
/--
@isnad1 id=eq.0h5v.s8.bb91681a89a8 from=translated src=- shape=e5943fbc vocab=b68a1630
-/
@[simp] theorem leftMultiplicationEnd_apply (r : R) (v : V) :
    leftMultiplicationEnd (K := K) (V := V) r v = r • v := rfl

/-- A basis genuinely adapted to the maximal-ideal-power filtration.

`level i` records the last filtration layer containing `b i`.  The ordering
condition says deeper vectors occur earlier, as in the basis construction in
Proposition 3.2.  The second field identifies every power-filtration layer
with the span of the corresponding basis vectors.-/
structure IsMaximalIdealFiltrationAdapted
    (m : Ideal R)
    (b : Module.Basis (Fin (n + 1)) K V) (level : Fin (n + 1) → ℕ) : Prop where
  antitone_level : Antitone level
  power_span : ∀ t : ℕ,
    ((m ^ t • (⊤ : Submodule R V)).restrictScalars K) =
      Submodule.span K (b '' {i | t ≤ level i})

/-- Multiplication by a maximal-ideal element raises the power filtration by
one.
@isnad1 id=mem.2h5v.s9.f886ac406ced from=translated src=- shape=c1b778e4 vocab=a10023a5
-/
lemma maximalIdeal_smul_mem_succ_power
    {r : R} (hr : r ∈ 𝔪) {t : ℕ} {v : V}
    (hv : v ∈ 𝔪 ^ t • (⊤ : Submodule R V)) :
    r • v ∈ 𝔪 ^ (t + 1) • (⊤ : Submodule R V) := by
  refine Submodule.smul_induction_on
    (p := fun v => r • v ∈ 𝔪 ^ (t + 1) • (⊤ : Submodule R V)) hv ?_ ?_
  · intro (a : R) ha w hw
    rw [smul_smul]
    apply Submodule.smul_mem_smul
    · rw [pow_succ']
      exact Ideal.mul_mem_mul hr ha
    · exact Submodule.mem_top
  · intro x y hx hy
    rw [smul_add]
    exact Submodule.add_mem _ hx hy

/-- The left multiplication matrix of a maximal-ideal element is strictly
upper triangular in a maximal-ideal-filtration adapted basis.
@isnad1 id=isstrict.2h7v.s10.a07adcc7c256 from=translated src=- shape=8856e62d vocab=848e6f42
-/
theorem leftMultiplicationMatrix_isStrictUpperTriangular
    (b : Module.Basis (Fin (n + 1)) K V) (level : Fin (n + 1) → ℕ)
    (hadapted : IsMaximalIdealFiltrationAdapted 𝔪 b level)
    {r : R} (hr : r ∈ 𝔪) :
    IsStrictUpperTriangular
      (LinearMap.toMatrix b b (leftMultiplicationEnd (K := K) (V := V) r)) := by
  intro i j hji
  rw [LinearMap.toMatrix_apply]
  have hbjSpan :
      b j ∈ Submodule.span K (b '' {i | level j ≤ level i}) := by
    exact (b.self_mem_span_image).mpr (show level j ≤ level j from le_rfl)
  have hbjPower : b j ∈ 𝔪 ^ level j • (⊤ : Submodule R V) := by
    have := hbjSpan
    rw [← hadapted.power_span (level j)] at this
    exact this
  have hraised :
      r • b j ∈ 𝔪 ^ (level j + 1) • (⊤ : Submodule R V) :=
    maximalIdeal_smul_mem_succ_power hr hbjPower
  have hspan :
      r • b j ∈ Submodule.span K (b '' {i | level j + 1 ≤ level i}) := by
    rw [← hadapted.power_span (level j + 1)]
    exact hraised
  have hsupp := b.repr_support_subset_of_mem_span
    {i | level j + 1 ≤ level i} hspan
  by_contra hne
  have hiSupport : i ∈ (b.repr (r • b j)).support := Finsupp.mem_support_iff.mpr hne
  have hlevel : level j + 1 ≤ level i := hsupp hiSupport
  have hreverse : level i ≤ level j := hadapted.antitone_level hji
  omega

/-- In the Artinian-local case, the matrix of multiplication by a
maximal-ideal element is nilpotent.
@isnad1 id=isnilpot.1h6v.s10.c380dc146f98 from=translated src=- shape=d30f0574 vocab=3747b503
-/
theorem leftMultiplicationMatrix_isNilpotent
    [IsArtinianRing R]
    (b : Module.Basis (Fin (n + 1)) K V) {r : R} (hr : r ∈ 𝔪) :
    IsNilpotent
      (LinearMap.toMatrix b b (leftMultiplicationEnd (K := K) (V := V) r)) := by
  have hrnil : IsNilpotent r := by
    obtain ⟨N, hN⟩ :=
      Stafford38.Characteristic.ArtinianCoefficientField.maximalIdeal_isNilpotent
        (R := R)
    refine ⟨N, ?_⟩
    have hrpow : r ^ N ∈ 𝔪 ^ N := Ideal.pow_mem_pow hr N
    rw [hN] at hrpow
    exact hrpow
  have hend : IsNilpotent (leftMultiplicationEnd (K := K) (V := V) r) := by
    obtain ⟨N, hN⟩ := hrnil
    refine ⟨N, ?_⟩
    ext v
    have hp : ∀ (j : ℕ) (w : V),
        ((leftMultiplicationEnd (K := K) (V := V) r) ^ j) w = r ^ j • w := by
      intro j
      induction j with
      | zero => intro w; simp
      | succ j ih =>
          intro w
          rw [pow_succ, Module.End.mul_apply, ih, leftMultiplicationEnd_apply]
          exact (SemigroupAction.mul_smul (r ^ j) r w).symm.trans (by rw [pow_succ])
    rw [hp N v, hN, zero_smul, LinearMap.zero_apply]
  exact hend.map (LinearMap.toMatrixAlgEquiv b)

/-- Matrix form of equation (3.1): the coefficient-field scalar contributes
`q I`, and the maximal-ideal remainder contributes its multiplication
matrix.
@isnad1 id=eq.1h8v.s11.424ac4ecc45f from=translated src=- shape=f24b3e8d vocab=944b43b1
-/
theorem leftMultiplicationMatrix_decomposition
    (b : Module.Basis (Fin (n + 1)) K V) (q : K) (r z : R)
    (hz : z = algebraMap K R q + r) :
    LinearMap.toMatrix b b (leftMultiplicationEnd (K := K) (V := V) z) =
      q • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) +
        LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) r) := by
  subst z
  have hend :
      leftMultiplicationEnd (K := K) (V := V) (algebraMap K R q + r) =
        q • LinearMap.id + leftMultiplicationEnd (K := K) (V := V) r := by
    ext v
    simp [leftMultiplicationEnd, add_smul, IsScalarTower.algebraMap_smul]
  rw [hend, (LinearMap.toMatrix b b).map_add,
    (LinearMap.toMatrix b b).map_smul]
  simp

end AdaptedBasis

section SquareZeroDescent

variable {K W : Type u} [Field K]
variable [AddCommGroup W] [Module K W]
variable {n : ℕ}

/-- Square-zero exactness descends an equality after multiplication by the
parameter to equality of the induced special-fibre operators.

This is the exact square-zero quotient bridge: from
`C ∘ Z = C ∘ T` and `ker C = range C`, the actions of `Z` and `T` agree on
`W / range C`.
@isnad1 id=eq.4h5v.s10.73a43a4e332f from=translated src=- shape=d1314e85 vocab=04f0f9d9
-/
theorem quotientEnd_eq_of_parameter_comp_eq
    (C Z T : Module.End K W)
    (hExact : LinearMap.ker C = LinearMap.range C)
    (hZC : Z.comp C = C.comp Z)
    (hTC : T.comp C = C.comp T)
    (hparameter : C.comp Z = C.comp T) :
    quotientEnd C Z hZC = quotientEnd C T hTC := by
  apply LinearMap.ext
  intro q
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) q
  apply (Submodule.Quotient.eq (LinearMap.range C)).mpr
  rw [← hExact, LinearMap.mem_ker]
  change C (Z w - T w) = 0
  rw [map_sub, sub_eq_zero]
  exact LinearMap.congr_fun hparameter w

/-- A signed sum of three matrices that will be used only in the conditional
matrix assembler below.-/
def strictTriangularSignedSum
    (X Y Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  X - Y + Γ

/-- A signed sum of strictly upper-triangular matrices is strictly upper
triangular.
@isnad1 id=isstrict.3h5v.s7.54938086098f from=translated src=- shape=471d7181 vocab=caf743a5
-/
theorem strictTriangularSignedSum_isStrictUpperTriangular
    (X Y Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hX : IsStrictUpperTriangular X)
    (hY : IsStrictUpperTriangular Y)
    (hΓ : IsStrictUpperTriangular Γ) :
    IsStrictUpperTriangular (strictTriangularSignedSum X Y Γ) := by
  intro i j hji
  simp [strictTriangularSignedSum, hX i j hji, hY i j hji, hΓ i j hji]

/-- Conditional trace assembler for a supplied matrix decomposition.

The actual basis is on the special fibre `W / range C`.  Source-specific
upstream data has already produced the strict upper-triangular remainder
`R₀`; `hdecomposition` assumes that the corrected quotient operator is a
strictly triangular matrix plus commutators. This hypothesis already carries
the trace-zero content and is not claimed to follow directly from equation
(3.3). Square-zero exactness only replaces `T` by the quotient action of `Z`.
@isnad1 id=and.6h12v.s14.9b3354a37ee6 from=translated src=- shape=74bcc12e vocab=42e4e18d
-/
theorem adaptedBasis_conditional_trace_assembler
    (C Z T : Module.End K W)
    (hExact : LinearMap.ker C = LinearMap.range C)
    (hZC : Z.comp C = C.comp Z)
    (hTC : T.comp C = C.comp T)
    (hparameter : C.comp Z = C.comp T)
    (b : Module.Basis (Fin (n + 1)) K (W ⧸ LinearMap.range C))
    (R₀ Θ Φ Ψ H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hR₀ : IsStrictUpperTriangular R₀)
    (hdecomposition :
      LinearMap.toMatrix b b (quotientEnd C T hTC) =
        adaptedFirstOrderMatrix R₀ Θ Φ Ψ H) :
    LinearMap.toMatrix b b (quotientEnd C Z hZC) =
        adaptedFirstOrderMatrix R₀ Θ Φ Ψ H ∧
      Matrix.trace (LinearMap.toMatrix b b (quotientEnd C Z hZC)) = 0 := by
  have hdesc := quotientEnd_eq_of_parameter_comp_eq
    C Z T hExact hZC hTC hparameter
  constructor
  · rw [hdesc]
    exact hdecomposition
  · rw [hdesc, hdecomposition]
    exact trace_adaptedFirstOrderMatrix_eq_zero R₀ Θ Φ Ψ H hR₀

end SquareZeroDescent

section Proposition32Adapter

variable {K R V W : Type u}
variable [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
variable [IsArtinianRing R]
variable [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
variable [AddCommGroup W] [Module K W]
variable {n : ℕ}

local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- Conditional assembly of adapted-basis data with a supplied trace-zero
matrix decomposition.

The basis `b`, indexed by the nonempty finite type `Fin (n+1)`, exhibits the
special fibre `V` as nonzero and finite-dimensional over `K`; `V` is also a
module over the commutative Artinian local algebra `R`.  Its adaptedness makes
the multiplication matrix `U` of the maximal-ideal remainder in (3.1)
strictly upper triangular, while Artinianness makes `U` nilpotent.  This is
kept distinct from the strict triangular correction remainder `Δ` in (3.3).

The equivalence `e` identifies `V` with the square-zero quotient of the
deformation module. Exactness descends equality of the supplied operators to
the special fibre. The hypothesis `hdecomposition` already presents the
corrected operator as a strictly triangular matrix plus commutators.

The conclusion packages strictness and nilpotence of the (3.1) remainder,
trace zero conditional on the supplied decomposition, and the
scalar-plus-remainder matrix identity.  It does not assume or prove the scalar
conclusion `q = 0`. It does not derive the supplied matrix decomposition from
Singh--Kumar equation (3.3).
@isnad1 id=and.12h21v.s14.963eed5344db from=translated src=- shape=47be239a vocab=7b104096
-/
theorem adaptedBasis_conditional_terminal_inputs
    (b : Module.Basis (Fin (n + 1)) K V) (level : Fin (n + 1) → ℕ)
    (hadapted : IsMaximalIdealFiltrationAdapted 𝔪 b level)
    (q : K) (r z : R) (hr : r ∈ 𝔪)
    (hz : z = algebraMap K R q + r)
    (C Z T : Module.End K W)
    (hExact : LinearMap.ker C = LinearMap.range C)
    (hZC : Z.comp C = C.comp Z)
    (hTC : T.comp C = C.comp T)
    (hparameter : C.comp Z = C.comp T)
    (e : (W ⧸ LinearMap.range C) ≃ₗ[K] V)
    (hZaction :
      LinearMap.toMatrix (b.map e.symm) (b.map e.symm)
          (quotientEnd C Z hZC) =
        LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) z))
    (Xcorr Ycorr Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (Θ Φ Ψ H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hXcorr : IsStrictUpperTriangular Xcorr)
    (hYcorr : IsStrictUpperTriangular Ycorr)
    (hΓ : IsStrictUpperTriangular Γ)
    (hdecomposition :
      LinearMap.toMatrix (b.map e.symm) (b.map e.symm)
          (quotientEnd C T hTC) =
        adaptedFirstOrderMatrix
          (strictTriangularSignedSum Xcorr Ycorr Γ) Θ Φ Ψ H) :
    IsStrictUpperTriangular
        (LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) r)) ∧
      IsNilpotent
        (LinearMap.toMatrix b b
          (leftMultiplicationEnd (K := K) (V := V) r)) ∧
      Matrix.trace
        (LinearMap.toMatrix (b.map e.symm) (b.map e.symm)
          (quotientEnd C Z hZC)) = 0 ∧
      q • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) +
          LinearMap.toMatrix b b
            (leftMultiplicationEnd (K := K) (V := V) r) =
        LinearMap.toMatrix (b.map e.symm) (b.map e.symm)
          (quotientEnd C Z hZC) := by
  have hadaptedR : IsStrictUpperTriangular
      (LinearMap.toMatrix b b
        (leftMultiplicationEnd (K := K) (V := V) r)) :=
    leftMultiplicationMatrix_isStrictUpperTriangular b level hadapted hr
  have hmatrix := adaptedBasis_conditional_trace_assembler
    C Z T hExact hZC hTC hparameter (b.map e.symm)
      (strictTriangularSignedSum Xcorr Ycorr Γ) Θ Φ Ψ H
      (strictTriangularSignedSum_isStrictUpperTriangular
        Xcorr Ycorr Γ hXcorr hYcorr hΓ) hdecomposition
  refine ⟨hadaptedR, leftMultiplicationMatrix_isNilpotent b hr, hmatrix.2, ?_⟩
  rw [hZaction, ← leftMultiplicationMatrix_decomposition b q r z hz]

-- The adapted-basis strictness above is deliberately retained as a separate
-- output: it records the source's stronger triangular statement even though
-- nilpotence alone is consumed by equations (3.1)--(3.2).

end Proposition32Adapter

end

end Stafford38.Characteristic.ArtinianAdaptedBasisTraceAdapter
