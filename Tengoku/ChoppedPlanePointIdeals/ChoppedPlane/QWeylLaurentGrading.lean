module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylGrading
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentChartComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Actual Laurent grading of the cyclic profile operators

The coefficients are images of the literal binary polynomials.  Their
nonnegative Laurent supports prove closure on both affine charts as well as
the overlap.  The resulting degree shifts commute with homogeneous projection.
-/

noncomputable section
namespace ChoppedPlane.QWeyl
set_option maxHeartbeats 1000000
open LaurentPairing LaurentChartComplex
open scoped Pointwise
variable {K : Type*} [Field K]

/-- The actual binary polynomial embedding into the overlap Laurent ring.-/
def binaryLaurentEmbedding : BinaryRing K →ₐ[K] BinaryLaurent K :=
  MvPolynomial.aeval ![U, V]

/--
@isnad1 id=eq.0h1v.s8.08949d687dd9 from=translated src=- shape=b9e915e9 vocab=f1a276df
-/
@[simp] theorem binaryLaurentEmbedding_X_zero :
    binaryLaurentEmbedding (MvPolynomial.X (0 : Fin 2) : BinaryRing K) = U := by
  simp [binaryLaurentEmbedding]

/--
@isnad1 id=eq.0h1v.s8.96707c5c70f6 from=translated src=- shape=b9e915e9 vocab=36bd8d5b
-/
@[simp] theorem binaryLaurentEmbedding_X_one :
    binaryLaurentEmbedding (MvPolynomial.X (1 : Fin 2) : BinaryRing K) = V := by
  simp [binaryLaurentEmbedding]

/--
@isnad1 id=eq.0h1v.s8.526a7a1c9939 from=translated src=- shape=d0481623 vocab=44ad29f3
-/
@[simp] theorem binaryLaurentEmbedding_binaryU :
    binaryLaurentEmbedding (binaryU K) = (U : BinaryLaurent K) :=
  binaryLaurentEmbedding_X_zero

/--
@isnad1 id=eq.0h1v.s8.682a1936de7f from=translated src=- shape=d0481623 vocab=2de104cf
-/
@[simp] theorem binaryLaurentEmbedding_binaryV :
    binaryLaurentEmbedding (binaryV K) = (V : BinaryLaurent K) :=
  binaryLaurentEmbedding_X_one

/-- Nonnegative Laurent exponents of the specified ordinary degree.-/
def polynomialLaurentGrade (d : ℤ) : Submodule K (BinaryLaurent K) :=
  AddMonoidAlgebra.supported K K
    {e : ℤ × ℤ | 0 ≤ e.1 ∧ 0 ≤ e.2 ∧ e.1 + e.2 = d}

/--
@isnad1 id=mem.2h5v.s9.7d9d29f1367a from=translated src=- shape=9108c71e vocab=fcafcc7e
-/
theorem polynomialLaurentGrade_mul {d e : ℤ} {p q : BinaryLaurent K}
    (hp : p ∈ polynomialLaurentGrade d) (hq : q ∈ polynomialLaurentGrade e) :
    p * q ∈ polynomialLaurentGrade (d + e) := by
  classical
  apply AddMonoidAlgebra.mem_supported.mpr
  intro c hc
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset p q hc)
  have ha' := AddMonoidAlgebra.mem_supported.mp hp ha
  have hb' := AddMonoidAlgebra.mem_supported.mp hq hb
  change 0 ≤ a.1 + b.1 ∧ 0 ≤ a.2 + b.2 ∧
    (a.1 + b.1) + (a.2 + b.2) = d + e
  change 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.1 + a.2 = d at ha'
  change 0 ≤ b.1 ∧ 0 ≤ b.2 ∧ b.1 + b.2 = e at hb'
  omega

/--
@isnad1 id=mem.1h3v.s7.53212ccd3d32 from=translated src=- shape=b338c234 vocab=d73fb26e
-/
theorem polynomialLaurentGrade_single (e : ℤ × ℤ) (c : K)
    (he : 0 ≤ e.1 ∧ 0 ≤ e.2) :
    AddMonoidAlgebra.single e c ∈ polynomialLaurentGrade (e.1 + e.2) := by
  classical
  apply AddMonoidAlgebra.mem_supported.mpr
  intro a ha
  have h := Finsupp.support_single_subset ha
  have : a = e := Finset.mem_singleton.mp h
  subst a
  exact ⟨he.1, he.2, rfl⟩

/--
@isnad1 id=mem.0h1v.s7.ee0fd28bfc4f from=translated src=- shape=1be9b13a vocab=d6265426
-/
theorem U_mem_polynomialLaurentGrade : (U : BinaryLaurent K) ∈ polynomialLaurentGrade 1 :=
  polynomialLaurentGrade_single (1, 0) 1 (by norm_num)

/--
@isnad1 id=mem.0h1v.s7.0d0b15471430 from=translated src=- shape=1be9b13a vocab=1c61e2d5
-/
theorem V_mem_polynomialLaurentGrade : (V : BinaryLaurent K) ∈ polynomialLaurentGrade 1 :=
  polynomialLaurentGrade_single (0, 1) 1 (by norm_num)

/--
@isnad1 id=mem.0h1v.s7.51baff258ddf from=translated src=- shape=04022825 vocab=1c064d64
-/
theorem one_mem_polynomialLaurentGrade : (1 : BinaryLaurent K) ∈ polynomialLaurentGrade 0 := by
  change AddMonoidAlgebra.single (0, 0) 1 ∈ polynomialLaurentGrade 0
  exact polynomialLaurentGrade_single (0, 0) (1 : K) (by norm_num)

/--
@isnad1 id=mem.0h3v.s8.07e9cb553875 from=translated src=- shape=aefacd50 vocab=75140135
-/
theorem cubicLinearFactors_laurent_mem (q : K) (i : Fin 3) :
    binaryLaurentEmbedding (cubicLinearFactors q i) ∈ polynomialLaurentGrade 1 := by
  have hu := U_mem_polynomialLaurentGrade (K := K)
  have hv := V_mem_polynomialLaurentGrade (K := K)
  fin_cases i
  · simpa [cubicLinearFactors, binaryU, binaryV, binaryLaurentEmbedding] using
      (polynomialLaurentGrade (K := K) 1).add_mem hu hv
  · simpa [cubicLinearFactors, binaryU, binaryV, binaryLaurentEmbedding, Algebra.smul_def] using
      (polynomialLaurentGrade (K := K) 1).add_mem hu
        ((polynomialLaurentGrade (K := K) 1).smul_mem q hv)
  · simpa [cubicLinearFactors, binaryU, binaryV, binaryLaurentEmbedding, Algebra.smul_def] using
      (polynomialLaurentGrade (K := K) 1).add_mem hu
        ((polynomialLaurentGrade (K := K) 1).smul_mem (q ^ 2) hv)

/--
@isnad1 id=mem.0h4v.s8.ac0ef00431de from=translated src=- shape=ab1bc616 vocab=711c72af
-/
theorem profileFactors_laurent_mem (q : K) (s : CubicProfile) (i : Fin 3) :
    binaryLaurentEmbedding (profileFactors q s i) ∈
      polynomialLaurentGrade (profileFactorDegrees s i : ℤ) := by
  cases s <;> fin_cases i
  · exact cubicLinearFactors_laurent_mem q 0
  · exact cubicLinearFactors_laurent_mem q 1
  · exact cubicLinearFactors_laurent_mem q 2
  · exact cubicLinearFactors_laurent_mem q 0
  · simpa [profileFactors, profileFactorDegrees] using one_mem_polynomialLaurentGrade (K := K)
  · simpa [profileFactors, profileFactorDegrees, map_mul] using
      polynomialLaurentGrade_mul (cubicLinearFactors_laurent_mem q 1)
        (cubicLinearFactors_laurent_mem q 2)
  · simpa [profileFactors, profileFactorDegrees] using one_mem_polynomialLaurentGrade (K := K)
  · exact cubicLinearFactors_laurent_mem q 1
  · simpa [profileFactors, profileFactorDegrees, map_mul] using
      polynomialLaurentGrade_mul (cubicLinearFactors_laurent_mem q 0)
        (cubicLinearFactors_laurent_mem q 2)

variable {ι : Type*} [Finite ι]

/-- A literal Laurent coefficient matrix with one source per output component.-/
def laurentOperator (γ : ι → BinaryLaurent K) (σ : ι → ι) :
    FreeLaurent K ι →ₗ[K] FreeLaurent K ι :=
  (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap.comp
    (({
      toFun := fun m i => γ i * m (σ i)
      map_add' := by intro m n; funext i; exact mul_add _ _ _
      map_smul' := by
        intro c m
        funext i
        simp [Algebra.smul_def, mul_left_comm]
      } : (ι → BinaryLaurent K) →ₗ[K] (ι → BinaryLaurent K)).comp
        (freeLaurentEquiv (K := K) (ι := ι)).toLinearMap)

/--
@isnad1 id=eq.0h6v.s10.d500c80051ef from=translated src=- shape=b10b2651 vocab=711cf304
-/
@[simp] theorem freeLaurentEquiv_laurentOperator (γ : ι → BinaryLaurent K)
    (σ : ι → ι) (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (laurentOperator γ σ p) i = γ i * freeLaurentEquiv p (σ i) := by
  simp [laurentOperator]

/-- A polynomial coefficient preserves any exponent condition closed under
adding a nonnegative exponent pair, with the exact generator degree shift.
@isnad1 id=mem.3h12v.s10.1f1a5f5bbb40 from=translated src=- shape=07f92762 vocab=3145f615
-/
theorem laurentOperator_supported (γ : ι → BinaryLaurent K) (σ : ι → ι)
    (g h : ι → ℤ) (d : ℤ) (δ : ι → ℤ)
    (hγ : ∀ i, γ i ∈ polynomialLaurentGrade (δ i))
    (hdegree : ∀ i, δ i + h i = d + g (σ i))
    (P : ℤ × ℤ → Prop)
    (hP : ∀ a b : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → P b → P (a + b))
    (k : ℤ) (p : FreeLaurent K ι)
    (hp : p ∈ Finsupp.supported K K
      {e : ι × (ℤ × ℤ) | e.2.1 + e.2.2 + g e.1 = k ∧ P e.2}) :
    laurentOperator γ σ p ∈ Finsupp.supported K K
      {e : ι × (ℤ × ℤ) | e.2.1 + e.2.2 + h e.1 = k + d ∧ P e.2} := by
  classical
  apply (Finsupp.mem_supported K _).mpr
  intro e he
  have he' : e.2 ∈ (γ e.1 * freeLaurentEquiv p (σ e.1)).coeff.support := by
    rw [← freeLaurentEquiv_laurentOperator, Finsupp.mem_support_iff]
    simpa only [freeLaurentEquiv_coeff] using (Finsupp.mem_support_iff.mp he)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset _ _ he')
  have ha' := AddMonoidAlgebra.mem_supported.mp (hγ e.1) ha
  have hb' : (σ e.1, b) ∈ p.support := by
    simpa only [Finsupp.mem_support_iff, freeLaurentEquiv_coeff] using hb
  have hp' := (Finsupp.mem_supported K p).mp hp hb'
  change 0 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.1 + a.2 = δ e.1 at ha'
  change b.1 + b.2 + g (σ e.1) = k ∧ P b at hp'
  change e.2.1 + e.2.2 + h e.1 = k + d ∧ P e.2
  have hh := hdegree e.1
  rw [← hab]
  exact ⟨by change a.1 + b.1 + (a.2 + b.2) + h e.1 = k + d; omega,
    hP a b ha'.1 ha'.2.1 hp'.2⟩

/--
@isnad1 id=mem.3h10v.s9.661ba3e8eae8 from=translated src=- shape=51632fbe vocab=cf53c9fa
-/
theorem laurentOperator_mem_overlapGrade (γ : ι → BinaryLaurent K) (σ : ι → ι)
    (g h : ι → ℤ) (d : ℤ) (δ : ι → ℤ)
    (hγ : ∀ i, γ i ∈ polynomialLaurentGrade (δ i))
    (hdegree : ∀ i, δ i + h i = d + g (σ i))
    (k : ℤ) (p : FreeLaurent K ι) (hp : p ∈ overlapGrade g k) :
    laurentOperator γ σ p ∈ overlapGrade h (k + d) := by
  simpa only [overlapGrade, gradeIndices, and_true] using
    laurentOperator_supported γ σ g h d δ hγ hdegree (fun _ => True)
      (by intros; trivial) k p
        (by simpa only [overlapGrade, gradeIndices, and_true] using hp)

/--
@isnad1 id=mem.3h10v.s9.771ee8055e6c from=translated src=- shape=51632fbe vocab=e8983091
-/
theorem laurentOperator_mem_uChartGrade (γ : ι → BinaryLaurent K) (σ : ι → ι)
    (g h : ι → ℤ) (d : ℤ) (δ : ι → ℤ)
    (hγ : ∀ i, γ i ∈ polynomialLaurentGrade (δ i))
    (hdegree : ∀ i, δ i + h i = d + g (σ i))
    (k : ℤ) (p : FreeLaurent K ι) (hp : p ∈ uChartGrade g k) :
    laurentOperator γ σ p ∈ uChartGrade h (k + d) :=
  laurentOperator_supported γ σ g h d δ hγ hdegree (fun e => 0 ≤ e.2)
    (by intro a b ha hb h; change 0 ≤ a.2 + b.2; omega) k p hp

/--
@isnad1 id=mem.3h10v.s9.e7d29870e002 from=translated src=- shape=51632fbe vocab=1e44c221
-/
theorem laurentOperator_mem_vChartGrade (γ : ι → BinaryLaurent K) (σ : ι → ι)
    (g h : ι → ℤ) (d : ℤ) (δ : ι → ℤ)
    (hγ : ∀ i, γ i ∈ polynomialLaurentGrade (δ i))
    (hdegree : ∀ i, δ i + h i = d + g (σ i))
    (k : ℤ) (p : FreeLaurent K ι) (hp : p ∈ vChartGrade g k) :
    laurentOperator γ σ p ∈ vChartGrade h (k + d) :=
  laurentOperator_supported γ σ g h d δ hγ hdegree (fun e => 0 ≤ e.1)
    (by intro a b ha hb h; change 0 ≤ a.1 + b.1; omega) k p hp

/--
@isnad1 id=eq.2h9v.s9.5e38cdbe008a from=translated src=- shape=24b9ab69 vocab=17178d0d
-/
theorem laurentOperator_projection_commutes (γ : ι → BinaryLaurent K) (σ : ι → ι)
    (g h : ι → ℤ) (d : ℤ) (δ : ι → ℤ)
    (hγ : ∀ i, γ i ∈ polynomialLaurentGrade (δ i))
    (hdegree : ∀ i, δ i + h i = d + g (σ i)) (k : ℤ) :
    (gradeProjection h (k + d)).comp (laurentOperator γ σ) =
      (laurentOperator γ σ).comp (gradeProjection g k) :=
  gradeProjection_commutes_of_degree_shift g h d _
    (laurentOperator_mem_overlapGrade γ σ g h d δ hγ hdegree) k

/-- Actual componentwise scalar multiplication on the overlap.-/
def laurentScalar (c : BinaryLaurent K) : FreeLaurent K ι →ₗ[K] FreeLaurent K ι :=
  laurentOperator (fun _ => c) id

/--
@isnad1 id=eq.0h5v.s10.d03f2b05cb4e from=translated src=- shape=87033e34 vocab=55d845ec
-/
@[simp] theorem freeLaurentEquiv_laurentScalar (c : BinaryLaurent K)
    (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (laurentScalar c p) i = c * freeLaurentEquiv p i :=
  freeLaurentEquiv_laurentOperator _ _ _ _

/--
@isnad1 id=eq.0h4v.s10.67d7a3590f87 from=translated src=- shape=8671fe2b vocab=7c87769d
-/
@[simp] theorem freeLaurentEquiv_symm_scalar (c : BinaryLaurent K)
    (m : ι → BinaryLaurent K) :
    freeLaurentEquiv.symm (fun i => c * m i) =
      laurentScalar c (freeLaurentEquiv.symm m) := by
  apply freeLaurentEquiv.injective
  funext i
  simp

/-- Actual coefficient-vector grades transported through Laurent coefficients.-/
def vectorOverlapGrade (g : ι → ℤ) (k : ℤ) : Submodule K (ι → BinaryLaurent K) :=
  (overlapGrade g k).comap (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap

def vectorUChartGrade (g : ι → ℤ) (k : ℤ) : Submodule K (ι → BinaryLaurent K) :=
  (uChartGrade g k).comap (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap

def vectorVChartGrade (g : ι → ℤ) (k : ℤ) : Submodule K (ι → BinaryLaurent K) :=
  (vChartGrade g k).comap (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap

/--
@isnad1 id=mem.2h7v.s9.95525e5b9101 from=translated src=- shape=b83bdcf6 vocab=02dbc145
-/
theorem laurentScalar_mem_overlapGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι) (hp : p ∈ overlapGrade g k) :
    laurentScalar c p ∈ overlapGrade g (k + d) :=
  laurentOperator_mem_overlapGrade _ _ g g d (fun _ => d) (fun _ => hc)
    (fun _ => rfl) k p hp

/--
@isnad1 id=mem.2h7v.s9.fade3c387b53 from=translated src=- shape=b83bdcf6 vocab=00c2c9aa
-/
theorem laurentScalar_mem_uChartGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι) (hp : p ∈ uChartGrade g k) :
    laurentScalar c p ∈ uChartGrade g (k + d) :=
  laurentOperator_mem_uChartGrade _ _ g g d (fun _ => d) (fun _ => hc)
    (fun _ => rfl) k p hp

/--
@isnad1 id=mem.2h7v.s9.16ee18140e96 from=translated src=- shape=b83bdcf6 vocab=a9e9e314
-/
theorem laurentScalar_mem_vChartGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι) (hp : p ∈ vChartGrade g k) :
    laurentScalar c p ∈ vChartGrade g (k + d) :=
  laurentOperator_mem_vChartGrade _ _ g g d (fun _ => d) (fun _ => hc)
    (fun _ => rfl) k p hp

/--
@isnad1 id=eq.1h6v.s9.d52e6926dc1d from=translated src=- shape=fe0bd6f7 vocab=ac5a828a
-/
theorem laurentScalar_projection_commutes (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ) :
    (gradeProjection g (k + d)).comp (laurentScalar c) =
      (laurentScalar c).comp (gradeProjection g k) :=
  laurentOperator_projection_commutes _ _ g g d (fun _ => d) (fun _ => hc)
    (fun _ => rfl) k

/--
@isnad1 id=mem.2h7v.s9.213fb5ee9350 from=translated src=- shape=e09b9316 vocab=51483d4f
-/
theorem scalar_mem_vectorOverlapGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (m : ι → BinaryLaurent K) (hm : m ∈ vectorOverlapGrade g k) :
    (fun i => c * m i) ∈ vectorOverlapGrade g (k + d) := by
  change freeLaurentEquiv.symm (fun i => c * m i) ∈ overlapGrade g (k + d)
  rw [freeLaurentEquiv_symm_scalar]
  exact laurentScalar_mem_overlapGrade c d hc g k _ hm

/--
@isnad1 id=mem.2h7v.s9.8aecfb449b10 from=translated src=- shape=e09b9316 vocab=e7417d75
-/
theorem scalar_mem_vectorUChartGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (m : ι → BinaryLaurent K) (hm : m ∈ vectorUChartGrade g k) :
    (fun i => c * m i) ∈ vectorUChartGrade g (k + d) := by
  change freeLaurentEquiv.symm (fun i => c * m i) ∈ uChartGrade g (k + d)
  rw [freeLaurentEquiv_symm_scalar]
  exact laurentScalar_mem_uChartGrade c d hc g k _ hm

/--
@isnad1 id=mem.2h7v.s9.55025466942e from=translated src=- shape=e09b9316 vocab=7dd2c576
-/
theorem scalar_mem_vectorVChartGrade (c : BinaryLaurent K) (d : ℤ)
    (hc : c ∈ polynomialLaurentGrade d) (g : ι → ℤ) (k : ℤ)
    (m : ι → BinaryLaurent K) (hm : m ∈ vectorVChartGrade g k) :
    (fun i => c * m i) ∈ vectorVChartGrade g (k + d) := by
  change freeLaurentEquiv.symm (fun i => c * m i) ∈ vChartGrade g (k + d)
  rw [freeLaurentEquiv_symm_scalar]
  exact laurentScalar_mem_vChartGrade c d hc g k _ hm

/-- Source index of the literal transposed cyclic action.-/
def cyclicDualSource : Fin 3 → Fin 3 := ![1, 2, 0]

/-- Dual generator shifts, allowing an arbitrary finite auxiliary shift.-/
def dualLaurentWeights (s : CubicProfile) (a : ι → ℤ) : Fin 3 × ι → ℤ :=
  fun i => (dualGeneratorWeights s i.1 : ℤ) + a i.2

/-- The actual transposed cyclic action on the overlap free module.-/
def laurentProfileZDual (q : K) (s : CubicProfile) :
    FreeLaurent K (Fin 3 × ι) →ₗ[K] FreeLaurent K (Fin 3 × ι) :=
  laurentOperator (fun i => binaryLaurentEmbedding (profileFactors q s i.1))
    (fun i => (cyclicDualSource i.1, i.2))

/--
@isnad1 id=eq.0h7v.s11.9bc5f4a9e643 from=translated src=- shape=0ca0d23f vocab=446bfd17
-/
@[simp] theorem freeLaurentEquiv_laurentProfileZDual (q : K) (s : CubicProfile)
    (p : FreeLaurent K (Fin 3 × ι)) (i : Fin 3) (a : ι) :
    freeLaurentEquiv (laurentProfileZDual q s p) (i, a) =
      cyclicZDual (fun j => binaryLaurentEmbedding (profileFactors q s j))
        (fun j => freeLaurentEquiv p (j, a)) i := by
  fin_cases i <;> simp [laurentProfileZDual, cyclicDualSource, cyclicZDual]

omit [Finite ι] in
/--
@isnad1 id=eq.0h4v.s6.be390e786a83 from=translated src=- shape=6e18de3b vocab=80cbd191
-/
theorem profileDualLaurent_degree (s : CubicProfile) (a : ι → ℤ) (i : Fin 3 × ι) :
    (profileFactorDegrees s i.1 : ℤ) + dualLaurentWeights s a i =
      1 + dualLaurentWeights s a (cyclicDualSource i.1, i.2) := by
  rcases i with ⟨i, j⟩
  cases s <;> fin_cases i <;>
    simp [dualLaurentWeights, dualGeneratorWeights, generatorWeights,
      cyclicDualSource, profileFactorDegrees] <;> omega

/--
@isnad1 id=mem.1h7v.s9.2c555e9be3c7 from=translated src=- shape=13dc1ff6 vocab=96d5cb66
-/
theorem laurentProfileZDual_mem_overlapGrade (q : K) (s : CubicProfile)
    (a : ι → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × ι))
    (hp : p ∈ overlapGrade (dualLaurentWeights s a) k) :
    laurentProfileZDual q s p ∈ overlapGrade (dualLaurentWeights s a) (k + 1) :=
  laurentOperator_mem_overlapGrade _ _ _ _ 1
    (fun i => (profileFactorDegrees s i.1 : ℤ))
    (fun i => profileFactors_laurent_mem q s i.1)
    (profileDualLaurent_degree s a) k p hp

/--
@isnad1 id=mem.1h7v.s9.ea8b32ddc6ab from=translated src=- shape=13dc1ff6 vocab=4a7b4a1d
-/
theorem laurentProfileZDual_mem_uChartGrade (q : K) (s : CubicProfile)
    (a : ι → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × ι))
    (hp : p ∈ uChartGrade (dualLaurentWeights s a) k) :
    laurentProfileZDual q s p ∈ uChartGrade (dualLaurentWeights s a) (k + 1) :=
  laurentOperator_mem_uChartGrade _ _ _ _ 1
    (fun i => (profileFactorDegrees s i.1 : ℤ))
    (fun i => profileFactors_laurent_mem q s i.1)
    (profileDualLaurent_degree s a) k p hp

/--
@isnad1 id=mem.1h7v.s9.117a2c05d5f1 from=translated src=- shape=13dc1ff6 vocab=5dfdc8f8
-/
theorem laurentProfileZDual_mem_vChartGrade (q : K) (s : CubicProfile)
    (a : ι → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × ι))
    (hp : p ∈ vChartGrade (dualLaurentWeights s a) k) :
    laurentProfileZDual q s p ∈ vChartGrade (dualLaurentWeights s a) (k + 1) :=
  laurentOperator_mem_vChartGrade _ _ _ _ 1
    (fun i => (profileFactorDegrees s i.1 : ℤ))
    (fun i => profileFactors_laurent_mem q s i.1)
    (profileDualLaurent_degree s a) k p hp

/--
@isnad1 id=eq.0h6v.s9.bcf93d605a49 from=translated src=- shape=582d31cb vocab=f50df82a
-/
theorem laurentProfileZDual_projection_commutes (q : K) (s : CubicProfile)
    (a : ι → ℤ) (k : ℤ) :
    (gradeProjection (dualLaurentWeights s a) (k + 1)).comp (laurentProfileZDual q s) =
      (laurentProfileZDual q s).comp (gradeProjection (dualLaurentWeights s a) k) :=
  gradeProjection_commutes_of_degree_shift _ _ 1 _
    (laurentProfileZDual_mem_overlapGrade q s a) k

/-- The same literal action on one three-generator coefficient module.-/
def laurentCyclicZDual (q : K) (s : CubicProfile) :
    FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3) :=
  laurentOperator (fun i => binaryLaurentEmbedding (profileFactors q s i))
    cyclicDualSource

/--
@isnad1 id=eq.0h4v.s11.3d51161449ce from=translated src=- shape=4875a364 vocab=437f76e5
-/
@[simp] theorem freeLaurentEquiv_laurentCyclicZDual (q : K) (s : CubicProfile)
    (p : FreeLaurent K (Fin 3)) :
    freeLaurentEquiv (laurentCyclicZDual q s p) =
      cyclicZDual (fun j => binaryLaurentEmbedding (profileFactors q s j))
        (freeLaurentEquiv p) := by
  funext i
  fin_cases i <;> simp [laurentCyclicZDual, cyclicDualSource, cyclicZDual]

/--
@isnad1 id=eq.0h4v.s11.a75f8d1f70af from=translated src=- shape=d73f6a46 vocab=29cd5268
-/
@[simp] theorem freeLaurentEquiv_symm_cyclicZDual (q : K) (s : CubicProfile)
    (m : Fin 3 → BinaryLaurent K) :
    freeLaurentEquiv.symm
        (cyclicZDual (fun j => binaryLaurentEmbedding (profileFactors q s j)) m) =
      laurentCyclicZDual q s (freeLaurentEquiv.symm m) := by
  apply freeLaurentEquiv.injective
  simp

end ChoppedPlane.QWeyl
