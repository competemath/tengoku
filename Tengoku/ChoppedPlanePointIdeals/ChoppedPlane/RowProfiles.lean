module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GenericHilbertBurchOpen
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.GenericLinearMatrix
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FerrersCounts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The quadratic-row and linear-row profile

The full Hilbert--Burch parameter family has independent coefficients in its
quadratic and linear entries. Its projection to the linear rows is a
surjective polynomial family, so the matrix witnesses give determinant opens
in the same parameter space as the cofactors. The quotient calculation uses
the actual maximal-minor ideal and Hilbert--Burch exactness.
-/

noncomputable section

namespace ChoppedPlane

open Module MvPolynomial

variable {K : Type*} [Field K]

/-- The number of columns when there are `r` quadratic and `a` linear rows.-/
def positiveRowColumns (r a : ℕ) : ℕ := r + a - 1

/-- Quadratic rows come first, followed by the linear rows.-/
def positiveRowProfile (r a : ℕ) : Fin (positiveRowColumns r a + 1) → ℕ :=
  fun i => if i.val < r then 2 else 1

/--
@isnad1 id=eq.1h2v.s5.484ee01d62fd from=translated src=- shape=f43758c0 vocab=d3d73ecb
-/
theorem positiveRowColumns_rows (r a : ℕ) (hr : 0 < r) :
    positiveRowColumns r a + 1 = r + a := by
  unfold positiveRowColumns
  omega

/-- Inclusion of the linear-row indices in the full row index set.-/
def positiveLinearRowIndex {r a : ℕ} (hr : 0 < r) (i : Fin a) :
    Fin (positiveRowColumns r a + 1) := ⟨r + i.val, by
      have h := positiveRowColumns_rows r a hr
      omega⟩

/--
@isnad1 id=eq.1h3v.s5.e9f68714d890 from=translated src=- shape=acc24d07 vocab=e76e6ad1
-/
@[simp] theorem positiveLinearRowIndex_val {r a : ℕ} (hr : 0 < r) (i : Fin a) :
    (positiveLinearRowIndex hr i).val = r + i.val := rfl

/--
@isnad1 id=eq.1h3v.s5.094c53d06340 from=translated src=- shape=d086f84a vocab=b19df4fa
-/
@[simp] theorem positiveRowProfile_linear {r a : ℕ} (hr : 0 < r) (i : Fin a) :
    positiveRowProfile r a (positiveLinearRowIndex hr i) = 1 := by
  simp [positiveRowProfile, positiveLinearRowIndex]

/-- Projection of a genuinely homogeneous row matrix to its linear rows.-/
def positiveLinearBlock {r a : ℕ} (hr : 0 < r) :
    HomogeneousRowMatrix K (positiveRowProfile r a) →ₗ[K]
      LinearMatrix K a (positiveRowColumns r a) where
  toFun B i j := ⟨(B (positiveLinearRowIndex hr i) j).val, by
    have h := (B (positiveLinearRowIndex hr i) j).property
    simpa only [positiveRowProfile_linear] using h⟩
  map_add' B C := by funext i j; apply Subtype.ext; rfl
  map_smul' k B := by funext i j; apply Subtype.ext; rfl

/--
@isnad1 id=eq.1h6v.s12.f78df6f894b0 from=translated src=- shape=d48dff94 vocab=3365a83f
-/
@[simp] theorem positiveLinearBlock_val {r a : ℕ} (hr : 0 < r)
    (B : HomogeneousRowMatrix K (positiveRowProfile r a))
    (i : Fin a) (j : Fin (positiveRowColumns r a)) :
    (positiveLinearBlock hr B i j).val = (B (positiveLinearRowIndex hr i) j).val := rfl

/-- Fill the quadratic rows with zero and the linear rows with a chosen matrix.-/
def positiveRowLift {r a : ℕ} (hr : 0 < r)
    (L : LinearMatrix K a (positiveRowColumns r a)) :
    HomogeneousRowMatrix K (positiveRowProfile r a) := fun i j =>
  if hi : i.val < r then 0 else
    ⟨(L ⟨i.val - r, by
      have h := positiveRowColumns_rows r a hr
      have hib := i.isLt
      omega⟩ j).val, by
      have hf := (L ⟨i.val - r, by
        have h := positiveRowColumns_rows r a hr
        have hib := i.isLt
        omega⟩ j).property
      simpa only [positiveRowProfile, hi, ite_false] using hf⟩

/--
@isnad1 id=eq.1h4v.s12.adacb5c89506 from=translated src=- shape=331b279a vocab=55228893
-/
@[simp] theorem positiveLinearBlock_lift {r a : ℕ} (hr : 0 < r)
    (L : LinearMatrix K a (positiveRowColumns r a)) :
    positiveLinearBlock hr (positiveRowLift hr L) = L := by
  funext i j
  apply Subtype.ext
  change (positiveRowLift hr L (positiveLinearRowIndex hr i) j).val = (L i j).val
  simp [positiveRowLift, positiveLinearRowIndex]

/--
@isnad1 id=surjecti.1h3v.s12.4a077047c7c3 from=translated src=- shape=112645f8 vocab=8cd7071c
-/
theorem positiveLinearBlock_surjective {r a : ℕ} (hr : 0 < r) :
    Function.Surjective (positiveLinearBlock (K := K) (a := a) hr) := by
  intro L
  exact ⟨positiveRowLift hr L, positiveLinearBlock_lift hr L⟩

/-- The linear block of the full independent row-coefficient family.-/
def universalPositiveLinearBlock {r a : ℕ} (hr : 0 < r) :
    (RowMatrixParameter (positiveRowProfile r a) → K) →ₗ[K]
      LinearMatrix K a (positiveRowColumns r a) :=
  (positiveLinearBlock hr).comp (universalRowMatrix (positiveRowProfile r a))

/--
@isnad1 id=ispolyno.1h3v.s11.158c5d6cb187 from=translated src=- shape=c76343fc vocab=3c9901ff
-/
theorem universalPositiveLinearBlock_isPolynomialFamily {r a : ℕ} (hr : 0 < r) :
    IsPolynomialFamily (universalPositiveLinearBlock (K := K) (a := a) hr) := by
  classical
  exact isPolynomialFamily_linear _

/--
@isnad1 id=surjecti.1h3v.s11.63d301068a7d from=translated src=- shape=19250dbb vocab=d6c0a888
-/
theorem universalPositiveLinearBlock_surjective {r a : ℕ} (hr : 0 < r) :
    Function.Surjective (universalPositiveLinearBlock (K := K) (a := a) hr) := by
  intro L
  refine ⟨rowMatrixCoordinates (positiveRowProfile r a) (positiveRowLift hr L), ?_⟩
  change positiveLinearBlock hr
    (universalRowMatrix _ (rowMatrixCoordinates _ (positiveRowLift hr L))) = L
  rw [universalRowMatrix_coordinates, positiveLinearBlock_lift]

/-- A genuine matrix witness gives an all-twist open in the full row parameter space.
@isnad1 id=ex.2h3v.s11.97fa10907396 from=translated src=- shape=0a637feb vocab=20cee574
-/
theorem positiveRow_linearBlock_allTwists_open {r a : ℕ} (hr : 2 ≤ r)
    (hw : ∃ L : LinearMatrix K a (positiveRowColumns r a),
      ∀ t, LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial (RowMatrixParameter (positiveRowProfile r a)) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalPositiveLinearBlock (by omega : 0 < r) u) t :=
  linearMatrixFamily_allTwists_principal_open_of_surjective
    (universalPositiveLinearBlock (by omega : 0 < r))
    (universalPositiveLinearBlock_isPolynomialFamily _)
    (universalPositiveLinearBlock_surjective _) (by unfold positiveRowColumns; omega) hw

/--
@isnad1 id=eq.1h2v.s6.24ce464aeb52 from=translated src=- shape=c9fe433d vocab=92922a09
-/
theorem positiveRowProfile_sum (r a : ℕ) (hr : 0 < r) :
    (∑ i, positiveRowProfile r a i) = 2 * r + a := by
  calc
    (∑ i, positiveRowProfile r a i) =
        ∑ i : Fin (r + a), Ferrers.positiveProfile r a i :=
      Fintype.sum_equiv (finCongr (positiveRowColumns_rows r a hr)) _ _ (fun _ => rfl)
    _ = 2 * r + a := Ferrers.positiveProfile_sum r a

/-- Sum a function of the row degree, separating the two blocks.
@isnad1 id=eq.1h3v.s7.df1b3d9e81bb from=translated src=- shape=016a32fc vocab=a94c8603
-/
theorem positiveRowProfile_function_sum (r a : ℕ) (hr : 0 < r) (g : ℕ → ℤ) :
    (∑ i, g (positiveRowProfile r a i)) = (r : ℤ) * g 2 + (a : ℤ) * g 1 := by
  have heq : (∑ i, g (positiveRowProfile r a i)) =
      ∑ i : Fin (r + a), g (Ferrers.positiveProfile r a i) :=
    Fintype.sum_equiv (finCongr (positiveRowColumns_rows r a hr)) _ _ (fun _ => rfl)
  rw [heq, Fin.sum_univ_add]
  have hfirst (i : Fin r) : Ferrers.positiveProfile r a (Fin.castAdd a i) = 2 := by
    simp [Ferrers.positiveProfile, i.isLt]
  have hlast (i : Fin a) : Ferrers.positiveProfile r a (Fin.natAdd r i) = 1 := by
    simp [Ferrers.positiveProfile]
  simp_rw [hfirst, hlast]
  simp

/-- The generator degree of the quadratic-row cofactors.-/
def positiveRowGeneratorDegree (r a : ℕ) : ℕ := 2 * r + a - 2

/--
@isnad1 id=and.1h2v.s5.2ed06f206fe1 from=translated src=- shape=22486256 vocab=273ff544
-/
theorem positiveRow_counts {r a : ℕ} (hr : 0 < r) :
    aCount (positiveRowGeneratorDegree r a) r = a ∧
      cCount (positiveRowGeneratorDegree r a) r = positiveRowColumns r a := by
  dsimp [aCount, cCount, positiveRowGeneratorDegree, positiveRowColumns]
  omega

/-- Hilbert--Burch computes the literal quotient Hilbert function for this row profile.
@isnad1 id=eq.2h5v.s6.0de29d3202f9 from=translated src=- shape=26873794 vocab=d6035efb
-/
theorem positiveRow_minorHilbertFunction
    {r a : ℕ} (hr : 0 < r)
    (B : HomogeneousRowMatrix K (positiveRowProfile r a))
    (hprimitive : PrimitiveMaximalMinors (rowMatrixVal (positiveRowProfile r a) B))
    (t : ℤ) :
    (minorHilbertFunction (rowMatrixVal (positiveRowProfile r a) B) t : ℤ) =
      hbCoefficient (positiveRowGeneratorDegree r a) r t := by
  rw [minorHilbertFunction_at_degree _ _
    (rowMatrixVal_homogeneous _ B) hprimitive, positiveRowProfile_sum r a hr]
  rw [positiveRowProfile_function_sum r a hr
    (fun j => N₂ (t - ((2 * r + a : ℕ) : ℤ) + (j : ℤ)))]
  obtain ⟨ha, hc⟩ := positiveRow_counts (a := a) hr
  have hd : (positiveRowGeneratorDegree r a : ℤ) = 2 * r + a - 2 := by
    unfold positiveRowGeneratorDegree
    omega
  dsimp [hbCoefficient]
  rw [ha, hc, hd]
  have h₂ : t - (2 * (r : ℤ) + a) + 2 = t - (2 * (r : ℤ) + a - 2) := by ring
  have h₁ : t - (2 * (r : ℤ) + a) + 1 = t - (2 * (r : ℤ) + a - 2) - 1 := by ring
  have h₀ : t - (2 * (r : ℤ) + a) = t - (2 * (r : ℤ) + a - 2) - 2 := by ring
  rw [h₂, h₁, h₀]
  ring

/-- Above the generator degree, the actual quotient has `N(d) - r` dimensions.
@isnad1 id=eq.2h5v.s7.c8d8e2c8ac6f from=translated src=- shape=74c67c31 vocab=3020d49e
-/
theorem positiveRow_minorHilbertFunction_formula
    {r a : ℕ} (hr : 0 < r)
    (B : HomogeneousRowMatrix K (positiveRowProfile r a))
    (hprimitive : PrimitiveMaximalMinors (rowMatrixVal (positiveRowProfile r a) B))
    (t : ℤ) :
    (minorHilbertFunction (rowMatrixVal (positiveRowProfile r a) B) t : ℤ) =
      if t < (positiveRowGeneratorDegree r a : ℤ) then N₂ t
        else (N (positiveRowGeneratorDegree r a) : ℤ) - r := by
  rw [positiveRow_minorHilbertFunction hr B hprimitive, hbCoefficient_formula]

end ChoppedPlane
