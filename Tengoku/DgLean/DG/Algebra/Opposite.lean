import Tengoku.DgLean.DG.Algebra.Equiv
import Tengoku.DgLean.DG.Graded.Opposite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The opposite dg algebra

For a dg `R`-algebra `A`, the graded opposite algebra
`Aᵒᵖ = GradedOpposite (DGAlgebra.gradingSubmodule R A)` (a type synonym of `A`, with product
`op a * op b = (-1)^{|a||b|} • op (b * a)`, see `DG.Graded.Opposite`) is a dg `R`-algebra for the
same grading and the same differential, `d (op a) = op (d a)`.

## Main definitions and results

* `DG.GradedOpposite.instDGAddCommGroup`, `DG.GradedOpposite.instDGRing`,
  `DG.GradedOpposite.instDGAlgebra`: the dg algebra structure on `Aᵒᵖ`. The Leibniz rule for the
  signed opposite product is `DG.GradedOpposite.instDGRing`.
* `DG.GradedOpposite.d_op`, `DG.GradedOpposite.d_unop`: `op` and `unop` commute with `d`.
* `DG.GradedOpposite.opOpDGAlgEquiv`: the isomorphism of dg algebras `(Aᵒᵖ)ᵒᵖ ≃ A`.
* `DG.GradedOpposite.opDGAlgEquiv`: for graded commutative `A`, the isomorphism of dg algebras
  `A ≃ Aᵒᵖ` given by `op`.

The correspondence between right dg `A`-modules and left dg `Aᵒᵖ`-modules is in
`DG.Module.Opposite`.
-/

noncomputable section
open scoped DG


namespace DG

private theorem ks_eq {m n : ℤ} (h : Even (m - n)) : koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).mpr h

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [DGAddCommGroup A] [DGRing A]
  [DGAlgebra R A]

local notation "𝒜" => DGAlgebra.gradingSubmodule R A
local notation "Aᵒᵖ" => GradedOpposite (DGAlgebra.gradingSubmodule R A)

/-- The dg abelian group structure of the opposite of a dg algebra: the grading of the graded
opposite algebra and the differential `d (op a) = op (d a)`.-/
instance GradedOpposite.instDGAddCommGroup : DGAddCommGroup Aᵒᵖ where
  grading i := (GradedOpposite.grading 𝒜 i).toAddSubgroup
  decomposition :=
    { decompose' := DirectSum.decompose (GradedOpposite.grading 𝒜)
      left_inv := DirectSum.Decomposition.left_inv (ℳ := GradedOpposite.grading 𝒜)
      right_inv := DirectSum.Decomposition.right_inv (ℳ := GradedOpposite.grading 𝒜) }
  d := (GradedOpposite.op 𝒜).toLinearMap.toAddMonoidHom.comp
    ((d : A →+ A).comp (GradedOpposite.unop 𝒜).toLinearMap.toAddMonoidHom)
  d_mem' {n x} hx := by
    change GradedOpposite.op 𝒜 (d (GradedOpposite.unop 𝒜 x)) ∈ GradedOpposite.grading 𝒜 (n + 1)
    exact GradedOpposite.op_mem_grading 𝒜 (d_mem ((GradedOpposite.mem_grading_iff 𝒜).mp hx))
  d_d' x := by
    change GradedOpposite.op 𝒜 (d (d (GradedOpposite.unop 𝒜 x))) = 0
    rw [d_d, map_zero]

namespace GradedOpposite

/--
@isnad1 id=eq.0h3v.s11.8ec6cd14c3a9 from=translated src=- shape=9c5e6e54 vocab=dee90839
-/
@[simp]
theorem d_op (a : A) : d (op 𝒜 a) = op 𝒜 (d a) := rfl

/--
@isnad1 id=eq.0h3v.s11.cf2349752856 from=translated src=- shape=7fca6154 vocab=07dd14b8
-/
@[simp]
theorem d_unop (x : Aᵒᵖ) : d (unop 𝒜 x) = unop 𝒜 (d x) := rfl

/--
@isnad1 id=iff.0h4v.s10.14962ccd7007 from=translated src=- shape=46810145 vocab=fe525085
-/
theorem mem_dgGrading_iff {n : ℤ} {x : Aᵒᵖ} : x ∈ DG.grading n ↔ unop 𝒜 x ∈ DG.grading n :=
  mem_grading_iff 𝒜

/--
@isnad1 id=iff.0h4v.s10.7c088af00d2c from=translated src=- shape=425d7c61 vocab=32e1af81
-/
theorem op_mem_dgGrading_iff {n : ℤ} {a : A} : op 𝒜 a ∈ DG.grading n ↔ a ∈ DG.grading n :=
  mem_grading_iff 𝒜

/-- The opposite of a dg algebra is a dg ring: the Leibniz rule holds for the signed opposite
product.
@isnad1 id=dgring.0h2v.s6.a8e81f8b64db from=translated src=- shape=4720a692 vocab=c1fffc4c
-/
instance instDGRing : DGRing Aᵒᵖ where
  one_mem := (GradedOpposite.instGradedMonoid 𝒜).one_mem
  mul_mem := (GradedOpposite.instGradedMonoid 𝒜).mul_mem
  d_mul' {i x} hx y := by
    induction y using induction_on with
    | h_zero => simp
    | h_homogeneous y =>
      obtain ⟨y, hy⟩ := y
      rename_i j
      have ha : unop 𝒜 x ∈ DG.grading i := (mem_dgGrading_iff).mp hx
      have hb : unop 𝒜 y ∈ DG.grading j := (mem_dgGrading_iff).mp hy
      have hdx : d x ∈ DG.grading (i + 1) := d_mem hx
      have hdy : d y ∈ DG.grading (j + 1) := d_mem hy
      apply (unop 𝒜).injective
      rw [map_add, map_koszulSign_smul, ← d_unop, unop_mul 𝒜 hx hy, unop_mul 𝒜 hdx hy,
        unop_mul 𝒜 hx hdy, d_units_smul, d_mul hb, ← d_unop, ← d_unop]
      simp only [smul_add, smul_smul, ← koszulSign_add]
      rw [ks_eq (m := i * j + j) (n := (i + 1) * j) ⟨0, by ring⟩,
        ks_eq (m := i + i * (j + 1)) (n := i * j) ⟨i, by ring⟩]
      abel
    | h_add y y' hy hy' => rw [mul_add, d_add, hy, hy', d_add, mul_add, mul_add, smul_add]; abel

/--
@isnad1 id=dgalgebr.0h2v.s6.36097338ebfe from=translated src=- shape=64e1a352 vocab=c1fffc4c
-/
instance instDGAlgebra : DGAlgebra R Aᵒᵖ where
  algebraMap_mem' r := by
    rw [← op_algebraMap, op_mem_dgGrading_iff]
    exact algebraMap_mem_grading R r
  d_algebraMap' r := by
    rw [← op_algebraMap, d_op, d_algebraMap, map_zero]

/-- The double opposite of a dg algebra is isomorphic to it, via `unop ∘ unop`.-/
def opOpDGAlgEquiv : GradedOpposite (DGAlgebra.gradingSubmodule R Aᵒᵖ) ≃ᵈᵍₐ[R] A :=
  DGAlgEquiv.ofAlgEquiv (opOpAlgEquiv 𝒜) (fun hx => (opOpAlgEquiv_mem_iff 𝒜).mpr hx)
    fun _ => rfl

/--
@isnad1 id=eq.0h3v.s13.81b5716633a8 from=translated src=- shape=dd492199 vocab=97b42eca
-/
@[simp]
theorem opOpDGAlgEquiv_apply (x : GradedOpposite (DGAlgebra.gradingSubmodule R Aᵒᵖ)) :
    opOpDGAlgEquiv x = unop 𝒜 (unop (DGAlgebra.gradingSubmodule R Aᵒᵖ) x) := rfl

/-- A graded commutative dg algebra is isomorphic to its opposite, via `op`.-/
def opDGAlgEquiv [IsGradedComm 𝒜] : A ≃ᵈᵍₐ[R] Aᵒᵖ :=
  DGAlgEquiv.ofAlgEquiv (opAlgEquiv 𝒜) (fun ha => op_mem_grading 𝒜 ha) fun _ => rfl

/--
@isnad1 id=eq.0h3v.s10.8d1638419543 from=translated src=- shape=876e300e vocab=6e7f1d1e
-/
@[simp]
theorem opDGAlgEquiv_apply [IsGradedComm 𝒜] (a : A) : opDGAlgEquiv a = op 𝒜 a := rfl

end GradedOpposite

end DG

end
