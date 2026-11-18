import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Descent.Marks
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)

/--
@isnad1 id=eq.0h6v.s6.28a7207d36f1 from=translated src=- shape=7595664a vocab=b44f59b5
-/
theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property

omit [DecidableEq σ] [DecidableEq ι] in
/--
@isnad1 id=injectiv.0h3v.s5.b1f4779180a7 from=translated src=- shape=2c1721e5 vocab=4b97d28b
-/
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

/--
@isnad1 id=mem.1h7v.s8.214fa99ff544 from=translated src=- shape=76f96879 vocab=7acb0532
-/
theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

/--
@isnad1 id=eq.0h6v.s8.c08643a7cfab from=translated src=- shape=3b3a1ba6 vocab=7b87302f
-/
theorem primeMark_indexed_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A =
      ∑ r ∈ (I.pi (fun i => L i ∩ A)).image (indexedSlotAssignment I),
        slotAssignmentWeight I a (fun i hi => r (I.equivFin ⟨i,hi⟩)) := by
  rw [Finset.sum_image (fun q _ r _ h => indexedSlotAssignment_injective I h)]
  simpa only [indexedSlotAssignment,Equiv.symm_apply_apply] using
    primeMark_supported_assignments I L a A

end
end SevenEighths.InverseMoment

end OAI
