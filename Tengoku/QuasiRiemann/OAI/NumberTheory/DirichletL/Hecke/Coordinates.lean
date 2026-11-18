import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.Family
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

private theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen

/--
@isnad1 id=surjecti.0h0v.s4.59bab4e38e33 from=translated src=- shape=e37279c3 vocab=32849c8b
-/
theorem coordinateElement_surjective :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum

def intQuotientHom (χ : Character) : ℤ →+ (O ⧸ χ.modulus) :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)

def zmodQuotientHom (χ : Character) : ZMod χ.period →+ (O ⧸ χ.modulus) :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩

/--
@isnad1 id=eq.0h2v.s9.6d86e99116c2 from=translated src=- shape=cd508302 vocab=b97f530d
-/
@[simp] theorem zmodQuotientHom_intCast (χ : Character) (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _

/--
@isnad1 id=eq.0h2v.s9.af4cc5471f75 from=translated src=- shape=cd508302 vocab=85ed6a85
-/
@[simp] theorem zmodQuotientHom_natCast (χ : Character) (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)

def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

/--
@isnad1 id=eq.0h3v.s9.5d721233a028 from=translated src=- shape=044b52aa vocab=90850392
-/
@[simp] theorem coordinateQuotientHom_intCast (χ : Character) (a b : ℤ) :
    coordinateQuotientHom χ (a, b) =
      Ideal.Quotient.mk χ.modulus (coordinateElement a b) := by
  simp only [coordinateQuotientHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zmodQuotientHom_intCast, coordinateElement, map_add, map_mul]

/--
@isnad1 id=surjecti.0h1v.s9.b45170ffff07 from=translated src=- shape=79f2698c vocab=53163526
-/
theorem coordinateQuotientHom_surjective (χ : Character) :
    Function.Surjective (coordinateQuotientHom χ) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, hab⟩ := coordinateElement_surjective z
  change coordinateElement a b = z at hab
  exact ⟨(a,b), by rw [coordinateQuotientHom_intCast, hab]⟩

/--
@isnad1 id=eq.0h2v.s9.ef0bc9d43a19 from=translated src=- shape=d5a61850 vocab=81c5077c
-/
theorem coefficients_eq_quotient_character (χ : Character)
    (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]

end SevenEighths.HeckeCoordinates

end

end OAI
