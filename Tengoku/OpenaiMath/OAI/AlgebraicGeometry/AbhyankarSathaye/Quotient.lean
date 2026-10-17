import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Identities
import Tengoku

namespace OAI

/-!
# Polynomial maps and finitely presented quotients

Ring homomorphisms preserve the defining polynomial expressions. Algebra maps
annihilating two or three relations descend to the corresponding quotient.
-/

noncomputable section
namespace AbhyankarSathaye

section Maps
variable {B D H : Type*} [CommRing B] [CommRing D]
variable [FunLike H B D] [RingHomClass H B D]

/--
@isnad1 id=eq.0h8v.s6.6de6652ecb78 from=translated src=- shape=8766dc8a vocab=d7d6458e
-/
@[simp] theorem map_S (f : H) (h u v w : B) :
    f (S h u v w) = S (f h) (f u) (f v) (f w) := by simp [S, map_ofNat]

/--
@isnad1 id=eq.0h7v.s6.57fa63f1eb63 from=translated src=- shape=e50a39ff vocab=b8b79d9e
-/
@[simp] theorem map_P (f : H) (x y s : B) :
    f (P x y s) = P (f x) (f y) (f s) := by simp [P, map_ofNat]

/--
@isnad1 id=eq.0h6v.s6.fe2937d3a793 from=translated src=- shape=c7bb2af7 vocab=a6c16509
-/
@[simp] theorem map_Alpha (f : H) (x s : B) :
    f (Alpha x s) = Alpha (f x) (f s) := by simp [Alpha, map_ofNat]

/--
@isnad1 id=eq.0h7v.s6.eb9900949a88 from=translated src=- shape=e50a39ff vocab=aa3bf60f
-/
@[simp] theorem map_Beta (f : H) (x y s : B) :
    f (Beta x y s) = Beta (f x) (f y) (f s) := by simp [Beta, map_ofNat]

end Maps

section Presentations
variable {B A D : Type*} [CommRing B] [CommRing A] [CommRing D]
variable [Algebra B A] [Algebra B D]

def lift_pair (a b : A) (f : A →ₐ[B] D) (ha : f a = 0) (hb : f b = 0) :
    (A ⧸ Ideal.span {a,b}) →ₐ[B] D := by
  have hi : Ideal.span {a,b} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

/--
@isnad1 id=eq.2h7v.s9.22e9a99a8bdd from=translated src=- shape=cef60a46 vocab=c916e13f
-/
@[simp] theorem lift_pair_mk (a b : A) (f : A →ₐ[B] D) (ha hb) (z : A) :
    lift_pair a b f ha hb (Ideal.Quotient.mk _ z) = f z := rfl

def lift_triple (a b c : A) (f : A →ₐ[B] D)
    (ha : f a = 0) (hb : f b = 0) (hc : f c = 0) :
    (A ⧸ Ideal.span {a,b,c}) →ₐ[B] D := by
  have hi : Ideal.span {a,b,c} ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact Ideal.Quotient.liftₐ _ f (fun z hz => hi hz)

/--
@isnad1 id=eq.3h8v.s10.5de8aa41ee6d from=translated src=- shape=8c883100 vocab=2bf7782a
-/
@[simp] theorem lift_triple_mk (a b c : A) (f : A →ₐ[B] D) (ha hb hc) (z : A) :
    lift_triple a b c f ha hb hc (Ideal.Quotient.mk _ z) = f z := rfl

/--
@isnad1 id=eq.0h3v.s8.3705cd7cc245 from=translated src=- shape=5d98750b vocab=e2cf2a3e
-/
theorem quotient_pair_left (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/--
@isnad1 id=eq.0h3v.s8.6caf7131ebce from=translated src=- shape=9af7a23d vocab=e2cf2a3e
-/
theorem quotient_pair_right (a b : A) : Ideal.Quotient.mk (Ideal.span {a,b}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/--
@isnad1 id=eq.0h4v.s9.774e53b1cfd3 from=translated src=- shape=36782fa9 vocab=e2cf2a3e
-/
theorem quotient_triple_first (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/--
@isnad1 id=eq.0h4v.s9.7485a48f8c99 from=translated src=- shape=1d6be795 vocab=e2cf2a3e
-/
theorem quotient_triple_second (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) b = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/--
@isnad1 id=eq.0h4v.s9.e4112a0c4065 from=translated src=- shape=1a7cdad9 vocab=e2cf2a3e
-/
theorem quotient_triple_third (a b c : A) :
    Ideal.Quotient.mk (Ideal.span {a,b,c}) c = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

end Presentations
end AbhyankarSathaye

end

end OAI
