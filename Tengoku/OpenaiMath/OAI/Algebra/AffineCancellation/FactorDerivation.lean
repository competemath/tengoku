import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.FactorDerivation
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)
def value (s : S) : S := Classical.choose (h s)
omit [IsDomain R] in
/--
@isnad1 id=eq.1h7v.s8.ec3b1f4e6024 from=translated src=- shape=829d2796 vocab=15468a19
-/
lemma specification (s : S) : D (f s)=c*f (value f D c h s) := Classical.choose_spec (h s)
include hf hc in
/--
@isnad1 id=eq.3h8v.s8.53ba38c932a1 from=translated src=- shape=1c12f345 vocab=da597397
-/
lemma value_add (s t : S) : value f D c h (s+t)=value f D c h s+value f D c h t := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_add,map_add,map_add,mul_add,← specification,← specification]
include hf hc in
/--
@isnad1 id=eq.3h8v.s8.1710e5181d1a from=translated src=- shape=9847c1d8 vocab=f230cb3c
-/
lemma value_smul (a : k) (s : S) : value f D c h (a • s)=a • value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_smul,Derivation.map_smul,map_smul,mul_smul_comm,← specification]
include hf hc in
/--
@isnad1 id=eq.3h8v.s8.1c9d17cb6111 from=translated src=- shape=9befb15d vocab=da597397
-/
lemma value_mul (s t : S) :
    value f D c h (s*t)=s*value f D c h t+t*value f D c h s := by
  apply hf
  apply mul_left_cancel₀ hc
  rw [← specification,map_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul,
    specification f D c h s,specification f D c h t,map_add,map_mul,map_mul]
  ring
def derivation : Derivation k S S where
  toLinearMap := {
    toFun := value f D c h
    map_add' := value_add f hf D c hc h
    map_smul' := value_smul f hf D c hc h }
  map_one_eq_zero' := by
    apply hf
    apply mul_left_cancel₀ hc
    change c*f (value f D c h 1)=c*f 0
    rw [← specification,map_one,Derivation.map_one_eq_zero,map_zero,mul_zero]
  leibniz' s t := by
    exact value_mul f hf D c hc h s t
/--
@isnad1 id=eq.3h7v.s9.b1354d633b56 from=translated src=- shape=85655037 vocab=53ba8782
-/
lemma apply_spec (s : S) : D (f s)=c*f (derivation f hf D c hc h s) := specification f D c h s
end ComplexCancellation.FactorDerivation

end

end OAI
