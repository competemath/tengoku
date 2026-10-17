import Tengoku

namespace OAI

/-!
Transport, scaling, and descent of derivations through algebra homomorphisms.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- Literal pointwise local nilpotence; there is no uniform exponent requirement. -/
def LocallyNilpotent (D : Derivation K A A) : Prop :=
  ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0

/-- Pull a derivation back through an actual algebra equivalence. -/
def transportDerivation (e : A ≃ₐ[K] B) (D : Derivation K B B) : Derivation K A A where
  toLinearMap := e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap)
  map_one_eq_zero' := by
    change e.symm (D (e 1)) = 0
    simp
  leibniz' a b := by
    change e.symm (D (e (a * b))) = a * e.symm (D (e b)) + b * e.symm (D (e a))
    simp [Derivation.leibniz, smul_eq_mul]

/--
@isnad1 id=eq.0h6v.s8.2cd9456af9ca from=translated src=- shape=109059fc vocab=6753edf7
-/
@[simp] theorem transportDerivation_apply (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (a : A) :
    transportDerivation e D a = e.symm (D (e a)) := rfl

/--
@isnad1 id=eq.0h7v.s8.0f4e948af7d8 from=translated src=- shape=2ea12884 vocab=97712349
-/
theorem transportDerivation_iterate (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (n : ℕ) (a : A) :
    (transportDerivation e D : A → A)^[n] a = e.symm ((D : B → B)^[n] (e a)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', transportDerivation_apply,
      ih, e.apply_symm_apply]

/--
@isnad1 id=locallyn.1h5v.s6.b3d2a6f2a876 from=translated src=- shape=20a54f59 vocab=b04dd91f
-/
theorem transportDerivation_locallyNilpotent (e : A ≃ₐ[K] B)
    (D : Derivation K B B) (hD : LocallyNilpotent D) :
    LocallyNilpotent (transportDerivation e D) := by
  intro a
  obtain ⟨n, hn⟩ := hD (e a)
  exact ⟨n, by rw [transportDerivation_iterate, hn, map_zero]⟩

/--
@isnad1 id=eq.1h7v.s9.cfb564f5f00b from=translated src=- shape=b06cf7c7 vocab=97803917
-/
theorem transportDerivation_commute (e : A ≃ₐ[K] B)
    (D E : Derivation K B B) (hDE : ∀ b, D (E b) = E (D b)) (a : A) :
    transportDerivation e D (transportDerivation e E a) =
      transportDerivation e E (transportDerivation e D a) := by
  simp only [transportDerivation_apply, e.apply_symm_apply, hDE]

/-- Multiplication by a kernel element gives the exact nth-iterate formula.
@isnad1 id=eq.1h6v.s9.cc72e3a601fa from=translated src=- shape=640a7916 vocab=023da00e
-/
theorem scaleDerivation_iterate (D : Derivation K A A) (c : A) (hc : D c = 0)
    (n : ℕ) (a : A) :
    ((c • D : Derivation K A A) : A → A)^[n] a = c^n * (D : A → A)^[n] a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.smul_apply]
      simp only [smul_eq_mul, Derivation.leibniz, Derivation.leibniz_pow, hc,
        smul_zero, mul_zero, add_zero, Function.iterate_succ_apply']
      rw [pow_succ]
      ring

/--
@isnad1 id=locallyn.2h4v.s8.bdec3f86da30 from=translated src=- shape=755d2c81 vocab=0bd828de
-/
theorem scaleDerivation_locallyNilpotent (D : Derivation K A A) (c : A)
    (hc : D c = 0) (hD : LocallyNilpotent D) : LocallyNilpotent (c • D) := by
  intro a
  obtain ⟨n, hn⟩ := hD a
  exact ⟨n, by rw [scaleDerivation_iterate D c hc, hn, mul_zero]⟩

/-- Different multipliers may be used if both lie in both kernels.
@isnad1 id=eq.3h7v.s10.db31aab238ca from=translated src=- shape=4d6aa69c vocab=bff74346
-/
theorem scaleDerivation_commute (D E : Derivation K A A) (a b : A)
    (hDb : D b = 0) (hEa : E a = 0) (hDE : ∀ x, D (E x) = E (D x)) (x : A) :
    (a • D) ((b • E) x) = (b • E) ((a • D) x) := by
  simp only [Derivation.smul_apply, smul_eq_mul, Derivation.leibniz, hDb, hEa,
    mul_zero, add_zero, hDE]
  ring

/--
@isnad1 id=iff.1h5v.s8.2d14404abc09 from=translated src=- shape=0d0856a1 vocab=6b3e3389
-/
theorem scaleDerivation_kernel [IsDomain A] (D : Derivation K A A)
    (c : A) (hc : c ≠ 0) (a : A) : (c • D) a = 0 ↔ D a = 0 := by
  simp only [Derivation.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]

/-- A specified function whose image intertwines a derivation through an
injective algebra map automatically satisfies all derivation laws. -/
def descendDerivation (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a)) :
    Derivation K A A where
  toFun := d
  map_add' a b := by
    apply hι
    simp only [hd, map_add]
  map_smul' k a := by
    change d (k • a) = k • d a
    apply hι
    simp only [hd, map_smul, Derivation.map_smul]
  map_one_eq_zero' := by
    change d 1 = 0
    apply hι
    simp only [hd, map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    change d (a * b) = a * d b + b * d a
    apply hι
    simp only [hd, smul_eq_mul, map_mul, map_add, Derivation.leibniz]

/--
@isnad1 id=eq.2h7v.s8.6c5a336e8fef from=translated src=- shape=68f49b52 vocab=8907d72d
-/
@[simp] theorem descendDerivation_apply (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a)) (a : A) :
    descendDerivation ι hι D d hd a = d a := rfl

/--
@isnad1 id=eq.2h8v.s9.22c060f30cbc from=translated src=- shape=e2a36770 vocab=b5b3263a
-/
theorem descendDerivation_iterate (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a))
    (n : ℕ) (a : A) :
    ι ((descendDerivation ι hι D d hd : A → A)^[n] a) =
      (D : B → B)^[n] (ι a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', descendDerivation_apply, hd, ih]

/--
@isnad1 id=locallyn.3h6v.s8.e4aee46a31f3 from=translated src=- shape=d2b73dab vocab=d8b00df7
-/
theorem descendDerivation_locallyNilpotent (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (d : A → A) (hd : ∀ a, ι (d a) = D (ι a))
    (hD : LocallyNilpotent D) : LocallyNilpotent (descendDerivation ι hι D d hd) := by
  intro a
  obtain ⟨n, hn⟩ := hD (ι a)
  refine ⟨n, hι ?_⟩
  rw [descendDerivation_iterate, hn, map_zero]

/--
@isnad1 id=eq.4h9v.s10.0c35c8a27e86 from=translated src=- shape=106a702e vocab=8907d72d
-/
theorem descendDerivation_commute (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D E : Derivation K B B) (d e : A → A)
    (hd : ∀ a, ι (d a) = D (ι a)) (he : ∀ a, ι (e a) = E (ι a))
    (hDE : ∀ b, D (E b) = E (D b)) (a : A) :
    descendDerivation ι hι D d hd (descendDerivation ι hι E e he a) =
      descendDerivation ι hι E e he (descendDerivation ι hι D d hd a) := by
  apply hι
  simp only [descendDerivation_apply, hd, he, hDE]

/-- Existence of descent from the precise closure obligation.
@isnad1 id=ex.2h5v.s9.8b2b78e5830e from=translated src=- shape=1d1f97b8 vocab=d2e99359
-/
theorem exists_descendDerivation (ι : A →ₐ[K] B) (hι : Function.Injective ι)
    (D : Derivation K B B) (hstable : ∀ a : A, ∃ b : A, ι b = D (ι a)) :
    ∃ d : Derivation K A A, ∀ a, ι (d a) = D (ι a) := by
  choose d hd using hstable
  exact ⟨descendDerivation ι hι D d hd, hd⟩

end AbhyankarSathaye.CommutingDerivations

end

end OAI
