import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitsComponent (v : HeightOneSpectrum R) :
    (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom
    (fun v : HeightOneSpectrum R => v.adicCompletion K) v).toMonoidHom

variable {R K} in
/--
@isnad1 id=eq.0h4v.s9.5f6786230fad from=translated src=- shape=6a009171 vocab=8b10536b
-/
@[simp]
theorem val_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((unitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in
/--
@isnad1 id=eq.0h4v.s10.63527f39ccea from=translated src=- shape=be61b722 vocab=4d18feeb
-/
theorem val_inv_unitsComponent (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (((unitsComponent R K v x)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v :=
  rfl

variable {R K} in

/--
@isnad1 id=iff.0h4v.s9.5766e7669f3d from=translated src=- shape=9653889d vocab=36aae303
-/
theorem integer_and_inv_integer_iff_valuation_eq_one (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    ((x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K)
      ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hmul : (x : FiniteAdeleRing R K) v * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
    rw [← val_unitsComponent, ← val_inv_unitsComponent, Units.mul_inv]
  have hab : Valued.v ((x : FiniteAdeleRing R K) v)
      * Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, hmul, map_one]
  have ha0 : Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := left_ne_zero_of_mul_eq_one hab
  rw [← inv_eq_of_mul_eq_one_right hab]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 ha0)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

def ideleBox (S : Set (HeightOneSpectrum R)) (H : (v : HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ) :
    Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {x | (∀ v ∈ S, unitsComponent R K v x ∈ H v) ∧
    ∀ v : HeightOneSpectrum R, v ∉ S →
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' := ⟨fun v _ => by rw [map_one]; exact one_mem _,
    fun v _ => ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun v hv => by rw [map_mul]; exact mul_mem (hx1 v hv) (hy1 v hv), fun v hv => ?_⟩
    obtain ⟨hx, hx'⟩ := hx2 v hv
    obtain ⟨hy, hy'⟩ := hy2 v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx hy, by rw [mul_inv, Units.val_mul]; exact mul_mem hx' hy'⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v hv => by rw [map_inv]; exact inv_mem (hx1 v hv),
      fun v hv => ⟨(hx2 v hv).2, by rw [inv_inv]; exact (hx2 v hv).1⟩⟩

/--
@isnad1 id=eq.0h3v.s9.e7058b341305 from=translated src=- shape=3da6660f vocab=10cb06f9
-/
theorem ideleBox_top (S : Set (HeightOneSpectrum R)) : ideleBox R K S ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ => ⟨fun h => h.2, fun h => ⟨fun _ _ => Subgroup.mem_top _, h⟩⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def finitePartUnits : (AdeleRing R K)ˣ →* (IsDedekindDomain.FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom

variable {R K} in
/--
@isnad1 id=eq.0h3v.s9.d6413a132a49 from=translated src=- shape=93b964a5 vocab=39c7cfd2
-/
@[simp]
theorem val_finitePartUnits (x : (AdeleRing R K)ˣ) :
    ((finitePartUnits R K x : (IsDedekindDomain.FiniteAdeleRing R K)ˣ) : IsDedekindDomain.FiniteAdeleRing R K)
      = (x : AdeleRing R K).2 :=
  rfl

noncomputable def finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) :
    (AdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitsComponent R K v).comp (finitePartUnits R K)

noncomputable def infiniteUnitsComponent (w : InfinitePlace K) : (AdeleRing R K)ˣ →* (w.Completion)ˣ :=
  Units.map ((Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) w).comp
    (RingHom.fst (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K))).toMonoidHom

variable {R K} in
/--
@isnad1 id=eq.0h4v.s10.8c43114e1c14 from=translated src=- shape=9142dda0 vocab=b2f897fb
-/
@[simp]
theorem val_finiteUnitsComponent (v : IsDedekindDomain.HeightOneSpectrum R) (x : (AdeleRing R K)ˣ) :
    ((finiteUnitsComponent R K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : AdeleRing R K).2 v :=
  rfl

variable {R K} in
/--
@isnad1 id=eq.0h4v.s9.8f58c7e9fd02 from=translated src=- shape=15d5ed8a vocab=7d8ec930
-/
@[simp]
theorem val_infiniteUnitsComponent (w : InfinitePlace K) (x : (AdeleRing R K)ˣ) :
    ((infiniteUnitsComponent R K w x : (w.Completion)ˣ) : w.Completion) = (x : AdeleRing R K).1 w :=
  rfl

def ideleBox (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) : Subgroup (AdeleRing R K)ˣ where
  carrier := {x | finitePartUnits R K x ∈ IsDedekindDomain.FiniteAdeleRing.ideleBox R K S H ∧
    ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, fun w => by rw [map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_mul]; exact mul_mem hx1 hy1, fun w => by rw [map_mul]; exact mul_mem (hx2 w) (hy2 w)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [map_inv]; exact inv_mem hx1, fun w => by rw [map_inv]; exact inv_mem (hx2 w)⟩

variable {R K} in

/--
@isnad1 id=iff.0h6v.s11.0e8a8ea47bb1 from=translated src=- shape=7f87ece8 vocab=0241c539
-/
theorem mem_ideleBox_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (H : (v : IsDedekindDomain.HeightOneSpectrum R) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ) (x : (AdeleRing R K)ˣ) :
    x ∈ ideleBox R K S H Hinf ↔
      ((∀ v ∈ S, finiteUnitsComponent R K v x ∈ H v) ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum R, v ∉ S →
          (x : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K ∧
            ((x⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K).2 v ∈ v.adicCompletionIntegers K) ∧
      ∀ w : InfinitePlace K, infiniteUnitsComponent R K w x ∈ Hinf w :=
  Iff.rfl

/--
@isnad1 id=eq.0h3v.s9.de3388a2ff1b from=translated src=- shape=c95020b3 vocab=78cdba3d
-/
theorem ideleBox_top_top (S : Set (IsDedekindDomain.HeightOneSpectrum R)) :
    ideleBox R K S ⊤ ⊤ = unitIdelesOutside R K S :=
  Subgroup.ext fun _ =>
    ⟨fun h => (IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).le h.1,
      fun h => ⟨(IsDedekindDomain.FiniteAdeleRing.ideleBox_top R K S).ge h, fun _ => Subgroup.mem_top _⟩⟩

end NumberField.AdeleRing
