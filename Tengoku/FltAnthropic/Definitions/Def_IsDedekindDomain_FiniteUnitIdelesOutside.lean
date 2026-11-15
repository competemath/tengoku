import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IsDedekindDomain_FiniteUnitIdeles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

def unitIdelesOutside (S : Set (HeightOneSpectrum R)) : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | ∀ v : HeightOneSpectrum R, v ∉ S →
    (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
      ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' v _ := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y hx hy v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    obtain ⟨hy1, hy2⟩ := hy v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx1 hy1, by rw [mul_inv, Units.val_mul]; exact mul_mem hx2 hy2⟩
  inv_mem' := by
    rintro x hx v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    exact ⟨hx2, by rw [inv_inv]; exact hx1⟩

variable {R K} in
/--
@isnad1 id=iff.0h4v.s9.90183429cc39 from=translated src=- shape=c8b1262e vocab=1b8928b2
-/
theorem mem_unitIdelesOutside_iff (S : Set (HeightOneSpectrum R)) (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdelesOutside R K S ↔
      ∀ v : HeightOneSpectrum R, v ∉ S →
        (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s7.bfa1a6f5c78b from=translated src=- shape=5b81a73c vocab=09a4f25f
-/
theorem unitIdelesOutside_empty : unitIdelesOutside R K (∅ : Set (HeightOneSpectrum R)) = unitIdeles R K :=
  Subgroup.ext fun _ =>
    ⟨fun h => ⟨fun v => (h v fun hv => hv).1, fun v => (h v fun hv => hv).2⟩, fun h v _ => ⟨h.1 v, h.2 v⟩⟩

/--
@isnad1 id=le.1h4v.s8.0ec7c73119e5 from=translated src=- shape=dd7b34f4 vocab=f77d86f3
-/
theorem unitIdelesOutside_mono {S T : Set (HeightOneSpectrum R)} (h : S ⊆ T) :
    unitIdelesOutside R K S ≤ unitIdelesOutside R K T :=
  fun _ hx v hv => hx v fun hvS => hv (h hvS)

/--
@isnad1 id=le.0h3v.s8.e902b74ff161 from=translated src=- shape=3850a666 vocab=972dea08
-/
theorem unitIdeles_le_unitIdelesOutside (S : Set (HeightOneSpectrum R)) :
    unitIdeles R K ≤ unitIdelesOutside R K S :=
  fun _ hx v _ => ⟨hx.1 v, hx.2 v⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R)) : Subgroup (AdeleRing R K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S).comap
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom)

variable {R K} in
/--
@isnad1 id=iff.0h4v.s10.fe7d300f197e from=translated src=- shape=3ef4beea vocab=c17d417c
-/
theorem mem_unitIdelesOutside_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (x : (AdeleRing R K)ˣ) :
    x ∈ unitIdelesOutside R K S ↔
      Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom x ∈
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S :=
  Iff.rfl

end NumberField.AdeleRing
