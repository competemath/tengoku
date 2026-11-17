import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.OrbitaVertici

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Trasporto dell'orbita del sottogruppo semplice sotto una coniugazione
delle riflessioni semplici.

La coercizione da `simpleGen P hreg F i` a `Isom n` si riduce
definizionalmente a `simpleReflection P hreg F i`: per definizione,
`simpleGen` e' il sottotipo di `symGroup P` con quel valore sottostante.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un coniugio dei generatori trasporta ogni elemento del sottogruppo
semplice, con la stessa relazione puntuale.-/
private theorem simpleSubgroup_conj_exists
    (P Q : ConvexPolytope n) (hregP : P.IsRegular) (hregQ : Q.IsRegular)
    (F : P.Flag) (G : Q.Flag) (Φ : E n ≃ᵃⁱ[ℝ] E n)
    (hconj : ∀ i x,
      Φ (simpleReflection P hregP F i x) =
        simpleReflection Q hregQ G i (Φ x))
    {w : symGroup P} (hw : w ∈ simpleSubgroup P hregP F) :
    ∃ w' : symGroup Q,
      w' ∈ simpleSubgroup Q hregQ G ∧
        ∀ x, (w' : Isom n) (Φ x) = Φ ((w : Isom n) x) := by
  change w ∈ Subgroup.closure (Set.range (simpleGen P hregP F)) at hw
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      refine ⟨simpleGen Q hregQ G i, simpleGen_mem Q hregQ G i, ?_⟩
      intro x
      change simpleReflection Q hregQ G i (Φ x) =
        Φ (simpleReflection P hregP F i x)
      exact (hconj i x).symm
  | one =>
      refine ⟨1, one_mem _, ?_⟩
      intro x
      simp
  | mul a b ha hb iha ihb =>
      obtain ⟨a', ha'mem, ha'⟩ := iha
      obtain ⟨b', hb'mem, hb'⟩ := ihb
      refine ⟨a' * b', mul_mem ha'mem hb'mem, ?_⟩
      intro x
      change (a' : Isom n) ((b' : Isom n) (Φ x)) =
        Φ ((a : Isom n) ((b : Isom n) x))
      rw [hb' x, ha' ((b : Isom n) x)]
  | inv a ha iha =>
      obtain ⟨a', ha'mem, ha'⟩ := iha
      refine ⟨a'⁻¹, inv_mem ha'mem, ?_⟩
      intro x
      apply (a' : Isom n).injective
      rw [ha' (((a⁻¹ : symGroup P) : Isom n) x)]
      simp

/-- Una coniugazione affine delle riflessioni semplici trasporta
esattamente l'orbita puntuale del sottogruppo semplice.-/
theorem simpleVertexOrbit_conj
    (P Q : ConvexPolytope n) (hregP : P.IsRegular) (hregQ : Q.IsRegular)
    (F : P.Flag) (G : Q.Flag) (Φ : E n ≃ᵃⁱ[ℝ] E n)
    (hconj : ∀ i x,
      Φ (simpleReflection P hregP F i x) =
        simpleReflection Q hregQ G i (Φ x)) (v : E n) :
    (⇑Φ) '' simpleVertexOrbit P hregP F v =
      simpleVertexOrbit Q hregQ G (Φ v) := by
  ext u
  constructor
  · rintro ⟨z, ⟨w, hw, hwz⟩, rfl⟩
    obtain ⟨w', hw'mem, hw'⟩ :=
      simpleSubgroup_conj_exists P Q hregP hregQ F G Φ hconj hw
    refine ⟨w', hw'mem, ?_⟩
    rw [← hwz]
    exact hw' v
  · intro hu
    obtain ⟨w, hwmem, hwu⟩ := hu
    have hconj_symm : ∀ i y,
        Φ.symm (simpleReflection Q hregQ G i y) =
          simpleReflection P hregP F i (Φ.symm y) := by
      intro i y
      apply Φ.injective
      simpa using (hconj i (Φ.symm y)).symm
    obtain ⟨w', hw'mem, hw'⟩ :=
      simpleSubgroup_conj_exists Q P hregQ hregP G F Φ.symm
        hconj_symm hwmem
    refine ⟨(w' : Isom n) v, ⟨w', hw'mem, rfl⟩, ?_⟩
    calc
      Φ ((w' : Isom n) v) =
          Φ (Φ.symm ((w : Isom n) (Φ v))) := by
            apply congrArg Φ
            simpa using hw' (Φ v)
      _ = (w : Isom n) (Φ v) := Φ.apply_symm_apply _
      _ = u := hwu

/-- Se tutte le riflessioni semplici fissano un punto, la sua orbita
sotto il sottogruppo da esse generato e' il singoletto di quel punto.-/
theorem simpleVertexOrbit_eq_singleton_of_fixed
    (P : ConvexPolytope n) (hreg : P.IsRegular)
    (F : P.Flag) (v : E n)
    (hfix : ∀ i, simpleReflection P hreg F i v = v) :
    simpleVertexOrbit P hreg F v = {v} := by
  have all_fix : ∀ (w : symGroup P),
      w ∈ simpleSubgroup P hreg F → (w : Isom n) v = v := by
    intro w hw
    change w ∈ Subgroup.closure (Set.range (simpleGen P hreg F)) at hw
    induction hw using Subgroup.closure_induction with
    | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        change simpleReflection P hreg F i v = v
        exact hfix i
    | one => simp
    | mul a b ha hb iha ihb =>
        change (a : Isom n) ((b : Isom n) v) = v
        rw [ihb, iha]
    | inv a ha iha =>
        apply (a : Isom n).injective
        simp [iha]
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using all_fix w hw
  · intro hu
    have huv : u = v := by simpa using hu
    subst u
    exact ⟨1, one_mem _, by simp⟩

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
