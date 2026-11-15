import Tengoku.Seed.Combinatorics.SimpleGraph.Walk.Maps
import Tengoku.Seed.Combinatorics.SimpleGraph.Walk.Operations
import Tengoku.Seed.Algebra.BigOperators.Group.List.Basic
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace CerednikDrinfeld
namespace Mumford

variable {W : Type} [DecidableEq W] {𝒯 : SimpleGraph W}

namespace WalkOverlapAux
variable {α : Type}

/--
@isnad1 id=eq.0h3v.s5.86c7308be2b7 from=translated src=- shape=182f8821 vocab=23261049
-/
theorem sum_map_neg_int (l : List α) (f : α → ℤ) : (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/--
@isnad1 id=eq.0h4v.s6.5c61cb6bd456 from=translated src=- shape=7e9904fe vocab=00229ad9
-/
theorem sum_map_add_int (l : List α) (f g : α → ℤ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

omit [DecidableEq W] in
/--
@isnad1 id=injectiv.1h5v.s5.67cf1fe0ec11 from=translated src=- shape=cfed0165 vocab=a0b7b066
-/
theorem mapDart_injective {W' : Type} {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯') (hf : Function.Injective f) :
    Function.Injective f.mapDart := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have h' := congrArg SimpleGraph.Dart.toProd h
  simp only [SimpleGraph.Hom.mapDart, Prod.map, Prod.mk.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  cases hf h1
  cases hf h2
  rfl

end WalkOverlapAux

def walkOverlap {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') : ℤ :=
  (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum

/--
@isnad1 id=eq.0h8v.s7.f1f4ec527810 from=translated src=- shape=addc4514 vocab=80d4796b
-/
theorem walkOverlap_eq_sum {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q = (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum :=
  rfl

/--
@isnad1 id=eq.0h6v.s5.a54f2d7a89d5 from=translated src=- shape=48895ad3 vocab=6b7e60ca
-/
@[simp] theorem walkOverlap_nil_left (u : W) {u' v' : W} (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.nil : 𝒯.Walk u u) Q = 0 := by
  simp [walkOverlap]

/--
@isnad1 id=eq.0h6v.s5.1f9c5eb9447e from=translated src=- shape=fdc2cc16 vocab=6b7e60ca
-/
@[simp] theorem walkOverlap_nil_right {u v : W} (P : 𝒯.Walk u v) (u' : W) :
    walkOverlap P (SimpleGraph.Walk.nil : 𝒯.Walk u' u') = 0 := by
  simp [walkOverlap]

/--
@isnad1 id=eq.1h9v.s7.7f0b4f698727 from=translated src=- shape=329c3299 vocab=8b2c1e03
-/
theorem walkOverlap_cons_left {u v w u' v' : W} (h : 𝒯.Adj u v) (P : 𝒯.Walk v w) (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.cons h P) Q =
      (((Q.darts.count ⟨(u, v), h⟩ : ℕ) : ℤ) - ((Q.darts.count (⟨(u, v), h⟩ : 𝒯.Dart).symm : ℕ) : ℤ)) +
        walkOverlap P Q := by
  simp [walkOverlap]

/--
@isnad1 id=eq.0h10v.s6.3038386018f3 from=translated src=- shape=044ab87a vocab=7b35536d
-/
theorem walkOverlap_append_left {u v w u' v' : W} (P₁ : 𝒯.Walk u v) (P₂ : 𝒯.Walk v w) (Q : 𝒯.Walk u' v') :
    walkOverlap (P₁.append P₂) Q = walkOverlap P₁ Q + walkOverlap P₂ Q := by
  simp [walkOverlap, SimpleGraph.Walk.darts_append, List.sum_append]

/--
@isnad1 id=eq.0h10v.s6.5bca5aa06d72 from=translated src=- shape=ee821ac5 vocab=7b35536d
-/
theorem walkOverlap_append_right {u v u' v' w' : W} (P : 𝒯.Walk u v) (Q₁ : 𝒯.Walk u' v') (Q₂ : 𝒯.Walk v' w') :
    walkOverlap P (Q₁.append Q₂) = walkOverlap P Q₁ + walkOverlap P Q₂ := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_append, List.count_append, Nat.cast_add, ← WalkOverlapAux.sum_map_add_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  ring

/--
@isnad1 id=eq.0h8v.s5.f3fbe1475e3f from=translated src=- shape=3f1d6af8 vocab=b4bfce92
-/
theorem walkOverlap_reverse_left {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P.reverse Q = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map,
    ← WalkOverlapAux.sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply, SimpleGraph.Dart.symm_symm]
  ring

/--
@isnad1 id=eq.0h8v.s5.706c6220ee02 from=translated src=- shape=dcc03c73 vocab=b4bfce92
-/
theorem walkOverlap_reverse_right {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q.reverse = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, ← WalkOverlapAux.sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  have h1 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d = Q.darts.count d.symm := by
    rw [List.count_reverse, ← SimpleGraph.Dart.symm_symm d, List.count_map_of_injective _ _
      SimpleGraph.Dart.symm_involutive.injective, SimpleGraph.Dart.symm_symm]
  have h2 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d.symm = Q.darts.count d := by
    rw [List.count_reverse, List.count_map_of_injective _ _ SimpleGraph.Dart.symm_involutive.injective]
  rw [h1, h2]
  ring

/--
@isnad1 id=eq.1h11v.s7.bbd8b83b6a92 from=translated src=- shape=5fe45cf7 vocab=84ade2e3
-/
theorem walkOverlap_map {W' : Type} [DecidableEq W'] {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯')
    (hf : Function.Injective f) {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap (P.map f) (Q.map f) = walkOverlap P Q := by
  have hinj : Function.Injective f.mapDart := WalkOverlapAux.mapDart_injective f hf
  simp only [walkOverlap, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply]
  rw [List.count_map_of_injective _ _ hinj, show (f.mapDart d).symm = f.mapDart d.symm from rfl,
    List.count_map_of_injective _ _ hinj]

end Mumford
end CerednikDrinfeld
