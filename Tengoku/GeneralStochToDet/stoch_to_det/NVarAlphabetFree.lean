import Tengoku.GeneralStochToDet.stoch_to_det.NVarPosteriorCompression

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An alphabet-free coordinate bound for every `n >= 3`

This file combines posterior-replica control, the imported two-variable
compression theorem, finite seed fixing, and hardening.  Its final constant
depends only on `n`.
-/

namespace stoch_to_det

open Finset

namespace FiniteInfo

/-- Entropy is unchanged when two finite observables deterministically decode
each other on the underlying sample space.
@isnad1 id=eq.3h8v.s6.ca865073be93 from=translated src=- shape=c8733424 vocab=39a0a53d
-/
lemma Hvar_eq_of_mutual_recode
    {A F G : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (g : A -> G)
    (enc : F -> G) (dec : G -> F)
    (henc : forall a, enc (f a) = g a)
    (hdec : forall a, dec (g a) = f a) :
    Hvar g m = Hvar f m := by
  have hforward := Hvar_comp_le hm f enc
  have hback := Hvar_comp_le hm g dec
  have hfg : enc ∘ f = g := by funext a; exact henc a
  have hgf : dec ∘ g = f := by funext a; exact hdec a
  rw [hfg] at hforward
  rw [hgf] at hback
  exact le_antisymm hforward hback

/--
@isnad1 id=eq.3h10v.s6.cc306c6a3355 from=translated src=- shape=8e65e782 vocab=778365dd
-/
lemma condH_eq_of_mutual_recode_left
    {A F G K : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype G] [DecidableEq G] [Fintype K] [DecidableEq K]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (g : A -> G)
    (h : A -> K) (enc : F -> G) (dec : G -> F)
    (henc : forall a, enc (f a) = g a)
    (hdec : forall a, dec (g a) = f a) :
    condH g h m = condH f h m := by
  let encPair : F × K -> G × K := fun z => (enc z.1, z.2)
  let decPair : G × K -> F × K := fun z => (dec z.1, z.2)
  have hpair := Hvar_eq_of_mutual_recode hm
    (fun a => (f a, h a)) (fun a => (g a, h a)) encPair decPair
    (fun a => Prod.ext (henc a) rfl) (fun a => Prod.ext (hdec a) rfl)
  unfold condH
  rw [hpair]

/--
@isnad1 id=eq.3h10v.s6.c352ed76f1d1 from=translated src=- shape=69d99a5c vocab=778365dd
-/
lemma condH_eq_of_mutual_recode_condition
    {A F K L : Type*} [Fintype A] [Fintype F] [DecidableEq F]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    {m : A -> Real} (hm : IsPMF m) (f : A -> F) (h : A -> K)
    (k : A -> L) (enc : K -> L) (dec : L -> K)
    (henc : forall a, enc (h a) = k a)
    (hdec : forall a, dec (k a) = h a) :
    condH f k m = condH f h m := by
  let encPair : F × K -> F × L := fun z => (z.1, enc z.2)
  let decPair : F × L -> F × K := fun z => (z.1, dec z.2)
  have hpair := Hvar_eq_of_mutual_recode hm
    (fun a => (f a, h a)) (fun a => (f a, k a)) encPair decPair
    (fun a => Prod.ext rfl (henc a)) (fun a => Prod.ext rfl (hdec a))
  have hcond := Hvar_eq_of_mutual_recode hm h k enc dec henc hdec
  unfold condH
  rw [hpair, hcond]

end FiniteInfo

section Recode

variable {Omega delta : Type} [Fintype Omega] [DecidableEq Omega]
  [Nonempty Omega] [Fintype delta] [DecidableEq delta]

/-- Assign to every realized code value a canonical representative source
point, then label that point in `Fin |Omega|`.-/
private noncomputable def finiteCodeEncoder (code : Omega -> delta) :
    delta -> Fin (Fintype.card Omega) := fun d =>
  if h : exists x, code x = d then
    Fintype.equivFin Omega (Classical.choose h)
  else Fintype.equivFin Omega (Classical.choice inferInstance)

private noncomputable def finiteCodeDecoder (code : Omega -> delta) :
    Fin (Fintype.card Omega) -> delta := fun j =>
  code ((Fintype.equivFin Omega).symm j)

private noncomputable def finiteCodeRecode (code : Omega -> delta) :
    Omega -> Fin (Fintype.card Omega) :=
  finiteCodeEncoder code ∘ code

variable {n : Nat} {kappa gamma : Fin n -> Type}
  [forall i, Fintype (kappa i)] [forall i, DecidableEq (kappa i)]
  [forall i, Fintype (gamma i)] [forall i, DecidableEq (gamma i)]
  {p : Omega -> Real}

end Recode

namespace NVarAlphabetFree

variable {n : Nat} {alpha : Type} [Fintype alpha] [DecidableEq alpha]
  [Inhabited alpha]
variable {p : (Fin n -> alpha) -> Real}

end NVarAlphabetFree

end stoch_to_det
