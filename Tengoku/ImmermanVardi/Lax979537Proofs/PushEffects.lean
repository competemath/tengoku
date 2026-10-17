import Tengoku.ImmermanVardi.Lax979537Proofs.NodeMachine

namespace Lax979537Proofs.PushEffects

open Turing

structure Effect (tm : FinTM2) where
  key : tm.K
  symbol : tm.Γ key
  next : TM2Micro.Cursor tm.Γ tm.Λ tm.σ

def target (tm : FinTM2) (c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ) (v : tm.σ) : Option (Effect tm) :=
  match c with
  | .instruction (.push k f q) => some ⟨k, f v, .instruction q⟩
  | _ => none

/--
@isnad1 id=step.1h8v.s7.bfcba981bdbf from=translated src=- shape=cf85ccb0 vocab=7ba71330
-/
theorem target_step (tm : FinTM2) {Node : Type} (fresh : Node)
    (H : NodeMachine.Records Node tm.Γ) (heads : tm.K → Option Node)
    {c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ} {v : tm.σ} {e : Effect tm}
    (ht : target tm c v = some e) :
    NodeMachine.Step tm.m fresh H ⟨c, v, heads⟩
      (insert (fresh, Sigma.mk e.key e.symbol, heads e.key) H)
      ⟨e.next, v, Function.update heads e.key (some fresh)⟩ := by
  cases c with
  | boundary l => cases ht
  | instruction q =>
      cases q with
      | push k f q => cases ht; exact .push H k f q v heads
      | pop | peek | load | branch | goto | halt => cases ht

/--
@isnad1 id=eq.1h7v.s6.89a8bfabb6d3 from=translated src=- shape=5bfec17e vocab=6d008a5f
-/
theorem target_added (tm : FinTM2) {Node : Type} (fresh : Node)
    (heads : tm.K → Option Node)
    {c : TM2Micro.Cursor tm.Γ tm.Λ tm.σ} {v : tm.σ} {e : Effect tm}
    (ht : target tm c v = some e) :
    NodeMachine.added fresh ⟨c, v, heads⟩ = some (fresh, Sigma.mk e.key e.symbol, heads e.key) := by
  cases c with
  | boundary l => cases ht
  | instruction q =>
      cases q with
      | push k f q => cases ht; rfl
      | pop | peek | load | branch | goto | halt => cases ht

end Lax979537Proofs.PushEffects
