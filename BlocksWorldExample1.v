(** Basic table-top blocks manipulation demonstration. *)
Variable (Block:Type).

(** First define a type to capture the language used to describe the
   world. These are the propositions that apply to our domain. *)
Module BlockProp.
Inductive BlockProp : Type :=
| on    : Block -> Block -> BlockProp
| table : Block -> BlockProp
| clear : Block -> BlockProp
| holds : BlockProp
| empty : BlockProp.
End BlockProp.

Require Import Sig.
Module BlockSig <: Sig.
Definition A := BlockProp.BlockProp.
End BlockSig.

(** Instantiate the linear logic connectives over our langauge. *)
Require Context.
Module BlocksWorld := Context.Context BlockSig.
Import BlocksWorld.

(** Define linear logic propositions for the terms of our language. *)
Definition on X Y : LinProp := Term (BlockProp.on X Y).
Definition table X : LinProp := Term (BlockProp.table X).
Definition clear X : LinProp := Term (BlockProp.clear X).
Definition holds : LinProp := Term BlockProp.holds.
Definition empty : LinProp := Term BlockProp.empty.

(** Define the actions our system is capable of. *)
Axiom newBlock : [empty] ⊢ holds.
Axiom put : forall X Y, [holds] ⊢ empty ⊗ clear X ⊗ (table X & clear Y ⊸ on X Y).
Axiom get : forall X Y, 
  [empty, clear X] ⊢ holds ⊗ (table X ⊸ One & on X Y ⊸ clear Y).

(** An example table-top manipulation task. *)

(** Start with an empty gripper, and block [X] on top of block [Y]. We
    take block [X], put it on the table, then get block [Z] and put it
    on top of block [Y]. *)
Theorem test1 : forall X Y Z, [empty, clear X, on X Y] ⊢ on Z Y ⊗ ⊤.
Proof. intros. 
  break_context_at 2.
  apply Cut with (B:=holds⊗(table X ⊸ One & on X Y ⊸ clear Y)).
  apply get. 
  apply context_app_comm.
  apply Cut with (B:=holds⊗(on X Y ⊸ clear Y)).
  apply product_as_context.
  break_context_at 1.
  timesIntro; [|withElimR]; refl.
  apply product_app_as_context. simpl.
  match goal with 
  |- [?A,?B,?C] ⊢ _ => permute_context [A,C,B]
  end.
  break_context_at 2.
  apply Cut with (B:=clear Y).
  break_context_at 1; apply context_app_comm.
  impliesElim; refl.
  apply Cut with (B:=empty ⊗ clear Z ⊗ (table Z & clear Y ⊸ on Z Y)).
  apply put. product_to_context.
  permute_context ([table Z & clear Y ⊸ on Z Y]++[clear Y, empty, clear Z]).
  apply Cut with (B:=clear Y ⊸ on Z Y).
  withElimR; refl.
  simpl.
  permute_context ([clear Y ⊸ on Z Y, clear Y]++[empty, clear Z]).
  apply Cut with (B:=on Z Y).
  break_context_at 1.
  impliesElim; refl.
  simpl.
  permute_context ([on Z Y] ++ [empty, clear Z]).
  timesIntro. refl. topIntro.
Qed.
