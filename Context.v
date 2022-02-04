(** This module layers context handling facilities on top of the core
   linear logic module, [LinLog]. The most commonly useful definitions
   in this module are the tactics [product_to_context],
   [break_context_at], and [permute_context]. *)
Require Import Sig.
Require LinLog.
Require Export PermutationHelpers.
Module Context(Term:Sig).
Module LinLogTerm := LinLog.LinLog Term.
Export LinLogTerm.
Import List Permutation.
Import ListNotations.

Definition Context := list LinProp.

(** Convert a product into a list. *)
Fixpoint product_to_context (P:LinProp) : Context :=
  match P with
  | x ⊗ y => x :: product_to_context y
  | x => [x]
  end.

(** If we take ⊤ as a right-identity on products, we can convert a
   list of propositions into a single product. *)
Fixpoint context_to_product (C:Context) : LinProp :=
  match C with
  | [] => ⊤
  | [x] => x
  | h::t => h ⊗ context_to_product t
  end.

Lemma context_to_product_left_inverse : 
  forall P, context_to_product (product_to_context P) = P.
Proof. induction P; auto. simpl. rewrite IHP2.
  destruct P2; auto.
Qed.

(** A product consisting of the two elements of a context is just as
   good as the context represented as a list. *)
Lemma product_as_context : forall A B C, [A,B] ⊢ C -> [A ⊗ B] ⊢ C.
Proof. intros. apply Elim. replace [A⊗B] with ([] ++ [A⊗B]) by auto.
  apply TimesElim with (A:=A) (B:=B). refl. assumption.
Qed.

Lemma product_app_as_context : forall A B C D, 
  A++[B,C] ⊢ D -> A ++ [B⊗C] ⊢ D.
Proof. 
  intros. apply Elim. apply TimesElim with (A:=B) (B:=C). refl. assumption.
Qed.

(** Rewrite a list append expression to pop the had of the right
   operand onto the tail of the left operand. *)
Lemma app_pop_cons : forall {A} P (X:A) T, P++(X::T) = (P++[X])++T.
Proof. intros. replace (X::T) with ([X]++T) by auto. apply app_assoc. Qed.

Ltac simplify_all_apps :=
  match goal with
  | |- context f [(?P ++ ?X::?Y)++?Z] =>
    let tmp := fresh in
    assert ((P++X::Y)++Z = P++(X::Y++Z)) as tmp by
      (rewrite <- app_assoc; simpl; reflexivity);
    simpl in tmp; rewrite tmp; clear tmp
  | _ => idtac
  end. 

(** Flatten a product into a [Context]. *)
Ltac product_to_context :=
  match goal with
  | |- [_⊗_] ⊢ _ => apply product_as_context;
                     match goal with
                     | |- ?P::?X ⊢ _ => replace (P::X) with ([P]++X) by auto;
                                        product_to_context
                     end
  | |- ?P++[_⊗_] ⊢ _ => apply product_app_as_context;
                         rewrite app_pop_cons;
                         product_to_context
  | _ => simpl; repeat simplify_all_apps
  end.

(** [break_at n lst] returns a pair whose first component is no more
   than the first [n] elements of [list], and whose second component
   is the remaining elements of [lst]. *)
Definition break_at {A} (n:nat) (L:list A) :=
  let fix go n pre l :=
    match n with
    | 0 => (rev pre, l)
    | S n' => match l with
              | [] => (rev pre, [])
              | h::t => go n' (h::pre) t
              end
    end in
  go n [] L.

(** Tactic for splitting a context into two appended sub-lists. *)
Ltac break_context_at i :=
  match goal with
  |- ?C ⊢ _ => let parts := fresh in
               set (parts:=break_at i C); simpl in parts;
               let pre := fresh in
               set (pre:=fst parts); simpl in pre;
               let pos := fresh in
               set (pos:=snd parts); simpl in pos;
               let hperm := fresh in
               assert (hperm:Permutation C (pre++pos)) by auto;
               rewrite hperm;
               clear parts; subst pre; subst pos; clear hperm
  end.

Lemma context_app_comm : forall A B C, A++B ⊢ C -> B++A ⊢ C.
Proof. intros. 
assert (hperm:Permutation (A++B) (B++A)) by apply Permutation_app_comm.
rewrite <- hperm. assumption.
Qed.

(** Tactic for permuting a context. If the goal is [Context ⊢
   Conclusion], then [permute_context Context'] will attempt to
   replace [Context] with [Context'] in the goal. *)
Ltac permute_context Desired :=
  match goal with
  |- ?C ⊢ _ => let H := fresh in
               assert (H:Permutation C Desired) by permut;
               rewrite H; clear H
  end.

End Context.
