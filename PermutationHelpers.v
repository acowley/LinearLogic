(** From the Coq manual, updated to work with the current (8.4)
   standard library *)
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
Ltac permutAux n :=
match goal with
| |- (Permutation ?l ?l) => reflexivity
| |- (Permutation (?a :: ?l1) (?a :: ?l2)) =>
    let newn := eval compute in (length l1) in
    (apply perm_skip; permutAux newn)
| |- (Permutation (?a :: ?l1) ?l2) =>
    match eval compute in n with
    | 1 => fail
    | _ =>
        let l1' := constr:(l1 ++ a :: nil) in
        (apply (@perm_trans _ (a :: l1) l1' l2);
          [ apply Permutation_cons_append | compute; permutAux (pred n) ])
    end
end.

(** Permutation solver *)
Ltac permut :=
  match goal with
  | |- (Permutation ?l1 ?l2) =>
      match eval compute in (length l1 = length l2) with
      | (?n = ?n) => permutAux n
      end
  end.

(*
Notation "[ x , .. , y ]" := (x :: .. (y :: nil) ..) : list_scope.
Lemma fu : Permutation [1,2,3] [3,1,2].
Proof. permut. Qed.
*)