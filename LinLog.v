Require Import Sig.
Require Export List.
Require Export Permutation.
Require Import Setoid.

Require LinProp.
Module LinLog(Term:Sig).
Module LinPropTerm := LinProp.LinProp Term.
Import Term.
Export LinPropTerm.

Notation "[]" := nil.
Notation "[ x , .. , y ]" := (x :: .. (y :: nil) ..) : list_scope.

(** The linear consequence operator is defined inductively between any
   list of linear propositions (the hypotheses) and some other
   proposition (the conclusion). *)

Reserved Notation "A ⊢ B" (at level 74, right associativity).
Reserved Notation "A ⊢ι B" (at level 74, right associativity).
Reserved Notation "A ⊢ε B" (at level 74, right associativity).

(** Define the linear logic consequence relation by partitioning it
   into introduction and elimination forms. *)
Inductive LinCons : list LinProp -> LinProp -> Prop :=
| Intro : forall Γ C, Γ ⊢ι C -> Γ ⊢ C
| Elim  : forall Γ C, Γ ⊢ε C -> Γ ⊢ C
| PermContext : forall Γ Δ C, Permutation Γ Δ -> Γ ⊢ C -> Δ ⊢ C
| Cut   : forall Γ Δ A B, Γ ⊢ B -> Δ ++ [B] ⊢ A -> Γ ++ Δ ⊢ A
where "Γ ⊢ C" := (LinCons Γ C)
with
LinIntro : list LinProp -> LinProp -> Prop :=
| PermContextι : forall Γ Δ C, Permutation Γ Δ -> Γ ⊢ι C -> Δ ⊢ι C
| Refl         : forall t, [t] ⊢ι t
| OneIntro     : [] ⊢ι One
| TopIntro     : forall Γ, Γ ⊢ι ⊤
| TimesIntro   : forall Δ Θ A B, Δ ⊢ A -> Θ ⊢ B -> Δ ++ Θ ⊢ι A ⊗ B
| ImpliesIntro : forall Γ A B, Γ ++ [A] ⊢ B -> Γ ⊢ι A ⊸ B
| WithIntro    : forall Γ A B, Γ ⊢ A -> Γ ⊢ B -> Γ ⊢ι A & B
| PlusIntroL   : forall Γ A B, Γ ⊢ A -> Γ ⊢ι A ⊕ B
| PlusIntroR   : forall Γ A B, Γ ⊢ B -> Γ ⊢ι A ⊕ B
where "Γ ⊢ι C" := (LinIntro Γ C)
with
LinElim : list LinProp -> LinProp -> Prop :=
| PermContextε : forall Γ Δ C, Permutation Γ Δ -> Γ ⊢ε C -> Δ ⊢ε C
| OneElim     : forall Δ Θ A, Δ ⊢ One -> Θ ⊢ A -> Δ ++ Θ ⊢ε A
| TimesElim   : forall Γ Δ A B C, Δ ⊢ A ⊗ B -> Γ ++ [A,B] ⊢ C -> Γ ++ Δ ⊢ε C
| ImpliesElim : forall Γ Δ A B, Γ ⊢ A ⊸ B -> Δ ⊢ A -> Γ ++ Δ ⊢ε B
| WithElimL   : forall Γ A B, Γ ⊢ A & B -> Γ ⊢ε A
| WithElimR   : forall Γ A B, Γ ⊢ A & B -> Γ ⊢ε B
| PlusElim    : forall Θ Δ A B C, 
                Θ ⊢ A ⊕ B -> Δ ++ [A] ⊢ C -> Δ ++ [B] ⊢ C -> Θ ++ Δ ⊢ε C
| ZeroElim    : forall Γ A, Γ ++ [⊥] ⊢ε A
where "Γ ⊢ε C" := (LinElim Γ C).

Arguments PermContext [Γ Δ C].
Arguments Cut [Γ Δ A B].

Create HintDb linlog.
#[local] Hint Constructors LinIntro LinElim : linlog.

Add Parametric Morphism : LinIntro with
signature (@Permutation LinProp) ==> Logic.eq ==> iff as LinIntro_morph.
intros X Y HPerm C. split; intros H. inversion H; subst; try (eauto with linlog).
symmetry in HPerm. apply PermContextι with (Δ:=X) in H; assumption.
Qed.

Add Parametric Morphism : LinElim with
signature (@Permutation LinProp) ==> Logic.eq ==> iff as LinElim_morph.
intros X Y HPerm C. split; intros H. inversion H; subst; try (eauto with linlog).
symmetry in HPerm. apply PermContextε with (Δ:=X) in H; assumption.
Qed.

Add Parametric Morphism : LinCons with
signature (@Permutation LinProp) ==> Logic.eq ==> iff as LinCons_morph.
intros X Y HPerm C. split; intros H; inversion H.
rewrite HPerm in H0. apply Intro. assumption.
rewrite HPerm in H0. apply Elim. assumption.
apply (PermContext HPerm). assumption.
apply (Cut H0) in H1. rewrite <- H2 in HPerm. 
  apply (PermContext HPerm). assumption.

symmetry in HPerm. rewrite HPerm in H0. apply Intro. assumption.
symmetry in HPerm. rewrite HPerm in H0. apply Elim. assumption.
symmetry in HPerm. apply (PermContext HPerm). assumption.
symmetry in HPerm. apply (Cut H0) in H1. rewrite <- H2 in HPerm.
  apply (PermContext HPerm). assumption.
Qed.

(** * Tactics that de-clutter constructor application. *)

Ltac refl := apply Intro; apply Refl.
Ltac topIntro := apply Intro; apply TopIntro.
Ltac withElimL := apply Elim; eapply WithElimL.
Ltac withElimR := apply Elim; eapply WithElimR.
Ltac withIntro := apply Intro; apply WithIntro.
Ltac impliesElim := apply Elim; eapply ImpliesElim.
Ltac timesIntro := apply Intro; apply TimesIntro.

End LinLog.