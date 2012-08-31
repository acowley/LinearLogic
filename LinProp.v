(** Define the linear logic connectives. This module is parameterized
   over a term type that may be embedded in linear logic propositions. *)
Require Import Sig.
Module LinProp(Term:Sig).
Import Term.
Inductive LinProp : Type :=
| Implies     : LinProp -> LinProp -> LinProp
| One         : LinProp
| Plus        : LinProp -> LinProp -> LinProp
| Times       : LinProp -> LinProp -> LinProp
| Top         : LinProp
| With        : LinProp -> LinProp -> LinProp
| Zero        : LinProp
| Term        : A -> LinProp.

Infix "⊗"    := Times (at level 41, right associativity). (* \otimes *)
Infix "&"   := With (at level 74, right associativity).
Infix "⊕"    := Plus (at level 51, right associativity). (* \oplus *)
Notation "⊤" := Top. (* \top *)
Notation "⊥" := Zero. (* \bot *)
Infix "⊸"    := Implies (at level 73, right associativity). (* \multimap *)
End LinProp.
