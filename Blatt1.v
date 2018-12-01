Require Import CpdtTactics.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.

Set Implicit Arguments.

Section FunctionDefinitions.
  Variable A B : Type.
  Variable eq_A : A -> A -> Prop.
  Variable eq_B : B -> B -> Prop.

  Variable eqiv_A : Equivalence eq_A.
  Variable eqiv_B : Equivalence eq_B.

  Variable f : A -> B.

  Variable f_comp : Proper (eq_A==>eq_B) f.

  Notation "x ==_A y" := (eq_A x y)(at level 70, no associativity).
  Notation "x ==_B y" := (eq_B x y)(at level 70, no associativity).
  
  Definition injective := forall x1 x2 : A, f x1 ==_B f x2 -> x1 ==_A x2.
  Definition surjective := forall y : B, exists x, f x ==_B y.
  Definition bijective := injective /\ surjective.
End FunctionDefinitions.

Require NArithRing.

Require Import BinNat.
Require Import NArith.BinNatDef.

Section Ex1a.
  Definition twoN := { x : N | N.Even x }.
  Search (N -> N -> N).
  Program Definition f : N -> twoN :=
    fun x => N.mul 2 x.
  Next Obligation.
    match goal with
    | [ H: N |- _ ] => exists H; crush
    end.
  Defined.

  Check Logic.eq.
  Search (forall A, A -> A -> Prop).

  (* Lemma mult_inj :  *)

  Lemma f_bij : bijective eq Logic.eq f.
    Hint Unfold injective surjective.
    split; autounfold with *.
    - Arguments N.mul : simpl nomatch.
      inversion 1.
      rewrite <- N.mul_cancel_l; crush.
    - intros [y [x H]]. exists x. crush.
  Qed.
