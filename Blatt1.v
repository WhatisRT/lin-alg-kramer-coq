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

  (* Lemma mult_inj :  *)
  Lemma f_bij : bijective eq Logic.eq f.
    Hint Unfold injective surjective.
    split; autounfold with *.
    - Arguments N.mul : simpl nomatch.
      inversion 1.
      rewrite <- N.mul_cancel_l; crush.
    - intros [y [x H]]. exists x. crush.
  Qed.
End Ex1a.

Require Import Numbers.BinNums.
Require Import Arith.PeanoNat.

Section Ex1b.
  Local Notation of_succ_nat := BinPos.Pos.of_succ_nat.
  Local Notation of_nat := BinPos.Pos.of_nat.
  Local Notation div2 := Nat.div2.
  Local Notation even := Nat.even.

  Definition f2 : nat -> Z :=
    (fun n => match n with
           | 0 => Z0
           | S n' => let hn := (of_succ_nat (div2 n')) in
                    match even n' with
                    | true => Zpos hn
                    | false => Zneg hn
                    end
           end
    ).

  Example f2_0 : f2 0 = Z0. crush. Qed.
  Example f2_1 : f2 1 = Zpos (of_nat 1). crush. Qed.
  Example f2_2 : f2 2 = Zneg (of_nat 1). crush. Qed.

  Definition undo_div2 (even : bool) (y : nat) : nat :=
    2 * y + if even then 0 else 1.

  Lemma induction_by_2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
        (Hind : forall n', P n' -> P (S (S n'))) : forall n, P n.
    assert (forall n, P n /\ P (S n)). { induction n as [|n' IHn']; crush. }
    intros n. destruct (H n) as [Hn _]. exact Hn.
  Qed.

  Lemma undo_div2_works : forall n, undo_div2 (even n) (div2 n) = n.
    apply induction_by_2; try reflexivity.
    intros n' IHn'. simpl. unfold undo_div2.
    rewrite <- mult_n_Sm. rewrite (Nat.add_comm _ 2).
    rewrite <- Nat.add_assoc. fold (undo_div2 (even n') (div2 n')).
    crush.
  Qed.

  Lemma div2_even_complete : forall n m,
      even n = even m /\ div2 n = div2 m -> n = m.
    intros n m [Hev Hdiv].
    rewrite <- (undo_div2_works n).
    rewrite <- (undo_div2_works m).
    crush.
  Qed.

  Lemma neqb_neg : forall a b, Bool.eqb a b = false -> negb a = b.
    intros [|] [|]; crush.
  Qed.

  Lemma double_even : forall n, even (2 * n) = true.
    induction n; try reflexivity.
    simpl. rewrite <- plus_n_Sm. apply IHn.
  Qed.

  Lemma pred_commutes : forall n, of_succ_nat (Nat.pred n) = BinPos.Pos.pred (of_succ_nat n).
    induction n; try reflexivity.
    simpl. symmetry. apply BinPos.Pos.pred_succ.
  Qed.

  Lemma PosPredNat : forall p, of_succ_nat (Nat.pred (BinPos.Pos.to_nat p)) = p.
    intros p. rewrite -> pred_commutes.
    exact (Pnat.Pos2SuccNat.pred_id p).
  Qed.

  Lemma f2_bij : bijective eq eq f2.
    split.
    - (* inj *) intros [|x1] [|x2] H; try reflexivity.
      + (* 0, S x2 *) inversion H. destruct (even x2); crush.
      + (* S x1, 0 *) inversion H. destruct (even x1); crush.
      + (* S x1, S x2 *) inversion H.
        destruct (Bool.eqb (even x1) (even x2)) eqn:Heq.
        * apply Bool.eqb_prop in Heq. rewrite <- Heq in H1.
          destruct (even x1) eqn:ev1; inversion H1;
          apply (f_equal BinPos.Pos.to_nat) in H2;
          repeat rewrite -> Pnat.SuccNat2Pos.id_succ in H2;
          inversion H2; apply f_equal; apply div2_even_complete;
          crush.
        * apply neqb_neg in Heq. rewrite <- Heq in H1.
          destruct (even x1); inversion H1.
    - (* surj *) intros [|p|p].
      + (* y = Z0 *) exists 0. reflexivity.
      + (* y = Zpos p *)
        set (n := Nat.pred (BinPos.Pos.to_nat p)).
        exists (1 + 2 * n). simpl.
        replace (n + (n + 0)) with (2 * n) by reflexivity.
        repeat rewrite -> Nat.div2_double.
        rewrite -> double_even. unfold n. apply f_equal.
        apply PosPredNat.
      + (* y = Zneg *)
        set (n := Nat.pred (BinPos.Pos.to_nat p)).
        exists (2 * (1 + n)). simpl. rewrite <- plus_n_Sm.
        replace (n + (n + 0)) with (2 * n) by reflexivity.
        rewrite -> Nat.even_succ. rewrite <- Nat.negb_even.
        rewrite -> double_even. unfold negb. apply f_equal.
        rewrite -> Nat.div2_succ_double. unfold n.
        apply PosPredNat.
  Qed.
