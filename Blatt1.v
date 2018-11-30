Require Import CpdtTactics.
Require Import QArith.Qring.
Require Import QArith.Qfield.
Require Import Lists.List.
Require Import List.
Require Import Fin.
Import ListNotations.

Fixpoint finList (k : nat) : list (Fin.t k) :=
  match k with
  | O => List.nil
  | S m => List.cons Fin.F1 (List.map (fun x => Fin.FS x) (finList m))
  end.

Require Import QArith.QArith_base.

Definition sum x := List.fold_left Qplus x 0.

Definition iN n := inject_Z (Z.of_nat n).

Definition finListNatQ (k : nat) : list Q := List.map (fun k => iN (proj1_sig (to_nat k))) (finList k).

Lemma gauss : forall n, let nQ := iN n in
                   sum (finListNatQ (S n)) == Qdiv (nQ * (nQ + 1)) (iN 2).
Proof.
  Hint Unfold finListNatQ.
  Hint Unfold sum.
  Hint Unfold iN.
  Hint Unfold inject_Z.
  Hint Unfold Z.of_nat.
  (* Hint Unfold Qmult. *)
  (* Hint Unfold Qdiv. *)
  (* Hint Unfold Qinv. *)
  
  induction n; crush.
  assert (finListNatQ (S (S n)) = finListNatQ (S n) ++ [iN (S n)]).
  {
    clear IHn.
    generalize dependent n.
    induction n.
    - crush.
    - admit. 
  }
  rewrite H.
  unfold sum in *.
  rewrite fold_left_app.
  simpl.
  setoid_rewrite IHn.
  setoid_replace (iN (S n)) with (iN n + 1). field_simplify.
  remember (iN n) as k.
  unfold iN. unfold inject_Z, Z.of_nat. field_simplify. setoid_reflexivity.
  1,2:autounfold with *; crush.
  unfold iN.
  rewrite Nat2Z.inj_succ. 
  setoid_replace 1 with (inject_Z 1) by setoid_reflexivity.
  setoid_rewrite <- inject_Z_plus. setoid_reflexivity.
Admitted.