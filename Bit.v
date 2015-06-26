Require Import Bool List ZArith Arith.

Inductive bit : Set :=
| Zero
| One.

Definition bitField := list bit.

Fixpoint numOnes (b : bitField) : nat :=
  match b with
    | nil => 0
    | t :: rest =>
      match t with
        | Zero => numOnes rest
        | One => 1 + (numOnes rest)
      end
  end.


Theorem num_ones_lte_bitField_length :
  forall b : bitField, numOnes b <= (length b).
Proof.
  intros b. induction b as [| b'].

  simpl. reflexivity.

  destruct b'.
  simpl. rewrite IHb. apply le_n_Sn.

  simpl. apply le_n_S. apply IHb.
Qed.

Fixpoint halfAdd (carry left right : bit) : bitField :=
  match numOnes (carry :: left :: right :: nil) with
    | 0 => (Zero :: Zero :: nil)
    | 1 => (One :: Zero :: nil)
    | 2 => (Zero :: One :: nil)
    | other => (One :: One :: nil)
  end.

Theorem halfAdd_possible_results :
  forall c l r : bit, (halfAdd c l r) = (Zero :: Zero :: nil) \/
                      (halfAdd c l r) = (Zero :: One :: nil) \/
                      (halfAdd c l r) = (One :: Zero :: nil) \/
                      (halfAdd c l r) = (One :: One :: nil).
Proof.
  intros c l r.
  destruct c. destruct l. destruct r. simpl.
  tauto. tauto.
  destruct r. tauto. tauto.
  destruct l. destruct r. tauto. tauto.
  destruct r. tauto. tauto.
Qed.


Theorem halfAdd_result_is_length_2 :
  forall c l r : bit, length (halfAdd c l r) = 2.
Proof.
  intros c l r.
  pose proof halfAdd_possible_results as H.
  specialize (H c l r).

  inversion H.
  rewrite H0.
  simpl. reflexivity.

  inversion H0.
  rewrite H1. simpl. reflexivity.

  inversion H1.
  rewrite H2. simpl. reflexivity.

  inversion H2.
  rewrite H2. simpl. reflexivity.
Qed.


Open Scope Z_scope.

Fixpoint unsignedBitFieldToZRec (pow : Z) (f : bitField) : Z :=
  match f with
    | nil => 0
    | b :: f' =>
      match b with
        | Zero => unsignedBitFieldToZRec (pow + 1) f'
        | One => (2 ^ pow) + unsignedBitFieldToZRec (pow + 1) f'
      end
  end.

Definition unsignedBitFieldToZ (f : bitField) : Z :=
  match f with
    | nil => 0
    | other => unsignedBitFieldToZRec 0 other
  end.

Eval compute in unsignedBitFieldToZ nil.
Eval compute in unsignedBitFieldToZ (One :: nil).
Eval compute in unsignedBitFieldToZ (Zero :: One :: nil).
Eval compute in unsignedBitFieldToZ (Zero :: One :: One :: Zero :: nil).


(*
SearchAbout ((S _) <= (S _)).
SearchRewrite (_ <= (S _)).
*)
