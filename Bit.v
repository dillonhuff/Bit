Require Import Bool List ZArith Arith.
Require Import CpdtTactics.

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

Fixpoint numZeros (f : bitField) : nat :=
  match f with
    | nil => 0
    | t :: rest =>
      match t with
        | Zero => 1 + (numZeros rest)
        | One => numZeros rest
      end
  end.

Theorem all_ones_or_zeros :
  forall f : bitField, numOnes f + numZeros f = length f.
Proof.
  intros; induction f.
  simpl. reflexivity.

  destruct a. simpl. rewrite plus_comm. rewrite -> plus_Sn_m.
  rewrite plus_comm. apply eq_S. apply IHf.

  simpl. rewrite -> IHf. reflexivity.
Qed.  

(*eq_S: forall x y : nat, x = y -> S x = S y*)
(*: forall n m : nat, S n + m = S (n + m)*)
  SearchAbout (S _ = S _).

(*crush.
  simpl. crush.
Qed.*)

Theorem num_ones_lte_bitField_length :
  forall b : bitField, numOnes b <= (length b).
Proof.
  intros b. induction b as [| b'].

  simpl. reflexivity.

  destruct b'.
  simpl. rewrite IHb. apply le_n_Sn.

  simpl. apply le_n_S. apply IHb.
Qed.

Fixpoint isZero (f : bitField) : bool :=
  match f with
    | nil => true
    | Zero :: nil => true
    | b :: f' =>
      match b with
        | Zero => isZero f'
        | One => false
      end
  end.

(*Lemma isZero_implies_all_zero :
  forall f : bitField, isZero (Zero :: f) = true -> isZero f = true.
Proof.
  intros. simpl isZero in H.
  apply H.
Qed.*)

Lemma append_zero_gives_zero :
  forall f : bitField, isZero (Zero :: f) = isZero f.
Proof.
  intros.
  simpl. destruct f; simpl; reflexivity.
Qed.

Lemma append_one_gives_non_zero : 
  forall f : bitField, isZero (One :: f) = false.
Proof.
  intros. simpl; reflexivity.
Qed.

Theorem isZero_correct :
  forall f : bitField, (isZero f) = true -> numZeros f = length f.
Proof.
  intros.
  induction f. simpl. reflexivity.

  destruct a.
  simpl. rewrite append_zero_gives_zero in H.
  apply eq_S. apply IHf in H. apply H.
  discriminate.
Qed.

(*  rewrite append_one_gives_non_zero in H.*)

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

Fixpoint addUnsignedRec (carry : bit) (l r : bitField) : bitField :=
  match l with
    | nil =>
      match r with
        | nil => carry :: nil
        | other => nil
      end
    | b1 :: l' =>
      match r with
        | nil => nil
        | b2 :: r' =>
          let hadd := halfAdd carry b1 b2 in
          match hadd with
            | result :: newCarry :: nil => result :: (addUnsignedRec newCarry l' r')
            | other => nil
          end
      end
  end.

Definition addUnsigned (l r : bitField) : bitField :=
  addUnsignedRec Zero l r.

Theorem add_unsigned_correct :
  forall l r : bitField,
    (Zlength l) = (Zlength r) -> (Zlength r > 0) ->
    unsignedBitFieldToZ (addUnsigned l r) =
    (unsignedBitFieldToZ l) + (unsignedBitFieldToZ r).
Proof.
  intros.
  induction l.
  simpl. rewrite Zlength_nil in H.
  rewrite <- H in H0. crush.

  destruct a.
  
(*rewrite Zlength_nil.*)

SearchAbout (Zlength _).
(*
SearchAbout ((S _) <= (S _)).
SearchRewrite (_ <= (S _)).
*)
