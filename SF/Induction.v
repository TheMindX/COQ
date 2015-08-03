Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

(* 2start *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  simpl.
  intros h.
  rewrite -> h.
  reflexivity.
  simpl.
  intros h1.
  destruct c.
  reflexivity.
  rewrite <- h1.
  reflexivity.
Qed.


Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

Proof.
  intros n.
  induction  n as [|n'].
  Case "n = 0". reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.




Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.



(* Exercise: 2 stars (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n as [|n].
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.




Lemma p1 : forall n m : nat,
  S (n + m) = S n + m.
Proof.
  intros n.
  induction n as [|n'].
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.


Lemma p1_1 : forall n : nat,
    n + 1 = S n.
Proof.
  intros.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Lemma p2 : forall n m : nat,
  S n + m = n + S m.
  induction n, m.  
  reflexivity.
  reflexivity.
  simpl.
  rewrite -> plus_0_r_firsttry.
  rewrite -> p1_1.
  reflexivity.

  

Admitted.



Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [|n']. 
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.
  





