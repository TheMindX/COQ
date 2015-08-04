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

Lemma p0 : forall n : nat,
  S n = 1 + n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma p0_1 : forall n : nat,
  S n = n + 1.
Proof.
  intros.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.


Lemma p0_2 : forall n : nat,
  n + 1 = 1 + n.
Proof.
  simpl.
  intros.
  rewrite <- p0_1.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m:nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [|n'].
  simpl.
  reflexivity.
  simpl.
  intros m.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n as [|n'].
  rewrite -> plus_0_r_firsttry.
  reflexivity.
  rewrite <- plus_n_Sm with m n'.
  simpl.
  rewrite <- IHn'.
  reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction m.
  rewrite -> plus_0_r_firsttry.
  reflexivity.
  rewrite -> plus_comm with (S m) p.
  rewrite <- plus_n_Sm with p m.
  rewrite <- plus_n_Sm with n (p + m).
  rewrite -> plus_comm with p m.
  rewrite -> IHm.
  rewrite <- plus_n_Sm with n m.
  rewrite -> plus_comm with (S (n + m)) p.
  rewrite <- plus_n_Sm with p (n + m).
  rewrite -> plus_comm with p (n + m).
  reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite <- plus_n_Sm with n' n'.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> plus_assoc with n m p.
  rewrite -> plus_comm with m (n + p).
  rewrite -> plus_comm with (n + m) p.
  rewrite -> plus_comm with n p.
  rewrite -> plus_assoc with p n m.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros.

  assert(h1: forall x:nat, 0 * x = 0).
  intros.
  reflexivity.

  assert(h2: forall x:nat, x * 0 = 0).
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite -> IHx.
  reflexivity.
  induction m.
  rewrite h1.
  rewrite h2.
  reflexivity.
  
  assert(h3: forall m n:nat, S m * n = m * n + n).
  intros x y.
  simpl.
  rewrite -> plus_comm.
  reflexivity.
  
  assert(h4: forall m n:nat, m * S n = m * n + m).
  intros x y.
  induction x.
  rewrite -> h1.
  rewrite -> h1.
  reflexivity.
  simpl.
  rewrite IHx.
  rewrite -> plus_assoc.

  assert(h5: forall a b:nat, S (a + b) = (a + S b)).
  Focus 1.
  induction b.
  rewrite -> plus_comm with a 1.
  simpl.
  rewrite -> plus_0_r_firsttry.
  reflexivity.
  induction a.
  simpl.
  reflexivity.
  assert(h4: forall z:nat, S z = 1 + z).
  reflexivity.
  rewrite -> h4.
  rewrite -> h4 with a.
  rewrite -> h4 with b.
  rewrite -> h4 with (1 + b).
  rewrite -> plus_assoc.
  rewrite -> plus_comm with 1 (1 + a).
  rewrite -> plus_assoc with (1 + a) 1 (1+b).
  reflexivity.
  rewrite -> h5 with (y + x * y) x.
  reflexivity.

  rewrite -> h3.
  rewrite -> h4.
  rewrite IHm.
  reflexivity.
Qed.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') =>  evenb n'
  end.


Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).

Proof.
  intros.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
  assert(h1: forall x:nat, evenb (S (S x)) = evenb x).
  reflexivity.
  rewrite -> h1.
  rewrite -> IHn. 
  assert(h2: forall x:bool, negb (negb x) = x).
  destruct x.
  reflexivity.
  reflexivity.
  rewrite h2 with (evenb (S n)).
  reflexivity.
Qed.





