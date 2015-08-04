(* software foundation *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.


Eval compute in (next_weekday friday).
Eval compute in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. 
simpl. 
reflexivity. 
Qed.

Inductive bool : Type :=
  |true : bool
  |false : bool.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof. reflexivity. Qed.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => 
    match b2 with
    | false => true
    | true => false
    end
  end.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => 
      match b2 with
        |false => false
        |true => match b3 with
          |false => false
          |true => true
          end
        end
  end.
  


Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.



Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => 0
  | S (S n') => n'
  end.

Check S (S (S (S 0))).

Eval compute in (minustwo 4).

Check S.
Check Playground1.nat.
Check minustwo.

Fixpoint evenb ( n : nat) : bool :=
  match n with
  | 0 => true
  | S 0 => false
  | S (S n') =>  evenb (n')
  end.

Eval compute in evenb (14).

Definition oddb (n : nat) : bool :=
  negb (evenb n).
Eval compute in oddb (13).


Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

(* excer *)



(* Module Playground2.*)

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

(* End Playground2. *)



Fixpoint mult (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => plus m (mult n' m)
  end.


Eval compute in (mult 3 4).

Example testMult1 : (mult 5 6) = 30.
Proof. reflexivity. Qed.




Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | 0, _ => 0
  | S _, 0 => n
  | S n', S m' => minus n' m'
  end.

Eval compute in (minus 3 2).



Fixpoint exp (n m : nat) : nat :=
  match n, m with
  | _, 0 => 1
  | 0, _ => 0
  | (S n'), (S m') => (mult n (exp n m'))
  end.


Eval compute in (exp 3 4).

Fixpoint fac (n:nat) : nat :=
  match n with
  | 0 => 0
  | S 0 => 1
  | S n' => (mult n (fac n'))
  end.

Example testfac : (fac 3) = 6.
Proof. reflexivity. Qed.

Example testfac2 : (fac 4) = (mult 12 2).
Proof. reflexivity. Qed.


Notation "x +* y" := (exp x y)
(at level 50, left associativity) : nat_scope.

Check ((0+1) + 1).

Eval compute in ((2+*2) +* 2).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', 0 => false
  | 0, S m' => true
  | S n', S m' => (ble_nat n' m')
  end.

Eval compute in (ble_nat 3 3).

Fixpoint blt_nat1 (n m : nat) : bool :=
  match n, m with
  | 0, 0 => false
  | S n', 0 => false
  | 0, S m' => true
  | S n', S m' => (blt_nat1 n' m')
  end.

Example tblt_nat1: (blt_nat1 2 2) = false.
Proof. reflexivity. Qed.
Example tblt_nat2: (blt_nat1 2 4) = true.
Proof. reflexivity. Qed.
Example tblt_nat3: (blt_nat1 4 2) = false.
Proof. reflexivity. Qed.



Theorem plus_id_1 : forall n m : nat,
  n = m ->
  n + m = m + n.

Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o.
  intros H.
  intros H1.
  rewrite <- H.
  rewrite <- H1.
  rewrite <- H.
  reflexivity.
Qed.



Theorem plus_0_n : forall n:nat,
  0 + n = n.

Proof.
  intros n.
  simpl.
  reflexivity.
Qed.



Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.

Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
Qed.



(* comment start 2 *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  intros n m.
  simpl.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.


Fixpoint beq_nat1 (n m :nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', 0 => false
  | 0, S m' => false
  | S n', S m' => (beq_nat1 n' m')
  end.

Eval compute in (beq_nat1 2 1).


Notation "x + y" := (plus x y)
(at level 50, left associativity) : nat_scope.






Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat1 (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n']. (* vars sep by | *)
  reflexivity.
  reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.


Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
  reflexivity.
  reflexivity.
Qed.

(* comment start 2 *)
Theorem identity_fn_applied_twice : 
  forall(f : bool -> bool), 
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.


Example or_true_c :
  forall (c:bool),
  (orb true c) = true.

Proof.
  reflexivity.
Qed.

Lemma and_false_c :
  forall (c:bool),
  andb false c = false.

Proof.
  reflexivity.
Qed.


(* comment start 2 *)
Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  destruct b.
  intros c.
  Focus 1.
  simpl.
  intros.
  rewrite <- H.
  reflexivity.
  intros c.
  rewrite -> and_false_c with c.
  simpl.
  intros h2.
  rewrite -> h2.
  reflexivity.
Qed.
  


Inductive bnat : Type :=
  | O : bnat (* 0 *)
  | T : bnat->bnat (* xxx0 *)
  | TI : bnat->bnat (* xxxx1 *).


Fixpoint incr (n:bnat) : bnat :=
  match n with
  | O => TI O
  | T n' => TI n'
  | TI n' => T (incr n')
  end.


Example test_bin_incr1:
  (incr O) = (TI O).

Proof. simpl. reflexivity. Qed.

Example test_bin_incr2:
  (incr (TI (TI O)))=(T (T (TI O))).
Proof. reflexivity. Qed.

Example test_bin_incr3:
  (incr (T (TI O)))=(TI (TI O)).
Proof. reflexivity. Qed.

Example test_bin_incr4:
  (incr (TI (T (TI O))))=(T (TI (TI O))).
Proof. reflexivity. Qed.

Example test_bin_incr5:
  (incr (TI (T (TI O))))=(T (TI (TI O))).
Proof. reflexivity. Qed.


Fixpoint lt (n m:nat) : bool :=
  match n, m with
  | 0, S m' => true
  | 0, 0 => false
  | S n', 0 => false
  | S n', S m' => lt n' m'
  end.

Fixpoint decrto1(n:nat) : nat :=
  match n with
  | 3 => 1
  | S n' =>(decrto1 n')
  | _ => 1
  end.

Eval compute in (decrto1 10).
Eval compute in (eq 10 10).

Fixpoint eq1 (n m:nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', S m' => eq1 n' m'
  | _, _ => false
  end.

(* ill form 
Fixpoint incrto(n:nat) : nat :=
  match n with
  | 10 => 11
  | 0 => 1
  | m' =>(incrto (S m'))
  end.
*)




(*
http://www.cis.upenn.edu/~bcpierce/sf/current/Induction.html#lab38
*)

Require String. Open Scope string_scope.
Ltac move_to_top x :=
  match reverse goal with
  | H : _ |-  _ => try move x after H
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

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.





