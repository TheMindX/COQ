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

Proof. simpl. reflexivity. Qed.

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



Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

End Playground2.



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

Fixpoint ble_nat1 (n m : nat) : bool :=
  match n, m with
  | 0, 0 => true
  | S n', 0 => false
  | 0, S m' => true
  | S n', S m' => (ble_nat1 n' m')
  end.

Eval compute in (ble_nat1 3 4).

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







