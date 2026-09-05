Inductive asdfgh : Type :=
| asd : asdfgh
| fgh : asdfgh
| qwe
| zxc.

Definition something1 : asdfgh := asd.
Definition something2 : asdfgh := fgh.
Definition something3 : asdfgh := zxc.

Inductive bool : Type :=
| T
| F.

Definition is_qwe (x : asdfgh) : bool :=
    match x with
    | qwe => T
    | _ => F
    end.


Inductive nat : Type :=
| zero
| succ (n : nat).

Check nat_ind. 

Definition seven : nat := succ (succ (succ (succ (succ (succ (succ zero)))))).
Definition one : nat := succ zero.
Definition zero' : nat := zero.

Definition is_nonzero (x : nat) : bool :=
    match x with
    | succ _ => T
    | _ => F 
    end.
    
Compute is_nonzero seven.

Fixpoint add (x y : nat) : nat :=
match y with
| zero => x
| succ y' => succ (add x y') end.

Compute add (add seven one) zero.

Inductive R : nat -> asdfgh -> nat -> Prop :=
| base_case_12308957 : forall (n : nat) (x : asdfgh) (m : nat), R n x m
| some_other_case''' : forall (n m k : nat) (x y z: asdfgh),
                       R n x m -> R m y k -> R k z n.