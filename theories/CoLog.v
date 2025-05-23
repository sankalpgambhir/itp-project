Require Import Lia.
Declare ML Module "CoLog:colog.plugin".


Inductive PP3: nat -> nat -> Prop :=
  | P0_ : PP3 0 0
  | P1_ {n m} : PP3 n m -> PP3 (S n) m
  | P2_ {n m} : PP3 n m -> PP3 n (S m).

Inductive QQ2: nat -> Prop :=
  | Q_ {m n} : PP3 n m -> PP3 m n -> QQ2 n.

Goal QQ2 5.
  chc_auto.
  Show Proof.
Qed.

Goal 5 = 3 + 2.
  chc_auto.
  Show Proof.
Qed.

(* Test simple inductive goal *)


Inductive PP: nat -> Prop :=
  | P0 : PP 0
  | P1 {n} : PP n -> PP (S n).

Inductive QQ: Prop :=
  | Q0 : RR -> QQ
with RR : Prop :=
  | R0 : RR
.

(* Test simple inductive goal *)
Goal QQ.
  Show Proof.
  dno 5.
  chc_auto.
  Show Proof.
Qed.

(* Test with another simple inductive type *)
Inductive Even : nat -> Prop :=
  | Even0 : Even 0
  | EvenS n : Odd n -> Even (S n)
with Odd : nat -> Prop :=
  | OddS n : Even n -> Odd (S n).

Goal Even 4.
  Show Proof.
  chc_auto.
  (* chc_auto with depth=4. *)
  Show Proof.
Qed.

Inductive PPn: nat -> Prop :=
  | Pn0 : PPn 0
  | Pn2 {n} : PPn n -> PPn (S (S n))
  | Pn3 {n} : PPn n -> PPn (S (S (S n))).

Goal PPn 5.
  Show Proof.
  (* repeat constructor; fail. *)
  chc_auto.
  Show Proof.
Qed.

Goal PPn 1.
  Show Proof.
  try chc_auto.
Abort.

Goal PPn 5.
  Show Proof.
  chc_auto.
  (* chc_auto with depth=2. *)
  Show Proof.
Qed.

(* New tests for improved chc_auto *)

(* Test iterative deepening search *)
Goal PPn 32.
(* Goal PPn 52. *)
  (* This would require deeper search *)
  chc_auto.
  (* chc_auto with deepening. *)
  (* chc_auto with no_memo. *)
  (* chc_auto with no_memo deepening. *)
Qed.

(* Complex inductive type with multiple paths *)
Inductive ComplexTree : nat -> Prop :=
  | CTLeaf : ComplexTree 0
  | CTBranch1 n : ComplexTree n -> ComplexTree (S n)
  | CTBranch2 n : ComplexTree n -> ComplexTree n -> ComplexTree (S n)
  | CTBranch3 n m : ComplexTree n -> ComplexTree m -> ComplexTree (n + m).

(* This has multiple possible solutions, but memoization helps avoid redundant work *)
Goal ComplexTree 4.
  chc_auto.
  (* chc_auto with depth=6. *)
Qed.

(* Test discrimination capabilities *)
Inductive DataType : Type :=
  | A : DataType
  | B : DataType.

(* This proof requires inequality reasoning *)
(* Goal forall x y : DataType, x = A -> y = B -> x <> y.
  intros x y H1 H2.
  chc_auto. (* Should use discriminate tactic *)
Qed. *)

(* Test more complicated inductive structure requiring backtracking *)
Inductive BinaryTree : Type :=
  | Empty : BinaryTree
  | Node : BinaryTree -> nat -> BinaryTree -> BinaryTree.

Inductive HasValue : BinaryTree -> nat -> Prop :=
  | HVRoot : forall l n r, HasValue (Node l n r) n
  | HVLeft : forall l n r m, HasValue l m -> HasValue (Node l n r) m
  | HVRight : forall l n r m, HasValue r m -> HasValue (Node l n r) m.

(* Test with a complex goal that benefits from iterative deepening *)
Goal HasValue (Node (Node (Node Empty 5 Empty) 3 (Node Empty 7 Empty))
                   2
                   (Node (Node Empty 9 Empty) 4 Empty)) 9.
  (* chc_auto with deepening. *)
  chc_auto.
Qed.
