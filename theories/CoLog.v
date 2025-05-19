Declare ML Module "CoLog:colog.plugin".

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
  chc_auto with depth 4.
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
  chc_auto with depth 2.
  Show Proof.
Qed.
