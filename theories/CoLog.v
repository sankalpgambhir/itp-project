Declare ML Module "CoLog:colog.plugin".

Inductive PP: nat -> Prop :=
  | P0 : PP 0
  | P1 {n} : PP n -> PP (S n).

Inductive QQ: Prop :=
  | Q0 : QQ.

(* Goal PP 5.
  Show Proof.
  dno 5.
  Show Proof.
Abort. *)

Goal PP 5.
  Show Proof.
  chc_auto.
  Show Proof.
Abort.
