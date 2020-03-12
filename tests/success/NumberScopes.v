
(* We check that various definitions or lemmas have the correct
   argument scopes, especially the ones created via functor application. *)

Close Scope nat_scope.

Require Import Bignums.BigN.BigN.
Check (BigN.add 1 2).
Check (BigN.add_comm 1 2).
Check (BigN.min_comm 1 2).
Definition f_bigN (x:bigN) := x.
Check (f_bigN 1).

Require Import Bignums.BigZ.BigZ.
Check (BigZ.add 1 2).
Check (BigZ.add_comm 1 2).
Check (BigZ.min_comm 1 2).
Definition f_bigZ (x:bigZ) := x.
Check (f_bigZ 1).

Require Import Bignums.BigQ.BigQ.
Check (BigQ.add 1 2).
Check (BigQ.add_comm 1 2).
Check (BigQ.min_comm 1 2).
Definition f_bigQ (x:bigQ) := x.
Check (f_bigQ 1).
