Require Import ZArith.
Require Import Bignums.BigQ.BigQ.

Open Scope bigN_scope.
Check 2.
Check 1000000000000000000.
Check (BigN.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Eval vm_compute in 2^100.
Close Scope bigN_scope.

Open Scope bigZ_scope.
Check 2.
Check -1000000000000000000.
Check (BigZ.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
Eval vm_compute in (-2)^100.
Close Scope bigZ_scope.

Open Scope bigQ_scope.
Check 2.
Check -1000000000000000000.
Check (BigQ.add 2 2).
Check (2+2).
Eval vm_compute in 2+2.
Eval vm_compute in 65675757 * 565675998.
(* fractions *)
Check (6562 # 456). (* Nota: # is BigQ.Qq i.e. base fractions *)
Eval vm_compute in (BigQ.red (6562 # 456)).
Eval vm_compute in (1/-10000).
Eval vm_compute in (BigQ.red (1/(1/100))). (* back to integers... *)
Eval vm_compute in ((2/3)^(-100)).
Eval vm_compute in BigQ.red ((2/3)^(-1000) * (2/3)^(1000)).
Close Scope bigQ_scope.
