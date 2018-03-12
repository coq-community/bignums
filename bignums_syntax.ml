(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "bignums_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(* digit-based syntax for int31, bigN bigZ and bigQ *)

open Bigint
open Names
open Globnames
open Glob_term

(*** Constants for locating int31 / bigN / bigZ / bigQ constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let make_mind mp id = Names.MutInd.make2 mp (Label.make id)
let make_mind_mpfile dir id = make_mind (MPfile (make_dir dir)) id
let make_mind_mpdot dir modname id =
  let mp = MPdot (MPfile (make_dir dir), Label.make modname)
  in make_mind mp id


(* int31 stuff *)
let int31_module = ["Coq";"Numbers";"Cyclic"; "Int31"; "Int31"]
let int31_path = make_path int31_module "int31"
let int31_id = make_mind_mpfile int31_module
let int31_scope = "int31_scope"

let int31_construct = ConstructRef ((int31_id "int31",0),1)

let int31_0 = ConstructRef ((int31_id "digits",0),1)
let int31_1 = ConstructRef ((int31_id "digits",0),2)


(* bigN stuff*)

(* During Bignums migration, DoubleType.v moved.
   We hence use a more tolerant approach here. *)

let zn2z_W0 = lazy (Nametab.locate (Libnames.qualid_of_string "DoubleType.W0"))
let zn2z_WW = lazy (Nametab.locate (Libnames.qualid_of_string "DoubleType.WW"))

let bigN_module = ["Bignums"; "BigN"; "BigN" ]
let bigN_path = make_path (bigN_module@["BigN"]) "t"
let bigN_t = make_mind_mpdot bigN_module "BigN" "t'"
let bigN_scope = "bigN_scope"

(* number of inlined level of bigN (actually the level 0 to n_inlined-1 are inlined) *)
let n_inlined = 7

let bigN_constructor i =
  ConstructRef ((bigN_t,0),(min i n_inlined)+1)

(*bigZ stuff*)
let bigZ_module = ["Bignums"; "BigZ"; "BigZ" ]
let bigZ_path = make_path (bigZ_module@["BigZ"]) "t"
let bigZ_t = make_mind_mpdot bigZ_module "BigZ" "t_"
let bigZ_scope = "bigZ_scope"

let bigZ_pos = ConstructRef ((bigZ_t,0),1)
let bigZ_neg = ConstructRef ((bigZ_t,0),2)


(*bigQ stuff*)
let bigQ_module = ["Bignums"; "BigQ"; "BigQ"]
let bigQ_path = make_path (bigQ_module@["BigQ"]) "t"
let bigQ_t = make_mind_mpdot bigQ_module "BigQ" "t_"
let bigQ_scope = "bigQ_scope"

let bigQ_z =  ConstructRef ((bigQ_t,0),1)


(*** Definition of the Non_closed exception, used in the pretty printing ***)
exception Non_closed

(*** Parsing for int31 in digital notation ***)

(* parses a *non-negative* integer (from bigint.ml) into an int31
   wraps modulo 2^31 *)
let int31_of_pos_bigint ?loc n =
  let ref_construct = DAst.make ?loc @@ GRef (int31_construct, None) in
  let ref_0 = DAst.make ?loc @@ GRef (int31_0, None) in
  let ref_1 = DAst.make ?loc @@ GRef (int31_1, None) in
  let rec args counter n =
    if counter <= 0 then
      []
    else
      let (q,r) = div2_with_rest n in
	(if r then ref_1 else ref_0)::(args (counter-1) q)
  in
  DAst.make ?loc @@ GApp (ref_construct, List.rev (args 31 n))

let error_negative ?loc =
  CErrors.user_err ?loc ~hdr:"interp_int31" (Pp.str "int31 are only non-negative numbers.")

let interp_int31 ?loc n =
  if is_pos_or_zero n then
    int31_of_pos_bigint ?loc n
  else
    error_negative ?loc

(* Pretty prints an int31 *)

let is_gr c r = match DAst.get c with
| GRef (ref, _) -> eq_gr ref r
| _ -> false

let bigint_of_int31 =
  let rec args_parsing args cur =
    match args with
      | [] -> cur
      | b::l when is_gr b int31_0 -> args_parsing l (mult_2 cur)
      | b::l when is_gr b int31_1 -> args_parsing l (add_1 (mult_2 cur))
      | _ -> raise Non_closed
  in
  fun c -> match DAst.get c with
  | GApp (c, args) when is_gr c int31_construct -> args_parsing args zero
  | _ -> raise Non_closed

let uninterp_int31 (AnyGlobConstr i) =
  try
    Some (bigint_of_int31 i)
  with Non_closed ->
    None

(* Actually declares the interpreter for int31 *)
let _ = Notation.declare_numeral_interpreter int31_scope
  (int31_path, int31_module)
  interp_int31
  ([DAst.make @@ GRef (int31_construct, None)],
   uninterp_int31,
   true)


(*** Parsing for bigN in digital notation ***)
(* the base for bigN (in Coq) that is 2^31 in our case *)
let base = pow two 31

(* base of the bigN of height N : (2^31)^(2^n) *)
let rank n =
  let rec rk n pow2 =
    if n <= 0 then pow2
    else rk (n-1) (mult pow2 pow2)
  in rk n base

(* splits a number bi at height n, that is the rest needs 2^n int31 to be stored
   it is expected to be used only when the quotient would also need 2^n int31 to be
   stored *)
let split_at n bi =
  euclid bi (rank (n-1))

(* search the height of the Coq bigint needed to represent the integer bi *)
let height bi =
  let rec hght n pow2 =
    if less_than bi pow2 then n
    else hght (n+1) (mult pow2 pow2)
  in hght 0 base

(* n must be a non-negative integer (from bigint.ml) *)
let word_of_pos_bigint ?loc hght n =
  let ref_W0 = DAst.make ?loc @@ GRef (Lazy.force zn2z_W0, None) in
  let ref_WW = DAst.make ?loc @@ GRef (Lazy.force zn2z_WW, None) in
  let rec decomp hgt n =
    if hgt <= 0 then
      int31_of_pos_bigint ?loc n
    else if equal n zero then
      DAst.make ?loc @@ GApp (ref_W0, [DAst.make ?loc @@ GHole (Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None)])
    else
      let (h,l) = split_at hgt n in
      DAst.make ?loc @@ GApp (ref_WW, [DAst.make ?loc @@ GHole (Evar_kinds.InternalHole, Misctypes.IntroAnonymous, None);
			   decomp (hgt-1) h;
			   decomp (hgt-1) l])
  in
  decomp hght n

let nat_of_int ?loc n =
  let ref_O = DAst.make ?loc (GRef (Coqlib.glob_O, None)) in
  let ref_S = DAst.make ?loc (GRef (Coqlib.glob_S, None)) in
  let rec mk_nat acc n =
    if Int.equal n 0 then acc
    else
      mk_nat (DAst.make ?loc (GApp (ref_S, [acc]))) (pred n)
  in
  mk_nat ref_O n

let bigN_of_pos_bigint ?loc n =
  let h = height n in
  let ref_constructor = DAst.make ?loc @@ GRef (bigN_constructor h, None) in
  let word = word_of_pos_bigint ?loc h n in
  let args =
    if h < n_inlined then [word]
    else [nat_of_int ?loc (h-n_inlined);word]
  in
  DAst.make ?loc @@ GApp (ref_constructor, args)

let bigN_error_negative ?loc =
  CErrors.user_err ?loc ~hdr:"interp_bigN" (Pp.str "bigN are only non-negative numbers.")

let interp_bigN ?loc n =
  if is_pos_or_zero n then
    bigN_of_pos_bigint ?loc n
  else
    bigN_error_negative ?loc


(* Pretty prints a bigN *)

let bigint_of_word =
  let rec get_height rc =
    match DAst.get rc with
    | GApp (c, [_;lft;rght])
         when is_gr c (Lazy.force zn2z_WW) ->
      1+max (get_height lft) (get_height rght)
    | _ -> 0
  in
  let rec transform hght rc =
    match DAst.get rc with
    | GApp (c,_)
         when is_gr c (Lazy.force zn2z_W0) -> zero
    | GApp (c, [_;lft;rght])
         when is_gr c (Lazy.force zn2z_WW) ->
      let new_hght = hght-1 in
      add (mult (rank new_hght)
             (transform new_hght lft))
	(transform new_hght rght)
    | _ -> bigint_of_int31 rc
  in
  fun rc ->
    let hght = get_height rc in
    transform hght rc

let bigint_of_bigN rc =
  match DAst.get rc with
  | GApp (_,[one_arg]) -> bigint_of_word one_arg
  | GApp (_,[_;second_arg]) -> bigint_of_word second_arg
  | _ -> raise Non_closed

let uninterp_bigN (AnyGlobConstr rc) =
  try
    Some (bigint_of_bigN rc)
  with Non_closed ->
    None


(* declare the list of constructors of bigN used in the declaration of the
   numeral interpreter *)

let bigN_list_of_constructors =
  let rec build i =
    if i < n_inlined+1 then
      (DAst.make @@ GRef (bigN_constructor i,None))::(build (i+1))
    else
      []
  in
  build 0

(* Actually declares the interpreter for bigN *)
let _ = Notation.declare_numeral_interpreter bigN_scope
  (bigN_path, bigN_module)
  interp_bigN
  (bigN_list_of_constructors,
   uninterp_bigN,
   true)


(*** Parsing for bigZ in digital notation ***)
let interp_bigZ ?loc n =
  let ref_pos = DAst.make ?loc @@ GRef (bigZ_pos, None) in
  let ref_neg = DAst.make ?loc @@ GRef (bigZ_neg, None) in
  if is_pos_or_zero n then
    DAst.make ?loc @@ GApp (ref_pos, [bigN_of_pos_bigint ?loc n])
  else
    DAst.make ?loc @@ GApp (ref_neg, [bigN_of_pos_bigint ?loc (neg n)])

(* pretty printing functions for bigZ *)
let bigint_of_bigZ c = match DAst.get c with
  | GApp (c, [one_arg]) when is_gr c bigZ_pos -> bigint_of_bigN one_arg
  | GApp (c, [one_arg]) when is_gr c bigZ_neg ->
      let opp_val = bigint_of_bigN one_arg in
      if equal opp_val zero then
	raise Non_closed
      else
	neg opp_val
  | _ -> raise Non_closed


let uninterp_bigZ (AnyGlobConstr rc) =
  try
    Some (bigint_of_bigZ rc)
  with Non_closed ->
    None

(* Actually declares the interpreter for bigZ *)
let _ = Notation.declare_numeral_interpreter bigZ_scope
  (bigZ_path, bigZ_module)
  interp_bigZ
  ([DAst.make @@ GRef (bigZ_pos, None);
    DAst.make @@ GRef (bigZ_neg, None)],
   uninterp_bigZ,
   true)

(*** Parsing for bigQ in digital notation ***)
let interp_bigQ ?loc n =
  let ref_z = DAst.make ?loc @@ GRef (bigQ_z, None) in
  DAst.make ?loc @@ GApp (ref_z, [interp_bigZ ?loc n])

let uninterp_bigQ (AnyGlobConstr rc) =
  try match DAst.get rc with
    | GApp (c, [one_arg]) when is_gr c bigQ_z ->
	Some (bigint_of_bigZ one_arg)
    | _ -> None (* we don't pretty-print yet fractions *)
  with Non_closed -> None

(* Actually declares the interpreter for bigQ *)
let _ = Notation.declare_numeral_interpreter bigQ_scope
  (bigQ_path, bigQ_module)
  interp_bigQ
  ([DAst.make @@ GRef (bigQ_z, None)], uninterp_bigQ,
   true)
