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

(* digit-based syntax for int63, bigN bigZ and bigQ *)

open Bigint
open Names
open Glob_term

(*** Constants for locating bigN / bigZ / bigQ constructors ***)

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let make_mind mp id = Names.MutInd.make2 mp (Label.make id)
let make_mind_mpdot dir modname id =
  let mp = MPdot (MPfile (make_dir dir), Label.make modname)
  in make_mind mp id

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
  GlobRef.ConstructRef ((bigN_t,0),(min i n_inlined)+1)

(*bigZ stuff*)
let bigZ_module = ["Bignums"; "BigZ"; "BigZ" ]
let bigZ_path = make_path (bigZ_module@["BigZ"]) "t"
let bigZ_t = make_mind_mpdot bigZ_module "BigZ" "t_"
let bigZ_scope = "bigZ_scope"

let bigZ_pos = GlobRef.ConstructRef ((bigZ_t,0),1)
let bigZ_neg = GlobRef.ConstructRef ((bigZ_t,0),2)


(*bigQ stuff*)
let bigQ_module = ["Bignums"; "BigQ"; "BigQ"]
let bigQ_path = make_path (bigQ_module@["BigQ"]) "t"
let bigQ_t = make_mind_mpdot bigQ_module "BigQ" "t_"
let bigQ_scope = "bigQ_scope"

let bigQ_z =  GlobRef.ConstructRef ((bigQ_t,0),1)


let is_gr c r = match DAst.get c with
| GRef (ref, _) -> GlobRef.equal ref r
| _ -> false

(*** Parsing for bigN in digital notation ***)
(* the base for bigN (in Coq) that is 2^63 in our case *)
let base = pow two 63

(* base of the bigN of height N : (2^63)^(2^n) *)
let rank n =
  let rec rk n pow2 =
    if n <= 0 then pow2
    else rk (n-1) (mult pow2 pow2)
  in rk n base

(* splits a number bi at height n, that is the rest needs 2^n int63 to be stored
   it is expected to be used only when the quotient would also need 2^n int63 to be
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
      DAst.make ?loc (GInt (Notation.int63_of_pos_bigint n))
    else if equal n zero then
      DAst.make ?loc @@ GApp (ref_W0, [DAst.make ?loc @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None)])
    else
      let (h,l) = split_at hgt n in
      DAst.make ?loc @@ GApp (ref_WW, [DAst.make ?loc @@ GHole (Evar_kinds.InternalHole, Namegen.IntroAnonymous, None);
			   decomp (hgt-1) h;
			   decomp (hgt-1) l])
  in
  decomp hght n

let nat_of_int ?loc n =
  let ref_O = DAst.make ?loc (GRef (Coqlib.lib_ref "num.nat.O", None)) in
  let ref_S = DAst.make ?loc (GRef (Coqlib.lib_ref "num.nat.S", None)) in
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

exception Non_closed

let bigint_of_int63 c =
  match DAst.get c with
  | GInt i -> Bigint.of_string (Uint63.to_string i)
  | _ -> raise Non_closed

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
    | _ -> bigint_of_int63 rc
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
