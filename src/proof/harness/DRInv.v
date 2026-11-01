(* Shared vocabulary of the proof of pr_decode (harness/puny_ref.h) under the decode harness's compspecs, split
   over the DR*.v files: its sub-statements (copied from the Clight body), its ret_assert, the invariants of the main
   loop and of the digit loop. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.proof.harness.DRModel.
Require Import OpensslPunycode.harness.x_decode.code.

Definition stmt_delim : statement := (Ssequence (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _j tulong) (Etempvar _len tulong) tint) Sskip Sbreak) (Ssequence (Sset _t'8 (Ederef (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _j tulong) (tptr tuchar)) tuchar)) (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuchar) (Econst_int (Int.repr 45) tint) tint) (Sset _b (Etempvar _j tulong)) Sskip))) (Sset _j (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint) tulong)))).

Definition stmt_basic : statement := (Ssequence (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _j tulong) (Etempvar _b tulong) tint) Sskip Sbreak) (Ssequence (Ssequence (Sset _t'7 (Ederef (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _j tulong) (tptr tuchar)) tuchar)) (Sifthenelse (Ebinop Oge (Etempvar _t'7 tuchar) (Econst_int (Int.repr 128) tint) tint) (Sreturn None) Sskip)) (Ssequence (Ssequence (Sset _t'6 (Ederef (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _j tulong) (tptr tuchar)) tuchar)) (Sassign (Ederef (Ebinop Oadd (Etempvar _out (tptr tuint)) (Etempvar _j tulong) (tptr tuint)) tuint) (Etempvar _t'6 tuchar))) (Sassign (Efield (Ederef (Etempvar _d (tptr (Tstruct _pr_dec noattr))) (Tstruct _pr_dec noattr)) _count tulong) (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint) tulong))))) (Sset _j (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint) tulong)))).

Definition stmt_digits : statement := (Sloop (Ssequence Sskip (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _pos tulong) (Etempvar _len tulong) tint) (Sreturn None) Sskip) (Ssequence (Ssequence (Ssequence (Sset _t'5 (Ederef (Ebinop Oadd (Etempvar _in (tptr tuchar)) (Etempvar _pos tulong) (tptr tuchar)) tuchar)) (Scall (Some _t'1) (Evar _pr_digit_value (Tfunction (tuchar :: nil) tulong cc_default)) ((Etempvar _t'5 tuchar) :: nil))) (Sset _digit (Etempvar _t'1 tulong))) (Ssequence (Sset _pos (Ebinop Oadd (Etempvar _pos tulong) (Econst_int (Int.repr 1) tint) tulong)) (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _digit tulong) (Econst_long (Int64.repr 36) tulong) tint) (Sreturn None) Sskip) (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tulong) (Ebinop Omul (Etempvar _digit tulong) (Etempvar _w tulong) tulong) tulong)) (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _i tulong) (Econst_long (Int64.repr 4294967295) tulong) tint) (Sreturn None) Sskip) (Ssequence (Ssequence (Scall (Some _t'2) (Evar _pr_threshold (Tfunction (tulong :: tulong :: nil) tulong cc_default)) ((Etempvar _k tulong) :: (Etempvar _bias tulong) :: nil)) (Sset _t (Etempvar _t'2 tulong))) (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _digit tulong) (Etempvar _t tulong) tint) Sbreak Sskip) (Ssequence (Sset _w (Ebinop Omul (Etempvar _w tulong) (Ebinop Osub (Econst_long (Int64.repr 36) tulong) (Etempvar _t tulong) tulong) tulong)) (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _w tulong) (Econst_long (Int64.repr 4294967295) tulong) tint) (Sreturn None) Sskip) (Sset _k (Ebinop Oadd (Etempvar _k tulong) (Econst_long (Int64.repr 36) tulong) tulong))))))))))))) Sskip).

Definition stmt_insert : statement := (Ssequence (Ssequence (Sset _j (Etempvar _outlen tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _j tulong) (Etempvar _i tulong) tint) Sskip Sbreak) (Ssequence (Sset _t'4 (Ederef (Ebinop Oadd (Etempvar _out (tptr tuint)) (Ebinop Osub (Etempvar _j tulong) (Econst_int (Int.repr 1) tint) tulong) (tptr tuint)) tuint)) (Sassign (Ederef (Ebinop Oadd (Etempvar _out (tptr tuint)) (Etempvar _j tulong) (tptr tuint)) tuint) (Etempvar _t'4 tuint)))) (Sset _j (Ebinop Osub (Etempvar _j tulong) (Econst_int (Int.repr 1) tint) tulong)))) (Ssequence (Sassign (Ederef (Ebinop Oadd (Etempvar _out (tptr tuint)) (Etempvar _i tulong) (tptr tuint)) tuint) (Ecast (Etempvar _n tulong) tuint)) (Ssequence (Sassign (Efield (Ederef (Etempvar _d (tptr (Tstruct _pr_dec noattr))) (Tstruct _pr_dec noattr)) _count tulong) (Ebinop Oadd (Etempvar _outlen tulong) (Econst_int (Int.repr 1) tint) tulong)) (Sset _i (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint) tulong))))).

Definition stmt_rest : statement := (Ssequence (Sset _outlen (Efield (Ederef (Etempvar _d (tptr (Tstruct _pr_dec noattr))) (Tstruct _pr_dec noattr)) _count tulong)) (Ssequence (Ssequence (Scall (Some _t'3) (Evar _pr_adapt (Tfunction (tulong :: tulong :: tint :: nil) tulong cc_default)) ((Ebinop Osub (Etempvar _i tulong) (Etempvar _oldi tulong) tulong) :: (Ebinop Oadd (Ecast (Etempvar _outlen tulong) tulong) (Econst_int (Int.repr 1) tint) tulong) :: (Ebinop Oeq (Etempvar _oldi tulong) (Econst_int (Int.repr 0) tint) tint) :: nil)) (Sset _bias (Etempvar _t'3 tulong))) (Ssequence (Sset _n (Ebinop Oadd (Etempvar _n tulong) (Ebinop Odiv (Etempvar _i tulong) (Ebinop Oadd (Ecast (Etempvar _outlen tulong) tulong) (Econst_int (Int.repr 1) tint) tulong) tulong) tulong)) (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _n tulong) (Econst_long (Int64.repr 4294967295) tulong) tint) (Sreturn None) Sskip) (Ssequence (Sset _i (Ebinop Omod (Etempvar _i tulong) (Ebinop Oadd (Ecast (Etempvar _outlen tulong) tulong) (Econst_int (Int.repr 1) tint) tulong) tulong)) (Ssequence (Sifthenelse (Ebinop Oge (Etempvar _outlen tulong) (Etempvar _cap tulong) tint) (Sreturn None) Sskip) stmt_insert)))))).

Definition stmt_main : statement := (Swhile (Ebinop Olt (Etempvar _pos tulong) (Etempvar _len tulong) tint) (Ssequence (Sset _oldi (Etempvar _i tulong)) (Ssequence (Sset _w (Ecast (Econst_int (Int.repr 1) tint) tulong)) (Ssequence (Sset _k (Econst_long (Int64.repr 36) tulong)) (Ssequence stmt_digits stmt_rest))))).

Local Open Scope logic.

(* The value of struct pr_dec (ok, count); a Definition, as a pair literal inside EX does not elaborate. *)
Definition dec_rep (ok c: Z) : reptype t_dec := (Vint (Int.repr ok), Vlong (Int64.repr c)).

Section Inv.
Variables (shi: share) (pin: val) (inp: list Z) (sho: share) (pout: val) (cap: Z) (init: list val)
  (shd: share) (pd: val).

(* The ret_assert of the body of pr_decode (after start_function). *)
Definition dr_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tvoid
      (PROP () RETURN ()
       SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
         arr0 sho tuint cap (vb (snd (decode inp cap)) ++ sublist (Zlength (snd (decode inp cap))) cap init) pout;
         data_at shd t_dec (Vint (Int.repr (if fst (decode inp cap) then 1 else 0)),
                            Vlong (Int64.repr (Zlength (snd (decode inp cap))))) pd)))
    (stackframe_of f_pr_decode).

(* The invariant of the main loop: the model state (pos, n, i, bias, out) with fuel f. *)
Definition dr_inv : environ -> mpred :=
  EX pos: Z, EX n: Z, EX i: Z, EX bias: Z, EX out: list Z, EX f: nat,
  PROP (0 <= Zlength out <= pos; pos <= Zlength inp; Zlength out <= cap; 0 <= i <= Zlength out;
        128 <= n <= maxint; 0 <= bias <= 2340; Zlength inp - pos <= Z.of_nat f;
        decode inp cap = steps inp f cap pos n i bias out)
  LOCAL (temp _pos (Vlong (Int64.repr pos)); temp _n (Vlong (Int64.repr n)); temp _i (Vlong (Int64.repr i));
         temp _bias (Vlong (Int64.repr bias));
         temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
  SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd).

Variables (pos n i bias: Z) (out: list Z).

(* The invariant of the digit loop of one delta (k = 36 (j + 1)), and its exit. *)
Definition dig_inv : environ -> mpred :=
  EX p: Z, EX i': Z, EX w: Z, EX j: Z,
  PROP (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias =
          digits inp (Z.to_nat (Zlength inp - p)) p i' w (36 * (j + 1)) bias;
        pos <= p <= Zlength inp; i <= i' <= maxint; 1 <= w <= maxint; 0 <= j <= p - pos)
  LOCAL (temp _k (Vlong (Int64.repr (36 * (j + 1)))); temp _w (Vlong (Int64.repr w));
         temp _oldi (Vlong (Int64.repr i)); temp _pos (Vlong (Int64.repr p)); temp _i (Vlong (Int64.repr i'));
         temp _n (Vlong (Int64.repr n)); temp _bias (Vlong (Int64.repr bias));
         temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
  SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd).

Definition dig_brk : environ -> mpred :=
  EX i1: Z, EX pos1: Z,
  PROP (digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias = Some (i1, pos1);
        i <= i1 <= maxint; pos < pos1 <= Zlength inp)
  LOCAL (temp _oldi (Vlong (Int64.repr i)); temp _pos (Vlong (Int64.repr pos1)); temp _i (Vlong (Int64.repr i1));
         temp _n (Vlong (Int64.repr n)); temp _bias (Vlong (Int64.repr bias));
         temp _in pin; temp _len (Vlong (Int64.repr (Zlength inp))); temp _out pout;
         temp _cap (Vlong (Int64.repr cap)); temp _d pd)
  SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
       arr0 sho tuint cap (vb out ++ sublist (Zlength out) cap init) pout;
       data_at shd t_dec (dec_rep 0 (Zlength out)) pd).

End Inv.
