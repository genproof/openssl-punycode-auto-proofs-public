(* Shared definitions of the pieces of the body of the harness's encoder encode (TrtBodyEncode.v): the function's
   postcondition, the Clight sub-statements (verbatim from the law's code.v), the states between pieces and the
   statements of the pieces.  The algorithm is pr_encode's (src/proof/harness/BodyEncode.v), so the model facts of
   EncModel.v and the buffer lemmas of EncDefs.v (bufv: the octets written, then the rest of the initial buffer) are
   reused; the output goes through put, its length lives in *len. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Local Open Scope logic.

Definition TDelta : tycontext := func_tycontext f_encode Vprog Gprog_encode nil.

(* The postcondition of encode's body (as start_function states it). *)
Definition tpost (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) : ret_assert :=
  frame_ret_assert
  (function_body_ret_assert tint
     (EX o' : list val,
      PROP (Zlength o' = room)
      RETURN (Vint (Int.repr (if RefRt.encode_fits cps room then 1 else 0)))
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
      arr0 sho tuchar room (RefRt.encode_out cps room oinit o') po;
      if RefRt.encode_fits cps room
      then data_at shl tulong (Vlong (Int64.repr (RefRt.encode_len cps))) pl
      else data_at_ shl tulong pl))%argsassert) (stackframe_of f_encode).

(* A return of 0 when the encoding does not fit: o' := the current buffer, *len holds anything. *)
Lemma tret0_entail: forall cps room oinit shc pc sho po shl pl buf v,
  RefRt.encode_fits cps room = false -> Zlength buf = room ->
  arr0 shc tuint (Zlength cps) (vb cps) pc * arr0 sho tuchar room buf po * data_at shl tulong v pl
  |-- EX a : list val,
      !! (Zlength a = room /\ Vint (Int.repr 0) = Vint (Int.repr (if RefRt.encode_fits cps room then 1 else 0))) &&
      (arr0 shc tuint (Zlength cps) (vb cps) pc *
       (arr0 sho tuchar room (RefRt.encode_out cps room oinit a) po *
        (if RefRt.encode_fits cps room then data_at shl tulong (Vlong (Int64.repr (RefRt.encode_len cps))) pl
         else data_at_ shl tulong pl))).
Proof.
  intros. Exists buf. rewrite encode_out_false by auto. rewrite H.
  entailer!.
Qed.

(* ---- The Clight sub-statements: the branch c == n of the pass (the digits of delta, adapt, delta = 0, h++),
   the pass over the code points, the body of the main loop after its test, the main loop. ---- *)

Definition tstmt_digs := (Ssequence (Sset _q (Etempvar _delta tulong)) (Ssequence (Ssequence (Sset _k (Ecast
  (Econst_int (Int.repr 36) tint) tulong)) (Sloop (Ssequence Sskip (Ssequence (Ssequence (Sifthenelse (Ebinop Ole
  (Etempvar _k tulong) (Etempvar _bias tulong) tint) (Sset _t'6 (Ecast (Econst_int (Int.repr 1) tint) tulong))
  (Sifthenelse (Ebinop Oge (Etempvar _k tulong) (Ebinop Oadd (Etempvar _bias tulong) (Econst_int (Int.repr 26)
  tint) tulong) tint) (Ssequence (Sset _t'6 (Ecast (Econst_int (Int.repr 26) tint) tulong)) (Sset _t'6 (Ecast
  (Etempvar _t'6 tulong) tulong))) (Ssequence (Sset _t'6 (Ecast (Ebinop Osub (Etempvar _k tulong) (Etempvar _bias
  tulong) tulong) tulong)) (Sset _t'6 (Ecast (Etempvar _t'6 tulong) tulong))))) (Sset _t (Etempvar _t'6 tulong)))
  (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _q tulong) (Etempvar _t tulong) tint) Sbreak Sskip) (Ssequence
  (Ssequence (Ssequence (Scall (Some _t'7) (Evar _digit (Tfunction (tulong :: nil) tulong cc_default)) ((Ebinop
  Oadd (Etempvar _t tulong) (Ebinop Omod (Ebinop Osub (Etempvar _q tulong) (Etempvar _t tulong) tulong) (Ebinop
  Osub (Econst_int (Int.repr 36) tint) (Etempvar _t tulong) tulong) tulong) tulong) :: nil)) (Scall (Some _t'8)
  (Evar _put (Tfunction ((tptr tuchar) :: tulong :: (tptr tulong) :: tulong :: nil) tint cc_default)) ((Etempvar
  _out (tptr tuchar)) :: (Etempvar _room tulong) :: (Etempvar _len (tptr tulong)) :: (Etempvar _t'7 tulong) ::
  nil))) (Sifthenelse (Eunop Onotbool (Etempvar _t'8 tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  Sskip)) (Sset _q (Ebinop Odiv (Ebinop Osub (Etempvar _q tulong) (Etempvar _t tulong) tulong) (Ebinop Osub
  (Econst_int (Int.repr 36) tint) (Etempvar _t tulong) tulong) tulong)))))) (Sset _k (Ebinop Oadd (Etempvar _k
  tulong) (Econst_int (Int.repr 36) tint) tulong)))) (Ssequence (Ssequence (Ssequence (Scall (Some _t'9) (Evar
  _digit (Tfunction (tulong :: nil) tulong cc_default)) ((Etempvar _q tulong) :: nil)) (Scall (Some _t'10) (Evar
  _put (Tfunction ((tptr tuchar) :: tulong :: (tptr tulong) :: tulong :: nil) tint cc_default)) ((Etempvar _out
  (tptr tuchar)) :: (Etempvar _room tulong) :: (Etempvar _len (tptr tulong)) :: (Etempvar _t'9 tulong) :: nil)))
  (Sifthenelse (Eunop Onotbool (Etempvar _t'10 tint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))
  (Ssequence (Ssequence (Scall (Some _t'11) (Evar _rfc_adapt (Tfunction (tulong :: tulong :: tint :: nil) tulong
  cc_default)) ((Etempvar _delta tulong) :: (Ebinop Oadd (Etempvar _h tulong) (Econst_int (Int.repr 1) tint)
  tulong) :: (Ebinop Oeq (Etempvar _h tulong) (Etempvar _b tulong) tint) :: nil)) (Sset _bias (Etempvar _t'11
  tulong))) (Ssequence (Sset _delta (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sset _h (Ebinop Oadd (Etempvar
  _h tulong) (Econst_int (Int.repr 1) tint) tulong))))))).

Definition tstmt_passloop := (Ssequence (Sset _j__2 (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop
  (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _j__2 tulong) (Etempvar _m tulong) tint) Sskip Sbreak) (Ssequence
  (Ssequence (Sset _t'13 (Ederef (Ebinop Oadd (Etempvar _cps (tptr tuint)) (Etempvar _j__2 tulong) (tptr tuint))
  tuint)) (Sifthenelse (Ebinop Olt (Etempvar _t'13 tuint) (Etempvar _n tulong) tint) (Ssequence (Sset _delta
  (Ebinop Oadd (Etempvar _delta tulong) (Econst_int (Int.repr 1) tint) tulong)) (Sifthenelse (Ebinop Ogt (Etempvar
  _delta tulong) (Econst_int (Int.repr (-1)) tuint) tint) (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))
  Sskip)) (Ssequence (Sset _t'12 (Ederef (Ebinop Oadd (Etempvar _cps (tptr tuint)) (Etempvar _j__2 tulong) (tptr
  tuint)) tuint)) (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tuint) (Etempvar _n tulong) tint) tstmt_digs Sskip))))
  (Sset _j__2 (Ebinop Oadd (Etempvar _j__2 tulong) (Econst_int (Int.repr 1) tint) tulong)))).

Definition tstmt_roundbody := (Ssequence (Sset _min (Econst_long (Int64.repr (-1)) tulong)) (Ssequence (Ssequence
  (Sset _j__1 (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar
  _j__1 tulong) (Etempvar _m tulong) tint) Sskip Sbreak) (Ssequence (Ssequence (Sset _t'15 (Ederef (Ebinop Oadd
  (Etempvar _cps (tptr tuint)) (Etempvar _j__1 tulong) (tptr tuint)) tuint)) (Sifthenelse (Ebinop Oge (Etempvar
  _t'15 tuint) (Etempvar _n tulong) tint) (Ssequence (Sset _t'16 (Ederef (Ebinop Oadd (Etempvar _cps (tptr tuint))
  (Etempvar _j__1 tulong) (tptr tuint)) tuint)) (Sset _t'4 (Ecast (Ebinop Olt (Etempvar _t'16 tuint) (Etempvar _min
  tulong) tint) tbool))) (Sset _t'4 (Econst_int (Int.repr 0) tint)))) (Sifthenelse (Etempvar _t'4 tint) (Ssequence
  (Sset _t'14 (Ederef (Ebinop Oadd (Etempvar _cps (tptr tuint)) (Etempvar _j__1 tulong) (tptr tuint)) tuint)) (Sset
  _min (Ecast (Etempvar _t'14 tuint) tulong))) Sskip))) (Sset _j__1 (Ebinop Oadd (Etempvar _j__1 tulong)
  (Econst_int (Int.repr 1) tint) tulong)))) (Ssequence (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _delta tulong)
  (Econst_int (Int.repr (-1)) tuint) tint) (Sset _t'5 (Econst_int (Int.repr 1) tint)) (Sset _t'5 (Ecast (Ebinop Ogt
  (Ebinop Osub (Etempvar _min tulong) (Etempvar _n tulong) tulong) (Ebinop Odiv (Ebinop Osub (Econst_int (Int.repr
  (-1)) tuint) (Etempvar _delta tulong) tulong) (Ebinop Oadd (Etempvar _h tulong) (Econst_int (Int.repr 1) tint)
  tulong) tulong) tint) tbool))) (Sifthenelse (Etempvar _t'5 tint) (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  Sskip)) (Ssequence (Sset _delta (Ebinop Oadd (Etempvar _delta tulong) (Ebinop Omul (Ebinop Osub (Etempvar _min
  tulong) (Etempvar _n tulong) tulong) (Ebinop Oadd (Etempvar _h tulong) (Econst_int (Int.repr 1) tint) tulong)
  tulong) tulong)) (Ssequence (Sset _n (Etempvar _min tulong)) (Ssequence tstmt_passloop (Sset _delta (Ebinop Oadd
  (Etempvar _delta tulong) (Econst_int (Int.repr 1) tint) tulong)))))))).

Definition tstmt_mainloop := (Ssequence (Sset _h (Etempvar _b tulong)) (Sloop (Ssequence (Sifthenelse (Ebinop Olt
  (Etempvar _h tulong) (Etempvar _m tulong) tint) Sskip Sbreak) tstmt_roundbody) (Sset _n (Ebinop Oadd (Etempvar _n
  tulong) (Econst_int (Int.repr 1) tint) tulong)))).

(* ---- The states between the pieces ---- *)

(* After the branch c == n of the pass (j: the pass's index): the digits of delta written, bias adapted. *)
Definition tdig_q (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (n delta bias h b j: Z) (out: list Z) : environ -> mpred :=
  PROP (Zlength (out ++ enc_digits 64 delta 36 bias) <= room)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr 0));
    temp _bias (Vlong (Int64.repr (adapt delta (h + 1) (h =? b))));
    temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr (h + 1))); temp _j__2 (Vlong (Int64.repr j));
    temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
    temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc;
       arr0 sho tuchar room (bufv (out ++ enc_digits 64 delta 36 bias) room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength (out ++ enc_digits 64 delta 36 bias)))) pl).

(* The invariant of the main loop (before its test h < m): the rounds left from code point n, with fuel f
   (Zlength cps - h < f: h grows in every round), h = the number of code points below n.  B: the number of basic
   code points. *)
Definition tenc_inv (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (B: Z) : environ -> mpred :=
  EX n: Z, EX delta: Z, EX bias: Z, EX h: Z, EX out: list Z, EX f: nat,
  PROP (encode cps = enc_rounds cps f n delta bias h B out; (Zlength cps - h < Z.of_nat f)%Z;
        h = cnt_lt n cps; 128 <= n <= maxint + 1; 0 <= delta <= maxint + 1; 0 <= bias <= 2400;
        Zlength out <= room)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
         temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl).

(* After the body of the main loop, before its increment n = n + 1: tenc_inv for n + 1. *)
Definition tenc_cont (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (B: Z) : environ -> mpred :=
  EX n: Z, EX delta: Z, EX bias: Z, EX h: Z, EX out: list Z, EX f: nat,
  PROP (encode cps = enc_rounds cps f (n + 1) delta bias h B out; (Zlength cps - h < Z.of_nat f)%Z;
        h = cnt_lt (n + 1) cps; 128 <= n + 1 <= maxint + 1; 0 <= delta <= maxint + 1; 0 <= bias <= 2400;
        Zlength out <= room)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
         temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl).

(* ---- The statements of the pieces ---- *)

(* The branch c == n of the pass, for the code point n of the round: the encoding continues with the digits of
   delta (kont: the rest of the pass over rest, then the rounds after it). *)
Definition tdig_ok : Prop := forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl
  (n delta bias h b j: Z) (out: list Z) (f: nat) (rest: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  4 * Zlength cps <= Int64.max_unsigned -> 0 <= room <= Int64.max_unsigned -> Zlength oinit = room ->
  encode cps = kont cps f n rest 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias) ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> 0 <= h <= 2 * Zlength cps -> 0 <= b <= Zlength cps ->
  Zlength out <= room ->
  semax TDelta
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr b)); temp _h (Vlong (Int64.repr h));
      temp _j__2 (Vlong (Int64.repr j)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
      temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl))
   tstmt_digs
   (overridePost (tdig_q shc pc cps sho po room oinit shl pl n delta bias h b j out)
     (tpost shc pc cps sho po room oinit shl pl)).

(* The pass over all code points for the code point n of the round (h0: h before it). *)
Definition tpass_ok : Prop := forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl
  (f: nat) (n h0 B delta bias: Z) (out: list Z),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> 4 * Zlength cps <= Int64.max_unsigned ->
  0 <= room <= Int64.max_unsigned -> Zlength oinit = room ->
  0 <= h0 <= Zlength cps -> 0 <= B <= Zlength cps -> 0 <= n <= maxint ->
  encode cps = kont cps f n cps delta bias h0 B out ->
  0 <= delta <= maxint -> 0 <= bias <= 2400 -> Zlength out <= room ->
  semax TDelta
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h0));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl))
   tstmt_passloop
   (overridePost
     (EX delta': Z, EX bias': Z, EX h: Z, EX out': list Z,
      PROP (encode cps = enc_rounds cps f (n + 1) (delta' + 1) bias' h B out';
            (h = h0 + cnt_eq n cps)%Z; 0 <= delta' <= maxint; 0 <= bias' <= 2400; Zlength out' <= room)
      LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta'));
         temp _bias (Vlong (Int64.repr bias')); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
         temp _room (Vlong (Int64.repr room)); temp _len pl)
      SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out' room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out'))) pl))
     (tpost shc pc cps sho po room oinit shl pl)).

(* The body of the main loop after its test h < m: one round (the minimum code point >= n, the overflow test,
   the pass, delta++). *)
Definition tround_ok : Prop := forall {Espec: OracleKind} shc pc cps sho po room oinit shl pl
  (B n delta bias h: Z) (out: list Z) (f: nat),
  readable_share shc -> writable_share sho -> writable_share shl ->
  Forall (fun c => 0 <= c <= Int.max_unsigned) cps -> 4 * Zlength cps <= Int64.max_unsigned ->
  0 <= room <= Int64.max_unsigned -> Zlength oinit = room -> 0 <= B <= Zlength cps ->
  encode cps = enc_rounds cps f n delta bias h B out -> Zlength cps - h < Z.of_nat f ->
  h = cnt_lt n cps -> 128 <= n <= maxint + 1 -> 0 <= delta <= maxint + 1 -> 0 <= bias <= 2400 ->
  Zlength out <= room -> h < Zlength cps ->
  semax TDelta
   (PROP () LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
      temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
      temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps))); temp _out po;
      temp _room (Vlong (Int64.repr room)); temp _len pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
         data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl))
   tstmt_roundbody
   (overridePost (tenc_cont shc pc cps sho po room oinit shl pl B) (tpost shc pc cps sho po room oinit shl pl)).
