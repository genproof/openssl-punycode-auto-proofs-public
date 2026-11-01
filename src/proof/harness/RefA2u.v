(* The specifications of pr_put and pr_a2ulabel (harness/puny_ref.h), under the compspecs of harness/x_a2ulabel.c
   (struct pr_dec, struct pr_sink). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefDec.
Require Import OpensslPunycode.harness.x_a2ulabel.code.

#[export] Instance CS : compspecs. make_compspecs OpensslPunycode.harness.x_a2ulabel.code.prog. Defined.
Local Open Scope logic.

Definition t_sink := Tstruct _pr_sink noattr.

(* A sink record over buf of cap octets with the state k (written octets, short flag). *)
Definition sink_rep (buf: val) (cap: Z) (k: sink) : reptype t_sink :=
  (buf, (Vlong (Int64.repr cap), (Vlong (Int64.repr (Zlength (fst k))), Vint (Int.repr (if snd k then 1 else 0))))).

(* The buffer of a sink: the written octets then the rest of its initial contents. *)
Definition sink_buf (shb: share) (buf: val) (cap: Z) (init: list val) (w: list Z) : mpred :=
  data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf.

Definition pr_put_spec :=
  DECLARE _pr_put
  WITH shk: share, pk: val, buf: val, cap: Z, k: sink, init: list val, shb: share, shp: share, p: val, l: list Z
  PRE [ tptr t_sink, tptr tuchar, tulong ]
    PROP (writable_share shk; writable_share shb; readable_share shp; bytes_ok l; bytes_ok (fst k);
          Zlength (fst k) <= cap <= Int64.max_unsigned; Zlength init = cap)
    PARAMS (pk; p; Vlong (Int64.repr (Zlength l)))
    SEP (data_at shk t_sink (sink_rep buf cap k) pk; sink_buf shb buf cap init (fst k);
         arr0 shp tuchar (Zlength l) (vb l) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shk t_sink (sink_rep buf cap (put cap k l)) pk; sink_buf shb buf cap init (fst (put cap k l));
         arr0 shp tuchar (Zlength l) (vb l) p).

(* pr_a2ulabel(s, |s|, k, cps) on a fresh sink of cap >= 1 octets: the model's result and octets; cps is scratch. *)
Definition pr_a2ulabel_spec :=
  DECLARE _pr_a2ulabel
  WITH shs: share, ps: val, s: list Z, shk: share, pk: val, buf: val, cap: Z, init: list val, shb: share,
       shc: share, pc: val, cinit: list val
  PRE [ tptr tuchar, tulong, tptr t_sink, tptr tuint ]
    PROP (readable_share shs; writable_share shk; writable_share shb; writable_share shc; bytes_ok s; isptr ps;
          Zlength s < Int64.max_unsigned; 1 <= cap <= Int64.max_unsigned; Zlength init = cap;
          Zlength cinit = label_cap)
    PARAMS (ps; Vlong (Int64.repr (Zlength s)); pk; pc)
    SEP (arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap ([], false)) pk;
         sink_buf shb buf cap init []; data_at shc (tarray tuint label_cap) cinit pc)
  POST [ tint ]
    EX short: bool, EX cinit': list val,
    PROP (Zlength cinit' = label_cap)
    RETURN (Vint (Int.repr (fst (a2ulabel s cap))))
    SEP (arr0 shs tuchar (Zlength s) (vb s) ps;
         data_at shk t_sink (sink_rep buf cap (snd (a2ulabel s cap), short)) pk;
         sink_buf shb buf cap init (snd (a2ulabel s cap)); data_at shc (tarray tuint label_cap) cinit' pc).

Definition Vprog : varspecs := [].
Definition Gprog_put : funspecs := [].
Definition Gprog_a2ulabel : funspecs :=
  [pr_put_spec; OpensslPunycode.proof.harness.RefDec.pr_decode_spec; OpensslPunycode.proof.harness.RefRt.pr_utf8_spec].
