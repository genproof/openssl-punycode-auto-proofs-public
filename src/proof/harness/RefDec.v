(* The specifications of pr_digit_value and pr_decode (harness/puny_ref.h), under the compspecs of harness/x_decode.c
   (struct pr_dec); the same Clight is in harness/x_a2ulabel.c, whose program has struct pr_dec too.
  *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_decode.code.

#[export] Instance CS : compspecs. make_compspecs OpensslPunycode.harness.x_decode.code.prog. Defined.
Local Open Scope logic.

Definition t_dec := Tstruct _pr_dec noattr.

Definition pr_digit_value_spec :=
  DECLARE _pr_digit_value
  WITH c: Z
  PRE [ tuchar ]
    PROP (0 <= c <= Byte.max_unsigned) PARAMS (Vint (Int.repr c)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (digit_value c))) SEP ().

(* pr_decode(in, |inp|, out, cap, d): the model; the array holds the output so far then the rest of init, d.ok and
   d.count = the length of the output so far. *)
Definition pr_decode_spec :=
  DECLARE _pr_decode
  WITH shi: share, pin: val, inp: list Z, sho: share, pout: val, cap: Z, init: list val, shd: share, pd: val
  PRE [ tptr tuchar, tulong, tptr tuint, tulong, tptr t_dec ]
    PROP (readable_share shi; writable_share sho; writable_share shd; bytes_ok inp;
          Zlength inp < Int.max_unsigned; 0 <= cap <= Int.max_unsigned; Zlength init = cap)
    PARAMS (pin; Vlong (Int64.repr (Zlength inp)); pout; Vlong (Int64.repr cap); pd)
    SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin; arr0 sho tuint cap init pout; data_at_ shd t_dec pd)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (arr0 shi tuchar (Zlength inp) (vb inp) pin;
         arr0 sho tuint cap (vb (snd (decode inp cap)) ++ sublist (Zlength (snd (decode inp cap))) cap init) pout;
         data_at shd t_dec (Vint (Int.repr (if fst (decode inp cap) then 1 else 0)),
                            Vlong (Int64.repr (Zlength (snd (decode inp cap))))) pd).

Definition Vprog : varspecs := [].
Definition Gprog_decode : funspecs :=
  [pr_digit_value_spec; OpensslPunycode.proof.harness.RefRt.pr_threshold_spec;
   OpensslPunycode.proof.harness.RefRt.pr_adapt_spec].
Definition Gprog_none : funspecs := [].
