(* The specifications of the harnesses' own functions (harness/puny_ref.h, harness/common.h) that are the same
   Clight in every harness, under the compspecs of harness/x_roundtrip.c (no composites, so a body proved here moves to
   every law): pr_threshold, pr_adapt, pr_digit_char, pr_encode, pr_utf8, copy_bytes, same_bytes, same_uints.
  *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.harness.x_roundtrip.code.

#[export] Instance CS : compspecs. make_compspecs OpensslPunycode.harness.x_roundtrip.code.prog. Defined.
Local Open Scope logic.

Definition pr_threshold_spec :=
  DECLARE _pr_threshold
  WITH k: Z, bias: Z
  PRE [ tulong, tulong ]
    PROP (0 <= k <= Int64.max_unsigned; 0 <= bias <= Int64.max_unsigned - 26)
    PARAMS (Vlong (Int64.repr k); Vlong (Int64.repr bias))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (threshold k bias))) SEP ().

Definition pr_adapt_spec :=
  DECLARE _pr_adapt
  WITH delta: Z, numpoints: Z, firsttime: Z
  PRE [ tulong, tulong, tint ]
    PROP (0 <= delta <= maxint; 1 <= numpoints <= Int64.max_unsigned; Int.min_signed <= firsttime <= Int.max_signed)
    PARAMS (Vlong (Int64.repr delta); Vlong (Int64.repr numpoints); Vint (Int.repr firsttime))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (adapt delta numpoints (negb (firsttime =? 0))))) SEP ().

Definition pr_digit_char_spec :=
  DECLARE _pr_digit_char
  WITH d: Z
  PRE [ tulong ]
    PROP (0 <= d < 36) PARAMS (Vlong (Int64.repr d)) SEP ()
  POST [ tuchar ]
    PROP () RETURN (Vint (Int.repr (digit_char d))) SEP ().

(* pr_encode succeeds into ocap octets. *)
Definition encode_fits (cps: list Z) (ocap: Z) : bool :=
  match encode cps with Some e => Zlength e <=? ocap | None => false end.

(* The octets pr_encode leaves in o: the encoding then the rest of oinit on success, o' (anything) else. *)
Definition encode_out (cps: list Z) (ocap: Z) (oinit o': list val) : list val :=
  match encode cps with
  | Some e => if Zlength e <=? ocap then vb e ++ sublist (Zlength e) ocap oinit else o'
  | None => o'
  end.

Definition encode_len (cps: list Z) : Z :=
  match encode cps with Some e => Zlength e | None => 0 end.

Definition pr_encode_spec :=
  DECLARE _pr_encode
  WITH shc: share, pc: val, cps: list Z, sho: share, po: val, ocap: Z, oinit: list val, shl: share, pl: val
  PRE [ tptr tuint, tulong, tptr tuchar, tulong, tptr tulong ]
    PROP (readable_share shc; writable_share sho; writable_share shl;
          Forall (fun c => 0 <= c <= Int.max_unsigned) cps; Zlength cps <= Int.max_unsigned;
          0 <= ocap <= Int64.max_unsigned; Zlength oinit = ocap)
    PARAMS (pc; Vlong (Int64.repr (Zlength cps)); po; Vlong (Int64.repr ocap); pl)
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap oinit po; data_at_ shl tulong pl)
  POST [ tint ]
    EX o': list val,
    PROP (Zlength o' = ocap)
    RETURN (Vint (Int.repr (if encode_fits cps ocap then 1 else 0)))
    SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar ocap (encode_out cps ocap oinit o') po;
         if encode_fits cps ocap then data_at shl tulong (Vlong (Int64.repr (encode_len cps))) pl
         else data_at_ shl tulong pl).

(* pr_utf8(c, o): the UTF-8 octets of c at o (room for exactly them), their number. *)
Definition pr_utf8_spec :=
  DECLARE _pr_utf8
  WITH c: Z, sh: share, o: val, old: list val
  PRE [ tulong, tptr tuchar ]
    PROP (writable_share sh; 0 <= c <= Int64.max_unsigned; Zlength old = Zlength (utf8 c))
    PARAMS (Vlong (Int64.repr c); o)
    SEP (arr0 sh tuchar (Zlength (utf8 c)) old o)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Zlength (utf8 c))))
    SEP (arr0 sh tuchar (Zlength (utf8 c)) (vb (utf8 c)) o).

Definition copy_bytes_spec :=
  DECLARE _copy_bytes
  WITH shd: share, d: val, dold: list val, shs: share, s: val, l: list Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share shd; readable_share shs; bytes_ok l; Zlength dold = Zlength l;
          Zlength l <= Int64.max_unsigned)
    PARAMS (d; s; Vlong (Int64.repr (Zlength l)))
    SEP (arr0 shd tuchar (Zlength l) dold d; arr0 shs tuchar (Zlength l) (vb l) s)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (arr0 shd tuchar (Zlength l) (vb l) d; arr0 shs tuchar (Zlength l) (vb l) s).

Definition same_bytes_spec :=
  DECLARE _same_bytes
  WITH sha: share, a: val, la: list Z, shb: share, b: val, lb: list Z
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sha; readable_share shb; bytes_ok la; bytes_ok lb; Zlength la = Zlength lb;
          Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (arr0 sha tuchar (Zlength la) (vb la) a; arr0 shb tuchar (Zlength la) (vb lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec la lb then 1 else 0)))
    SEP (arr0 sha tuchar (Zlength la) (vb la) a; arr0 shb tuchar (Zlength la) (vb lb) b).

Definition same_uints_spec :=
  DECLARE _same_uints
  WITH sha: share, a: val, la: list Z, shb: share, b: val, lb: list Z
  PRE [ tptr tuint, tptr tuint, tulong ]
    PROP (readable_share sha; readable_share shb; Forall (fun x => 0 <= x <= Int.max_unsigned) la;
          Forall (fun x => 0 <= x <= Int.max_unsigned) lb; Zlength la = Zlength lb;
          Zlength la <= Int64.max_unsigned)
    PARAMS (a; b; Vlong (Int64.repr (Zlength la)))
    SEP (arr0 sha tuint (Zlength la) (vb la) a; arr0 shb tuint (Zlength la) (vb lb) b)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if list_eq_dec Z.eq_dec la lb then 1 else 0)))
    SEP (arr0 sha tuint (Zlength la) (vb la) a; arr0 shb tuint (Zlength la) (vb lb) b).

(* The callees of each body (Vprog: none of these functions reads a global). *)
Definition Vprog : varspecs := [].
Definition Gprog_encode : funspecs := [pr_threshold_spec; pr_adapt_spec; pr_digit_char_spec].
Definition Gprog_none : funspecs := [].
