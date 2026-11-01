(* The specifications of crypto/punycode.c (patched): ossl_punycode_decode and ossl_a2ulabel (public), adapt,
   is_basic, digit_decoded, codepoint2utf8 (static).  Each is exactly the model (OpensslPunycode.proof.model.Model).
   Under the unit's compspecs (OpensslPunycode.units.Punycode.CS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require OpensslPunycode.units.Punycode.
Require Import OpensslPunycode.punycode.code.

#[export] Instance CS : compspecs := OpensslPunycode.units.Punycode.CS.
Definition Vprog : varspecs. mk_varspecs OpensslPunycode.punycode.code.prog. Defined.
Local Open Scope logic.

(* The static constants of punycode.c (read-only globals). *)
Definition puny_consts (gv: globals) : mpred :=
  data_at Ers tuint (Vint (Int.repr 36)) (gv _base) *
  data_at Ers tuint (Vint (Int.repr 1)) (gv _tmin) *
  data_at Ers tuint (Vint (Int.repr 26)) (gv _tmax) *
  data_at Ers tuint (Vint (Int.repr 38)) (gv _skew) *
  data_at Ers tuint (Vint (Int.repr 700)) (gv _damp) *
  data_at Ers tuint (Vint (Int.repr 72)) (gv _initial_bias) *
  data_at Ers tuint (Vint (Int.repr 128)) (gv _initial_n) *
  data_at Ers tuint (Vint (Int.repr (-1))) (gv _maxint) *
  data_at Ers tschar (Vint (Int.repr 45)) (gv _delimiter).

(* The string literal "xn--" of ossl_a2ulabel. *)
Definition xn_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 5) (vb [120; 110; 45; 45; 0]) (gv ___stringlit_punycode_1).

(* ---------------------------------------------------------------------- *)
(* ossl_punycode_decode                                                   *)
(* ---------------------------------------------------------------------- *)

(* The result, the array and *pout_length after ossl_punycode_decode(inp, |inp|, array with init, &cap):
   inputs of UINT_MAX octets or more are rejected; else exactly the model: on success the code points then the
   rest of init, on failure the output so far then the rest of init (the length unchanged). *)
Definition decode_result (inp: list Z) (cap: Z) (init: list val) : Z * list val * Z :=
  if Int.max_unsigned <=? Zlength inp then (0, init, cap) else
  let (ok, out) := decode inp cap in
  (if ok then 1 else 0, vb out ++ sublist (Zlength out) cap init, if ok then Zlength out else cap).

Definition ossl_punycode_decode_spec :=
  DECLARE _ossl_punycode_decode
  WITH gv: globals, shi: share, pe: val, inp: list Z, sho: share, pd: val, cap: Z, init: list val,
       shl: share, pl: val
  PRE [ tptr tschar, tulong, tptr tuint, tptr tuint ]
    PROP (readable_share shi; writable_share sho; writable_share shl; bytes_ok inp;
          Zlength inp <= Int64.max_unsigned; 0 <= cap <= Int.max_unsigned; Zlength init = cap)
    PARAMS (pe; Vlong (Int64.repr (Zlength inp)); pd; pl) GLOBALS (gv)
    SEP (puny_consts gv; arr0 shi tuchar (Zlength inp) (vb inp) pe; arr0 sho tuint cap init pd;
         data_at shl tuint (Vint (Int.repr cap)) pl)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (fst (fst (decode_result inp cap init)))))
    SEP (puny_consts gv; arr0 shi tuchar (Zlength inp) (vb inp) pe;
         arr0 sho tuint cap (snd (fst (decode_result inp cap init))) pd;
         data_at shl tuint (Vint (Int.repr (snd (decode_result inp cap init)))) pl).

Definition adapt_spec :=
  DECLARE _adapt
  WITH gv: globals, delta: Z, numpoints: Z, firsttime: Z
  PRE [ tuint, tuint, tuint ]
    PROP (0 <= delta <= Int.max_unsigned; 1 <= numpoints <= Int.max_unsigned;
          0 <= firsttime <= Int.max_unsigned)
    PARAMS (Vint (Int.repr delta); Vint (Int.repr numpoints); Vint (Int.repr firsttime)) GLOBALS (gv)
    SEP (puny_consts gv)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (adapt delta numpoints (negb (firsttime =? 0))))) SEP (puny_consts gv).

Definition is_basic_spec :=
  DECLARE _is_basic
  WITH a: Z
  PRE [ tuint ]
    PROP (0 <= a <= Int.max_unsigned) PARAMS (Vint (Int.repr a)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if a <? 128 then 1 else 0))) SEP ().

Definition digit_decoded_spec :=
  DECLARE _digit_decoded
  WITH a: Z
  PRE [ tuchar ]
    PROP (0 <= a <= Byte.max_unsigned) PARAMS (Vint (Int.repr a)) SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if digit_value a =? 36 then -1 else digit_value a))) SEP ().

(* ---------------------------------------------------------------------- *)
(* ossl_a2ulabel                                                          *)
(* ---------------------------------------------------------------------- *)

(* codepoint2utf8(out, c) into the 6-octet seed: the UTF-8 octets of c first, their number as the result. *)
Definition codepoint2utf8_spec :=
  DECLARE _codepoint2utf8
  WITH sh: share, p: val, old: list val, c: Z
  PRE [ tptr tuchar, tulong ]
    PROP (writable_share sh; Zlength old = 6; 0 <= c <= Int64.max_unsigned)
    PARAMS (p; Vlong (Int64.repr c))
    SEP (data_at sh (tarray tuchar 6) old p)
  POST [ tint ]
    EX new: list val,
    PROP (Zlength new = 6; sublist 0 (Zlength (utf8 c)) new = vb (utf8 c))
    RETURN (Vint (Int.repr (Zlength (utf8 c))))
    SEP (data_at sh (tarray tuchar 6) new p).

(* The outcome of ossl_a2ulabel(s, out, cap) with the knob fn: (result, knob', failure flag', buffer'), given
   whether malloc failed (mf) when it was called.  out = NULL or cap = 0: -1, nothing done; the knob set: the
   allocation fails (-1); malloc failed: -1; else the model (Model.a2ulabel): the octets written at the start of
   the buffer, every other octet unchanged. *)
Definition a2u_outcome (out: val) (cap: Z) (s: list Z) (init: list val) (fn zf: Z) (mf: bool)
  : Z * Z * Z * list val :=
  if Val.eq out nullval then (-1, fn, zf, init)
  else if cap =? 0 then (-1, fn, zf, init)
  else if negb (fn =? 0) then (-1, 0, 1, init)
  else if mf then (-1, 0, 1, init)
  else let (r, w) := a2ulabel s cap in (r, 0, zf, vb w ++ sublist (Zlength w) cap init).

(* The output buffer: none when out = NULL.  A zero-size buffer comes with the token of its malloc(0) block
   (zero_tok: the test out != NULL needs a valid pointer). *)
Definition out_buf (sho: share) (out: val) (cap: Z) (v: list val) (tk: type) : mpred :=
  if Val.eq out nullval then emp else data_at sho (tarray tuchar cap) v out * zero_tok cap tk out.

Definition ossl_a2ulabel_spec :=
  DECLARE _ossl_a2ulabel
  WITH gv: globals, shi: share, pin: val, s: list Z, sho: share, out: val, cap: Z, init: list val, tk: type,
       fn: Z, zf: Z, live: Z
  PRE [ tptr tschar, tptr tschar, tulong ]
    PROP (readable_share shi; writable_share sho; str_ok s; 0 <= cap <= Int64.max_unsigned;
          out = nullval \/ Zlength init = cap; sizeof tk <= 0; shim_bounds fn zf live;
          live + 1 < Int64.max_signed)
    PARAMS (pin; out; Vlong (Int64.repr cap)) GLOBALS (gv)
    SEP (puny_consts gv; xn_lit gv; shim_state gv fn zf live; mem_mgr gv; cstr shi s pin;
         out_buf sho out cap init tk)
  POST [ tint ]
    EX mf: bool,
    PROP ()
    RETURN (Vint (Int.repr (fst (fst (fst (a2u_outcome out cap s init fn zf mf))))))
    SEP (puny_consts gv; xn_lit gv;
         shim_state gv (snd (fst (fst (a2u_outcome out cap s init fn zf mf))))
                       (snd (fst (a2u_outcome out cap s init fn zf mf))) live;
         mem_mgr gv; cstr shi s pin; out_buf sho out cap (snd (a2u_outcome out cap s init fn zf mf)) tk).

(* The callees of each body. *)
Definition Gprog_decode : funspecs := [adapt_spec; is_basic_spec; digit_decoded_spec].
Definition Gprog_a2ulabel : funspecs :=
  [strchr_spec; strlen_spec; OPENSSL_strncasecmp_spec;
   OpensslPunycode.proof.packet.PacketSpec.WPACKET_init_static_len_spec;
   OpensslPunycode.proof.packet.PacketSpec.WPACKET_memcpy_spec;
   OpensslPunycode.proof.packet.PacketSpec.WPACKET_put_bytes___spec;
   OpensslPunycode.proof.packet.PacketSpec.WPACKET_cleanup_spec;
   ossl_punycode_decode_spec; codepoint2utf8_spec].
Definition Gprog_none : funspecs := [].
