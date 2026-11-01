(* The specifications of the WPACKET functions (patch/units/packet_ext.c = crypto/packet.c, verbatim) for a STATIC
   WPACKET (WPACKET_init_static_len with lenbytes = 0, the only kind ossl_a2ulabel makes): a buffer of cap > 0
   octets with a written prefix w, the record fields buf = NULL, staticbuf = the buffer, curr = written = |w|,
   maxsize = cap, subs = a zeroed block of CRYPTO_zalloc, endfirst = 0.
   Under the unit's compspecs (OpensslPunycode.units.Packet.CS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.libc.LibcSpec.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.units.Packet.
Require Import OpensslPunycode.packet.code.

#[export] Instance CS : compspecs := OpensslPunycode.units.Packet.CS.
Definition Vprog : varspecs. mk_varspecs OpensslPunycode.packet.code.prog. Defined.
Local Open Scope logic.

Definition t_pkt := Tstruct _wpacket_st noattr.
Definition t_sub := Tstruct _wpacket_sub noattr.

(* sizeof(WPACKET_SUB) = 40: the size CRYPTO_zalloc is asked for. *)
Definition sub_size : Z := 40.

(* The sub-packet record: a zeroed block of CRYPTO_zalloc (as CRYPTO_zalloc returns it). *)
Definition sub_rec (sub: val) : mpred := zblock sub_size sub.

(* The fields of a static WPACKET over buf with n octets written, capacity cap, record sub. *)
Definition pkt_rep (buf: val) (n cap: Z) (sub: val) : reptype t_pkt :=
  (nullval, (buf, (Vlong (Int64.repr n), (Vlong (Int64.repr n), (Vlong (Int64.repr cap), (sub, Vint Int.zero)))))).

(* A static WPACKET at pkt over the buffer buf of cap octets whose initial contents were init, with w written:
   the buffer holds w then the rest of init. *)
Definition wpkt (shp: share) (pkt: val) (shb: share) (buf: val) (cap: Z) (init: list val) (w: list Z) (sub: val)
  : mpred :=
  !! (0 < cap <= Int64.max_unsigned /\ Zlength init = cap /\ Zlength w <= cap /\ bytes_ok w) &&
  (data_at shp t_pkt (pkt_rep buf (Zlength w) cap sub) pkt *
   data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf *
   sub_rec sub).

(* A write of l fits (pr_put / WPACKET_memcpy): nothing to write, or room for it. *)
Definition put_ok (cap: Z) (w l: list Z) : bool := orb (Zlength l =? 0) (Zlength l <=? cap - Zlength w).

(* ---------------------------------------------------------------------- *)
(* The public functions (called by ossl_a2ulabel)                         *)
(* ---------------------------------------------------------------------- *)

(* WPACKET_init_static_len(pkt, buf, cap, 0).  cap = 0 fails before the allocation; else the record is allocated
   (CRYPTO_zalloc).  The test buf != NULL needs a valid pointer: when cap = 0 the caller gives the token of the
   malloc(0) block of buf (zero_tok), returned unchanged. *)
Definition WPACKET_init_static_len_spec :=
  DECLARE _WPACKET_init_static_len
  WITH gv: globals, shp: share, pkt: val, shb: share, buf: val, cap: Z, init: list val,
       fn: Z, zf: Z, live: Z, tk: type
  PRE [ tptr t_pkt, tptr tuchar, tulong, tulong ]
    PROP (writable_share shp; writable_share shb; 0 <= cap <= Int64.max_unsigned; Zlength init = cap;
          shim_bounds fn zf live; sizeof tk <= 0)
    PARAMS (pkt; buf; Vlong (Int64.repr cap); Vlong (Int64.repr 0)) GLOBALS (gv)
    SEP (zero_tok cap tk buf; data_at_ shp t_pkt pkt; data_at shb (tarray tuchar cap) init buf;
         shim_state gv fn zf live; mem_mgr gv)
  POST [ tint ]
    EX r: Z, EX sub: val, EX fn': Z, EX zf': Z, EX live': Z,
    PROP (if Z.eq_dec cap 0 then r = 0 /\ sub = nullval /\ fn' = fn /\ zf' = zf /\ live' = live
          else zalloc_outcome sub_size fn zf live sub fn' zf' live' /\ r = (if eq_dec sub nullval then 0 else 1))
    RETURN (Vint (Int.repr r))
    SEP (zero_tok cap tk buf; shim_state gv fn' zf' live'; mem_mgr gv;
         if Z.eq_dec r 0
         then (EX v: reptype t_pkt, data_at shp t_pkt v pkt) * data_at shb (tarray tuchar cap) init buf
         else wpkt shp pkt shb buf cap init [] sub).

(* WPACKET_memcpy(pkt, src, |l|): appends l when it fits (result 1), else changes nothing (result 0). *)
Definition WPACKET_memcpy_spec :=
  DECLARE _WPACKET_memcpy
  WITH shp: share, pkt: val, shb: share, buf: val, cap: Z, init: list val, w: list Z, sub: val,
       shs: share, src: val, l: list Z
  PRE [ tptr t_pkt, tptr tvoid, tulong ]
    PROP (writable_share shp; writable_share shb; readable_share shs; bytes_ok l;
          Zlength l <= Int64.max_unsigned)
    PARAMS (pkt; src; Vlong (Int64.repr (Zlength l)))
    SEP (wpkt shp pkt shb buf cap init w sub; arr0 shs tuchar (Zlength l) (vb l) src)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if put_ok cap w l then 1 else 0)))
    SEP (wpkt shp pkt shb buf cap init (fst (put cap (w, false) l)) sub; arr0 shs tuchar (Zlength l) (vb l) src).

(* WPACKET_put_bytes__(pkt, v, 1) (WPACKET_put_bytes_u8): appends the octet v when it fits. *)
Definition WPACKET_put_bytes___spec :=
  DECLARE _WPACKET_put_bytes__
  WITH shp: share, pkt: val, shb: share, buf: val, cap: Z, init: list val, w: list Z, sub: val, v: Z
  PRE [ tptr t_pkt, tulong, tulong ]
    PROP (writable_share shp; writable_share shb; 0 <= v <= Byte.max_unsigned)
    PARAMS (pkt; Vlong (Int64.repr v); Vlong (Int64.repr 1))
    SEP (wpkt shp pkt shb buf cap init w sub)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if put_ok cap w [v] then 1 else 0)))
    SEP (wpkt shp pkt shb buf cap init (fst (put cap (w, false) [v])) sub).

(* WPACKET_cleanup(pkt): the record is released (CRYPTO_free); the buffer keeps what was written. *)
Definition WPACKET_cleanup_spec :=
  DECLARE _WPACKET_cleanup
  WITH gv: globals, shp: share, pkt: val, shb: share, buf: val, cap: Z, init: list val, w: list Z, sub: val,
       fn: Z, zf: Z, live: Z
  PRE [ tptr t_pkt ]
    PROP (writable_share shp; shim_bounds fn zf live)
    PARAMS (pkt) GLOBALS (gv)
    SEP (wpkt shp pkt shb buf cap init w sub; shim_state gv fn zf live; mem_mgr gv)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP ((EX v: reptype t_pkt, data_at shp t_pkt v pkt);
         data_at shb (tarray tuchar cap) (vb w ++ sublist (Zlength w) cap init) buf;
         shim_state gv fn zf (live - 1); mem_mgr gv).

(* ---------------------------------------------------------------------- *)
(* The internal functions                                                 *)
(* ---------------------------------------------------------------------- *)

Definition maxmaxsize_model (lb: Z) : Z :=
  if orb (8 <=? lb) (lb =? 0) then Int64.max_unsigned else 2 ^ (lb * 8) - 1 + lb.

Definition maxmaxsize_spec :=
  DECLARE _maxmaxsize
  WITH lb: Z
  PRE [ tulong ]
    PROP (0 <= lb <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr lb))
    SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (maxmaxsize_model lb))) SEP ().

(* wpacket_intern_init_len(pkt, 0): curr = written = 0 and the record allocated (subs = NULL when it fails). *)
Definition wpacket_intern_init_len_spec :=
  DECLARE _wpacket_intern_init_len
  WITH gv: globals, shp: share, pkt: val, b: val, sb: val, c: val, wr: val, m: val, s: val, e: val,
       fn: Z, zf: Z, live: Z
  PRE [ tptr t_pkt, tulong ]
    PROP (writable_share shp; shim_bounds fn zf live)
    PARAMS (pkt; Vlong (Int64.repr 0)) GLOBALS (gv)
    SEP (data_at shp t_pkt (b, (sb, (c, (wr, (m, (s, e)))))) pkt; shim_state gv fn zf live; mem_mgr gv)
  POST [ tint ]
    EX sub: val, EX fn': Z, EX zf': Z, EX live': Z,
    PROP (zalloc_outcome sub_size fn zf live sub fn' zf' live')
    RETURN (Vint (Int.repr (if eq_dec sub nullval then 0 else 1)))
    SEP (data_at shp t_pkt (b, (sb, (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), (m, (sub, e)))))) pkt;
         shim_state gv fn' zf' live'; mem_mgr gv; if eq_dec sub nullval then emp else sub_rec sub).

(* WPACKET_get_curr: the current position staticbuf + curr (the static buffer is non-NULL: cap > 0). *)
Definition WPACKET_get_curr_spec :=
  DECLARE _WPACKET_get_curr
  WITH shp: share, pkt: val, shb: share, buf: val, cap: Z, v: list val, n: Z, wr: val, mx: val, sub: val
  PRE [ tptr t_pkt ]
    PROP (readable_share shp; readable_share shb; 0 < cap; 0 <= n <= Int64.max_unsigned)
    PARAMS (pkt)
    SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (wr, (mx, (sub, Vint Int.zero)))))) pkt;
         data_at shb (tarray tuchar cap) v buf)
  POST [ tptr tuchar ]
    PROP () RETURN (offset_val n buf)
    SEP (data_at shp t_pkt (nullval, (buf, (Vlong (Int64.repr n), (wr, (mx, (sub, Vint Int.zero)))))) pkt;
         data_at shb (tarray tuchar cap) v buf).

(* WPACKET_reserve_bytes(pkt, len, pa) (pa non-NULL): 1 and *pa = the current position when 0 < len <= room. *)
Definition WPACKET_reserve_bytes_spec :=
  DECLARE _WPACKET_reserve_bytes
  WITH shp: share, pkt: val, shb: share, buf: val, cap: Z, v: list val, n: Z, sub: val,
       len: Z, sha: share, pa: val
  PRE [ tptr t_pkt, tulong, tptr (tptr tuchar) ]
    PROP (writable_share shp; readable_share shb; writable_share sha; 0 < cap <= Int64.max_unsigned; 0 <= n <= cap;
          0 <= len <= Int64.max_unsigned)
    PARAMS (pkt; Vlong (Int64.repr len); pa)
    SEP (data_at shp t_pkt (pkt_rep buf n cap sub) pkt; data_at shb (tarray tuchar cap) v buf; sub_rec sub;
         data_at_ sha (tptr tuchar) pa)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if orb (len =? 0) (cap - n <? len) then 0 else 1)))
    SEP (data_at shp t_pkt (pkt_rep buf n cap sub) pkt; data_at shb (tarray tuchar cap) v buf; sub_rec sub;
         if orb (len =? 0) (cap - n <? len) then data_at_ sha (tptr tuchar) pa
         else data_at sha (tptr tuchar) (offset_val n buf) pa).

(* WPACKET_allocate_bytes: reserve, then written and curr advance by len. *)
Definition WPACKET_allocate_bytes_spec :=
  DECLARE _WPACKET_allocate_bytes
  WITH shp: share, pkt: val, shb: share, buf: val, cap: Z, v: list val, n: Z, sub: val,
       len: Z, sha: share, pa: val
  PRE [ tptr t_pkt, tulong, tptr (tptr tuchar) ]
    PROP (writable_share shp; readable_share shb; writable_share sha; 0 < cap <= Int64.max_unsigned; 0 <= n <= cap;
          0 <= len <= Int64.max_unsigned)
    PARAMS (pkt; Vlong (Int64.repr len); pa)
    SEP (data_at shp t_pkt (pkt_rep buf n cap sub) pkt; data_at shb (tarray tuchar cap) v buf; sub_rec sub;
         data_at_ sha (tptr tuchar) pa)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if orb (len =? 0) (cap - n <? len) then 0 else 1)))
    SEP (if orb (len =? 0) (cap - n <? len)
         then data_at shp t_pkt (pkt_rep buf n cap sub) pkt * data_at_ sha (tptr tuchar) pa
         else data_at shp t_pkt (pkt_rep buf (n + len) cap sub) pkt * data_at sha (tptr tuchar) (offset_val n buf) pa;
         data_at shb (tarray tuchar cap) v buf; sub_rec sub).

(* put_value(data, value, 1): the low octet of value at data; 1 when value fits in one octet. *)
Definition put_value_spec :=
  DECLARE _put_value
  WITH sh: share, data: val, old: val, value: Z
  PRE [ tptr tuchar, tulong, tulong ]
    PROP (writable_share sh; 0 <= value <= Int64.max_unsigned)
    PARAMS (data; Vlong (Int64.repr value); Vlong (Int64.repr 1))
    SEP (data_at sh tuchar old data)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if value <? 256 then 1 else 0)))
    SEP (data_at sh tuchar (Vint (Int.repr (value mod 256))) data).

(* The callees of each body. *)
Definition Gprog_init_static_len : funspecs := [maxmaxsize_spec; wpacket_intern_init_len_spec].
Definition Gprog_intern_init_len : funspecs := [CRYPTO_zalloc_spec].
Definition Gprog_memcpy : funspecs := [WPACKET_allocate_bytes_spec; OpensslPunycode.proof.libc.LibcSpec.memcpy_spec].
Definition Gprog_put_bytes : funspecs := [WPACKET_allocate_bytes_spec; put_value_spec].
Definition Gprog_allocate_bytes : funspecs := [WPACKET_reserve_bytes_spec].
Definition Gprog_reserve_bytes : funspecs := [WPACKET_get_curr_spec].
Definition Gprog_cleanup : funspecs := [CRYPTO_free_spec].
Definition Gprog_none : funspecs := [].
