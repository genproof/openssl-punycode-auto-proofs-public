(* The specifications of the shim unit (patch/shim/ossl_shim.c): CRYPTO_zalloc / CRYPTO_free with the knob and the
   counters, strlen, strchr, OPENSSL_strncasecmp (with shim_tolower), and the trap BUF_MEM_grow (precondition
   False: WPACKET_reserve_bytes calls it only for a growable WPACKET).  strncmp is reached by no law.
   Under the unit's compspecs (OpensslPunycode.units.Shim.CS). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.libc.LibcSpec.
Require OpensslPunycode.units.Shim.
Require Import OpensslPunycode.shim.code.

#[export] Instance CS : compspecs := OpensslPunycode.units.Shim.CS.
Definition Vprog : varspecs. mk_varspecs OpensslPunycode.shim.code.prog. Defined.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The knob and the counters                                              *)
(* ---------------------------------------------------------------------- *)

(* ossl_shim_fail_next = fn, ossl_shim_zalloc_failed = zf, ossl_shim_live = live. *)
Definition shim_state (gv: globals) (fn zf live: Z) : mpred :=
  data_at Ews tint (Vint (Int.repr fn)) (gv _ossl_shim_fail_next) *
  data_at Ews tint (Vint (Int.repr zf)) (gv _ossl_shim_zalloc_failed) *
  data_at Ews tlong (Vlong (Int64.repr live)) (gv _ossl_shim_live).

Definition shim_bounds (fn zf live: Z) : Prop :=
  Int.min_signed <= fn <= Int.max_signed /\ Int.min_signed <= zf <= Int.max_signed /\
  Int64.min_signed < live < Int64.max_signed.

(* A block of CRYPTO_zalloc: n zero octets (and the token free needs). *)
Definition zblock (n: Z) (p: val) : mpred :=
  malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) (Zrepeat (Vint Int.zero) n) p.

(* The validity of a pointer to a zero-size buffer, from its malloc(0) block's token (sizeof tk <= 0: VST's
   malloc_token_valid_pointer); nothing when the buffer is not empty (then its data_at gives it). *)
Definition zero_tok (cap: Z) (tk: type) (p: val) : mpred :=
  if Z.eq_dec cap 0 then malloc_token Ews tk p else emp.

(* What CRYPTO_zalloc(num) does to (p, fn, zf, live): num = 0 gives NULL (and sets the failure flag); else the
   knob makes it fail once; else malloc may fail; a block returned counts as live. *)
Definition zalloc_outcome (num fn zf live: Z) (p: val) (fn' zf' live': Z) : Prop :=
  if Z.eq_dec num 0 then p = nullval /\ fn' = fn /\ zf' = 1 /\ live' = live
  else if Z.eq_dec fn 0 then
    fn' = 0 /\ ((p = nullval /\ zf' = 1 /\ live' = live) \/ (p <> nullval /\ zf' = zf /\ live' = live + 1))
  else p = nullval /\ fn' = 0 /\ zf' = 1 /\ live' = live.

Definition CRYPTO_zalloc_spec :=
  DECLARE _CRYPTO_zalloc
  WITH gv: globals, num: Z, file: val, line: Z, fn: Z, zf: Z, live: Z
  PRE [ tulong, tptr tschar, tint ]
    PROP (0 <= num <= Ptrofs.max_unsigned; Int.min_signed <= line <= Int.max_signed; shim_bounds fn zf live)
    PARAMS (Vlong (Int64.repr num); file; Vint (Int.repr line)) GLOBALS (gv)
    SEP (shim_state gv fn zf live; mem_mgr gv)
  POST [ tptr tvoid ]
    EX p: val, EX fn': Z, EX zf': Z, EX live': Z,
    PROP (zalloc_outcome num fn zf live p fn' zf' live')
    RETURN (p)
    SEP (shim_state gv fn' zf' live'; mem_mgr gv; if eq_dec p nullval then emp else zblock num p).

(* CRYPTO_free(p): a block of n octets (any contents) is released; free(NULL) is nothing. *)
Definition CRYPTO_free_spec :=
  DECLARE _CRYPTO_free
  WITH gv: globals, p: val, n: Z, file: val, line: Z, fn: Z, zf: Z, live: Z
  PRE [ tptr tvoid, tptr tschar, tint ]
    PROP (0 <= n <= Ptrofs.max_unsigned; Int.min_signed <= line <= Int.max_signed; shim_bounds fn zf live)
    PARAMS (p; file; Vint (Int.repr line)) GLOBALS (gv)
    SEP (shim_state gv fn zf live; mem_mgr gv;
         if eq_dec p nullval then emp else malloc_token Ews (tarray tuchar n) p * data_at_ Ews (tarray tuchar n) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (shim_state gv fn zf (if eq_dec p nullval then live else live - 1); mem_mgr gv).

(* ---------------------------------------------------------------------- *)
(* Strings                                                                *)
(* ---------------------------------------------------------------------- *)

(* A string: octets 1..255, then the NUL, in an array of exactly that size. *)
Definition str_ok (s: list Z) : Prop := Forall (fun b => 1 <= b <= Byte.max_unsigned) s.

Definition cstr (sh: share) (s: list Z) (p: val) : mpred :=
  data_at sh (tarray tuchar (Zlength s + 1)) (vb (s ++ [0])) p.

Definition strlen_spec :=
  DECLARE _strlen
  WITH sh: share, s: list Z, p: val
  PRE [ tptr tschar ]
    PROP (readable_share sh; str_ok s)
    PARAMS (p)
    SEP (cstr sh s p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (Zlength s)))
    SEP (cstr sh s p).

(* The index of the first c in l, Zlength l when there is none. *)
Fixpoint index_of (c: Z) (l: list Z) : Z :=
  match l with
  | [] => 0
  | x :: l' => if x =? c then 0 else 1 + index_of c l'
  end.

(* strchr(s, c) for an octet c <> 0 (as the int argument): the first occurrence, NULL when there is none. *)
Definition strchr_spec :=
  DECLARE _strchr
  WITH sh: share, s: list Z, p: val, c: Z
  PRE [ tptr tschar, tint ]
    PROP (readable_share sh; str_ok s; 1 <= c <= Byte.max_unsigned)
    PARAMS (p; Vint (Int.repr c))
    SEP (cstr sh s p)
  POST [ tptr tschar ]
    PROP ()
    RETURN (if index_of c s <? Zlength s then offset_val (index_of c s) p else nullval)
    SEP (cstr sh s p).

(* ossl_tolower on an ASCII platform, on the int value of a (signed) char. *)
Definition tolower (c: Z) : Z := if andb (65 <=? c) (c <=? 90) then c + 32 else c.

(* OPENSSL_strncasecmp on the char values (sbyte) of the arrays l1, l2 (each a string with its NUL): the first
   nonzero difference of the lowercased chars within n, 0 at a common NUL or after n chars. *)
Fixpoint ncasecmp (l1 l2: list Z) (n: nat) : Z :=
  match n, l1, l2 with
  | S n', c1 :: r1, c2 :: r2 =>
    let t := tolower (sbyte c1) - tolower (sbyte c2) in
    if negb (t =? 0) then t else if c1 =? 0 then 0 else ncasecmp r1 r2 n'
  | _, _, _ => 0
  end.

Definition shim_tolower_spec :=
  DECLARE _shim_tolower
  WITH c: Z
  PRE [ tint ]
    PROP (Int.min_signed <= c <= Int.max_signed)
    PARAMS (Vint (Int.repr c))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (tolower c))) SEP ().

Definition OPENSSL_strncasecmp_spec :=
  DECLARE _OPENSSL_strncasecmp
  WITH sh1: share, s1: list Z, p1: val, sh2: share, s2: list Z, p2: val, n: Z
  PRE [ tptr tschar, tptr tschar, tulong ]
    PROP (readable_share sh1; readable_share sh2; str_ok s1; str_ok s2; 0 <= n <= Int64.max_unsigned)
    PARAMS (p1; p2; Vlong (Int64.repr n))
    SEP (cstr sh1 s1 p1; cstr sh2 s2 p2)
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (ncasecmp (s1 ++ [0]) (s2 ++ [0]) (Z.to_nat n))))
    SEP (cstr sh1 s1 p1; cstr sh2 s2 p2).

(* The trap: never called (a static WPACKET has no BUF_MEM). *)
Definition BUF_MEM_grow_spec :=
  DECLARE _BUF_MEM_grow
  WITH str: val, len: Z
  PRE [ tptr (Tstruct _buf_mem_st noattr), tulong ]
    PROP (False) PARAMS (str; Vlong (Int64.repr len)) SEP ()
  POST [ tulong ]
    PROP () RETURN (Vlong Int64.zero) SEP ().

(* The callees of each body. *)
Definition Gprog_zalloc : funspecs :=
  [(_quickproof_malloc, @malloc_spec' CS); OpensslPunycode.proof.libc.LibcSpec.memset_spec].
Definition Gprog_free : funspecs := [(_quickproof_free, @free_spec' CS)].
Definition Gprog_strncasecmp : funspecs := [shim_tolower_spec].
Definition Gprog_none : funspecs := [].
