(* ossl_a2ulabel, the ACE branch (s_ace) in pieces: its sub-statements and the assertions between them.
   s_ace = bufsize = 512; (DEC; DTEST); ((i = 0; for (; ITEST; INCR) CPBODY); FIN)
   CPBODY = CPA (t'13 = buf[i]; t'7 = codepoint2utf8(seed, t'13); utfsize = t'7);
            CPB (if (utfsize == 0) { result = -1; break; });
            CPC (t'8 = WPACKET_memcpy(&pkt, seed, utfsize)); CPD (if (!t'8) result = 0). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.proof.punycode.A2uDefs.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.

Definition s_bs : statement := ltac:(
  let b := eval hnf in s_ace in match b with Ssequence ?x _ => exact x end).
Definition s_dec : statement := ltac:(
  let b := eval hnf in s_ace in match b with Ssequence _ (Ssequence (Ssequence ?x _) _) => exact x end).
Definition s_dtest : statement := ltac:(
  let b := eval hnf in s_ace in match b with Ssequence _ (Ssequence (Ssequence _ ?x) _) => exact x end).
Definition s_i0 : statement := ltac:(
  let b := eval hnf in s_ace in
  match b with Ssequence _ (Ssequence _ (Ssequence (Ssequence ?x _) _)) => exact x end).
Definition s_itest : statement := ltac:(
  let b := eval hnf in s_ace in
  match b with Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop (Ssequence ?x _) _)) _)) => exact x end).
Definition s_incr : statement := ltac:(
  let b := eval hnf in s_ace in
  match b with Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?x)) _)) => exact x end).
Definition s_fin : statement := ltac:(
  let b := eval hnf in s_ace in match b with Ssequence _ (Ssequence _ (Ssequence _ ?x)) => exact x end).
Definition s_cpa : statement := ltac:(
  let b := eval hnf in s_cpbody in match b with Ssequence ?x _ => exact x end).
Definition s_cpb : statement := ltac:(
  let b := eval hnf in s_cpbody in match b with Ssequence _ (Ssequence ?x _) => exact x end).
Definition s_cpc : statement := ltac:(
  let b := eval hnf in s_cpbody in match b with Ssequence _ (Ssequence _ (Ssequence ?x _)) => exact x end).
Definition s_cpd : statement := ltac:(
  let b := eval hnf in s_cpbody in match b with Ssequence _ (Ssequence _ (Ssequence _ ?x)) => exact x end).

Lemma s_ace_eq: s_ace = Ssequence s_bs (Ssequence (Ssequence s_dec s_dtest)
  (Ssequence (Ssequence s_i0 (Sloop (Ssequence s_itest s_cpbody) s_incr)) s_fin)).
Proof. reflexivity. Qed.

Lemma s_cpbody_eq: s_cpbody = Ssequence s_cpa (Ssequence s_cpb (Ssequence s_cpc s_cpd)).
Proof. reflexivity. Qed.

Section Asserts.
Variables (gv: globals) (shi: share) (pin: val) (s: list Z) (sho: share) (out: val) (cap: Z) (init: list val)
  (tk: type) (zf live: Z) (sub: val) (vbuf vpkt vbs vseed: val).

(* After DEC/DTEST when the label decoded into cps (bufsize = |cps|, buf = cps then the old values bv). *)
Definition ace_dec (st: Z) (w: list Z) (sh: bool) (cps: list Z) (bv: list val) : environ -> mpred :=
  PROP ()
  LOCAL (temp _tmpptr (tmp_at pin s st); temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame gv out cap tk zf live; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr shi pin s st;
       data_at Tsh (tarray tuint 512) (vb cps ++ sublist (Zlength cps) 512 bv) vbuf;
       data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vbs;
       EX sv: list val, !! (Zlength sv = 6) && data_at Tsh (tarray tuchar 6) sv vseed).

(* After CPA at i (the sink (w, sh)): the UTF-8 form of cps[i] at the start of the seed, its length in utfsize. *)
Definition cp_a (st: Z) (w0: list Z) (sh0: bool) (cps: list Z) (bv: list val) (i: Z) (w: list Z) (sh: bool)
  : environ -> mpred :=
  EX new: list val,
  PROP (0 <= i < Zlength cps;
        put_utf8s cap (w0, sh0) cps = put_utf8s cap (w, sh) (sublist i (Zlength cps) cps);
        Zlength new = 6; sublist 0 (Zlength (utf8 (Znth i cps))) new = vb (utf8 (Znth i cps)))
  LOCAL (temp _utfsize (Vlong (Int64.repr (Zlength (utf8 (Znth i cps)))));
         temp _i (Vint (Int.repr i)); temp _tmpptr (tmp_at pin s st); temp _inptr (offset_val st pin);
         temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame gv out cap tk zf live; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr shi pin s st;
       data_at Tsh (tarray tuint 512) (vb cps ++ sublist (Zlength cps) 512 bv) vbuf;
       data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vbs;
       data_at Tsh (tarray tuchar 6) new vseed).

(* After CPB (cps[i] has a UTF-8 form). *)
Definition cp_b (st: Z) (w0: list Z) (sh0: bool) (cps: list Z) (bv: list val) (i: Z) (w: list Z) (sh: bool)
  : environ -> mpred :=
  !! (0 < Zlength (utf8 (Znth i cps))) && cp_a st w0 sh0 cps bv i w sh.

(* After CPBODY at i: the loop increment is next. *)
Definition cp_mid (st: Z) (w0: list Z) (sh0: bool) (cps: list Z) (bv: list val) (i: Z) : environ -> mpred :=
  EX w: list Z, EX sh: bool,
  PROP (0 <= i < Zlength cps;
        put_utf8s cap (w0, sh0) cps = put_utf8s cap (w, sh) (sublist (i + 1) (Zlength cps) cps))
  LOCAL (temp _i (Vint (Int.repr i)); temp _tmpptr (tmp_at pin s st); temp _inptr (offset_val st pin);
         temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame gv out cap tk zf live; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr shi pin s st;
       data_at Tsh (tarray tuint 512) (vb cps ++ sublist (Zlength cps) 512 bv) vbuf;
       data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vbs;
       EX sv: list val, !! (Zlength sv = 6) && data_at Tsh (tarray tuchar 6) sv vseed).

End Asserts.

(* The facts on the decoded code points the code-point loop needs. *)
Definition cps_ok (cps: list Z) (bv: list val) : Prop :=
  Forall (fun c => 0 <= c <= maxint) cps /\ Zlength cps <= 512 /\ Zlength bv = 512.

(* The type context of ossl_a2ulabel's body. *)
Notation DeltaA := (func_tycontext f_ossl_a2ulabel Vprog Gprog_a2ulabel nil) (only parsing).
