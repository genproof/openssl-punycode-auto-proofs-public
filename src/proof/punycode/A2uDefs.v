(* The pieces of the proof of ossl_a2ulabel (crypto/punycode.c, patched): its sub-statements, the assertions between
   them (the loop invariants), the function's return assertion.  Under Punycode.CS.  The body is proved in pieces
   (one lemma per file, A2u*.v) assembled in BodyA2uMain.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.proof.punycode.PunySpec.
Require Import OpensslPunycode.proof.punycode.A2uModel.
Require Import OpensslPunycode.proof.punycode.A2uLemmas.
Require Import OpensslPunycode.proof.punycode.A2uVst.
Require Import OpensslPunycode.punycode.code.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The statements                                                         *)
(* ---------------------------------------------------------------------- *)

Ltac a2u_body := let b := eval hnf in (fn_body f_ossl_a2ulabel) in exact b.
Definition a2u_body_stmt : statement := ltac:(a2u_body).

(* if (out == NULL) return -1 *)
Definition s_ifout : statement := ltac:(
  let b := eval hnf in (fn_body f_ossl_a2ulabel) in
  match b with Ssequence _ (Ssequence _ (Ssequence ?x _)) => exact x end).
(* WPACKET_init_static_len and its test *)
Definition s_init : statement := ltac:(
  let b := eval hnf in (fn_body f_ossl_a2ulabel) in
  match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence ?x _))) => exact x end).
(* the body of the label loop *)
Definition s_label : statement := ltac:(
  let b := eval hnf in (fn_body f_ossl_a2ulabel) in
  match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Sloop ?x Sskip) _)))) => exact x end).
(* after the label loop: the final NUL, the cleanup, the return *)
Definition s_post : statement := ltac:(
  let b := eval hnf in (fn_body f_ossl_a2ulabel) in
  match b with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence (Sloop _ Sskip) ?x)))) => exact x end).
(* the parts of the label body: Ssequence Sskip (Ssequence FIND (Ssequence DELTA (Ssequence (Ssequence CMP IF) TAIL))) *)
Definition s_find : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence ?x _) => exact x end).
Definition s_delta : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence _ (Ssequence ?x _)) => exact x end).
Definition s_cmp : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence _ (Ssequence _ (Ssequence (Ssequence ?x _) _))) => exact x end).
Definition s_nonace : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ ?x _)) _))) =>
    exact x end).
Definition s_ace : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ _ ?x)) _))) =>
    exact x end).
Definition s_tail : statement := ltac:(
  let b := eval hnf in s_label in
  match b with Ssequence Sskip (Ssequence _ (Ssequence _ (Ssequence _ ?x))) => exact x end).
(* the ACE branch: Ssequence (bufsize = 512) (Ssequence (Ssequence DECODE TEST) (Ssequence (Ssequence (i = 0) (Sloop
   (Ssequence ITEST CPBODY) INCR)) (if (result == -1) break))) *)
Definition s_cpbody : statement := ltac:(
  let b := eval hnf in s_ace in
  match b with context [Sloop (Ssequence _ ?x) _] => exact x end).

Lemma s_label_eq: s_label = Ssequence Sskip (Ssequence s_find (Ssequence s_delta (Ssequence (Ssequence s_cmp
  (Sifthenelse (Eunop Onotbool (Ebinop Oeq (Etempvar _t'9 tint) (Econst_int (Int.repr 0) tint) tint) tint)
     s_nonace s_ace)) s_tail))).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The model side                                                         *)
(* ---------------------------------------------------------------------- *)

(* After the first label of rest was converted with the sink now k: the rest of the conversion. *)
Definition a2u_cont (cap: Z) (k: sink) (rest: list Z) : Z * sink :=
  if index_of 46 rest <? Zlength rest
  then a2u_labels cap (put cap k [46]) (labels (sublist (index_of 46 rest + 1) (Zlength rest) rest))
  else let k2 := put cap k [0] in (if snd k2 then 0 else 1, k2).

(* The state at the exit of the label loop: result r with the sink (w, sh): -1 and the conversion's end, or every
   label converted and the final NUL still to write. *)
Definition a2u_end (cap: Z) (s: list Z) (w: list Z) (sh: bool) (r: Z) : Prop :=
  (r = -1 /\ a2u_labels cap ([], false) (labels s) = (-1, (w, sh))) \/
  (r = (if sh then 0 else 1) /\ a2u_labels cap ([], false) (labels s) = a2u_cont cap (w, sh) []).

(* The decoded label at the start of rest (when it is an A-label). *)
Definition ace_in (rest: list Z) : list Z := sublist 4 (index_of 46 rest) rest.

(* The result variable for a sink *)
Definition res_of (sh: bool) : Z := if sh then 0 else 1.

(* ---------------------------------------------------------------------- *)
(* The assertions                                                         *)
(* ---------------------------------------------------------------------- *)

Section Asserts.
Variables (gv: globals) (shi: share) (pin: val) (s: list Z) (sho: share) (out: val) (cap: Z) (init: list val)
  (tk: type) (fn zf live: Z) (sub: val) (vbuf vpkt vbs vseed: val).

(* The function's postcondition and return assertion (as start_function gives them). *)
Definition a2u_R : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
      (EX mf : bool,
       PROP ( )
       RETURN (Vint (Int.repr (fst (fst (fst (a2u_outcome out cap s init fn zf mf))))))
       SEP (puny_consts gv; xn_lit gv;
            shim_state gv (snd (fst (fst (a2u_outcome out cap s init fn zf mf))))
              (snd (fst (a2u_outcome out cap s init fn zf mf))) live;
            mem_mgr gv; cstr shi s pin;
            out_buf sho out cap (snd (a2u_outcome out cap s init fn zf mf)) tk))%argsassert)
    (stackframe_of f_ossl_a2ulabel).

(* What the loop does not touch (fn = 0, the record allocated: live + 1). *)
Definition a2u_frame : mpred :=
  puny_consts gv * xn_lit gv * shim_state gv 0 zf (live + 1) * mem_mgr gv * zero_tok cap tk out.

(* The local arrays buf, bufsize, seed with any contents. *)
Definition scratch : mpred :=
  EX bv: list val, EX bsv: val, EX sv: list val,
  !! (Zlength bv = 512 /\ Zlength sv = 6) &&
  (data_at Tsh (tarray tuint 512) bv vbuf * data_at Tsh tuint bsv vbs * data_at Tsh (tarray tuchar 6) sv vseed).

(* The input string, cut at st (inptr = pin + st). *)
Definition instr (st: Z) : mpred :=
  piece shi (s ++ [0]) 0 st pin * piece shi (s ++ [0]) st (Zlength s + 1) pin.

(* The remaining string at st. *)
Definition rest_at (st: Z) : list Z := sublist st (Zlength s) s.

(* tmpptr = strchr(inptr, '.') *)
Definition tmp_at (st: Z) : val :=
  if index_of 46 (rest_at st) <? Zlength (rest_at st) then offset_val (st + index_of 46 (rest_at st)) pin
  else nullval.

(* The invariant of the label loop: inptr at st, the sink (w, sh), and the rest of the conversion is that of the
   labels of the remaining string. *)
Definition a2u_inv : environ -> mpred :=
  EX st: Z, EX w: list Z, EX sh: bool,
  PROP (0 <= st <= Zlength s;
        a2u_labels cap ([], false) (labels s) = a2u_labels cap (w, sh) (labels (rest_at st)))
  LOCAL (temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st; scratch).

(* The exit of the label loop (break). *)
Definition a2u_brk : environ -> mpred :=
  EX st: Z, EX w: list Z, EX sh: bool, EX r: Z,
  PROP (0 <= st <= Zlength s; a2u_end cap s w sh r)
  LOCAL (temp _result (Vint (Int.repr r));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st; scratch).

(* The return assertion of the label loop's body. *)
Definition a2u_loopR (R: ret_assert) : ret_assert := loop1_ret_assert a2u_inv (overridePost a2u_brk R).

(* After FIND, DELTA, CMP: tmpptr, delta, and t'9 the result of OPENSSL_strncasecmp(inptr, "xn--", 4). *)
Definition a2u_head (st: Z) (w: list Z) (sh: bool) (c9: Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'9 (Vint (Int.repr c9)); temp _tmpptr (tmp_at st);
         temp _delta (Vlong (Int64.repr (index_of 46 (rest_at st))));
         temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st; scratch).

(* After the first label of the remaining string at st was converted (the sink now (w, sh)). *)
Definition a2u_lab (st: Z) : environ -> mpred :=
  EX w: list Z, EX sh: bool,
  PROP (a2u_labels cap ([], false) (labels s) = a2u_cont cap (w, sh) (rest_at st))
  LOCAL (temp _tmpptr (tmp_at st); temp _inptr (offset_val st pin); temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st; scratch).

(* The loop over the code points cps (decoded into buf, n = |cps| in bufsize) of the A-label at st, started with the
   sink (w0, sh0): at i with the sink (w, sh). *)
Definition cp_inv (st: Z) (w0: list Z) (sh0: bool) (cps: list Z) (bv: list val) (i: Z) (w: list Z) (sh: bool)
  : environ -> mpred :=
  PROP (0 <= i <= Zlength cps;
        put_utf8s cap (w0, sh0) cps = put_utf8s cap (w, sh) (sublist i (Zlength cps) cps))
  LOCAL (temp _i (Vint (Int.repr i)); temp _tmpptr (tmp_at st); temp _inptr (offset_val st pin);
         temp _result (Vint (Int.repr (res_of sh)));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st;
       data_at Tsh (tarray tuint 512) (vb cps ++ sublist (Zlength cps) 512 bv) vbuf;
       data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vbs;
       EX sv: list val, !! (Zlength sv = 6) && data_at Tsh (tarray tuchar 6) sv vseed).

(* The exit of the loop over the code points: result r and the sink (w, sh). *)
Definition cp_brk (st: Z) (w0: list Z) (sh0: bool) (cps: list Z) (bv: list val) : environ -> mpred :=
  EX w: list Z, EX sh: bool, EX r: Z,
  PROP ((r = -1 /\ put_utf8s cap (w0, sh0) cps = (false, (w, sh))) \/
        (r = res_of sh /\ put_utf8s cap (w0, sh0) cps = (true, (w, sh))))
  LOCAL (temp _tmpptr (tmp_at st); temp _inptr (offset_val st pin); temp _result (Vint (Int.repr r));
         lvar _seed (tarray tuchar 6) vseed; lvar _bufsize tuint vbs;
         lvar _pkt (Tstruct _wpacket_st noattr) vpkt; lvar _buf (tarray tuint 512) vbuf; gvars gv)
  SEP (a2u_frame; PacketSpec.wpkt Tsh vpkt sho out cap init w sub; instr st;
       data_at Tsh (tarray tuint 512) (vb cps ++ sublist (Zlength cps) 512 bv) vbuf;
       data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vbs;
       EX sv: list val, !! (Zlength sv = 6) && data_at Tsh (tarray tuchar 6) sv vseed).

End Asserts.

(* The facts every piece of the proof assumes. *)
Definition a2u_ctx (shi: share) (pin: val) (s: list Z) (sho: share) (out: val) (cap: Z) (init: list val) : Prop :=
  readable_share shi /\ writable_share sho /\ str_ok s /\ isptr pin /\
  field_compatible (tarray tuchar (Zlength s + 1)) [] pin /\ 0 <= cap <= Int64.max_unsigned /\
  Zlength init = cap /\ isptr out.

(* The conversion of the labels of rest, by its first label. *)
Lemma a2u_labels_first: forall cap k rest,
  a2u_labels cap k (labels rest) =
  let (ok, k1) := label_step cap k (label_of rest) in if ok then a2u_cont cap k1 rest else (-1, k1).
Proof.
  intros. unfold a2u_cont, label_of.
  destruct (Z_lt_le_dec (index_of 46 rest) (Zlength rest)) as [L|L].
  - rewrite labels_split by auto. simpl.
    destruct (label_step cap k (sublist 0 (index_of 46 rest) rest)) as [ok k1].
    destruct ok; auto.
    replace (index_of 46 rest <? Zlength rest) with true by (symmetry; apply Z.ltb_lt; auto).
    destruct (labels (sublist (index_of 46 rest + 1) (Zlength rest) rest)) eqn:E; auto.
    exfalso. eapply labels_ne; eauto.
  - pose proof (index_of_range 46 rest).
    assert (E: index_of 46 rest = Zlength rest) by lia.
    rewrite labels_none by auto. rewrite E, sublist_same by lia. simpl.
    destruct (label_step cap k rest) as [ok k1]. destruct ok; auto.
    replace (Zlength rest <? Zlength rest) with false by (symmetry; apply Z.ltb_ge; lia). auto.
Qed.
