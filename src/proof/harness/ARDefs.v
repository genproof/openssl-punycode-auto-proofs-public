(* Shared vocabulary of the proof of pr_a2ulabel (harness/puny_ref.h) under the a2ulabel harness's compspecs,
   split over the AR*.v files: its sub-statements (copied from the Clight body), its ret_assert, the invariants. *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.proof.harness.ARModel.
Require Import OpensslPunycode.harness.x_a2ulabel.code.

Definition s_find : statement :=
  (Sloop
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _e tulong)
                                     (Etempvar _n tulong) tint)
                        (Ssequence
                          (Sset _t'17
                            (Ederef
                              (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                (Etempvar _e tulong) (tptr tuchar)) tuchar))
                          (Sset _t'1
                            (Ecast
                              (Ebinop Cop.One (Etempvar _t'17 tuchar)
                                (Econst_int (Int.repr 46) tint) tint) tbool)))
                        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                      (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
                    (Sset _e
                      (Ebinop Oadd (Etempvar _e tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  Sskip).

Definition s_test : statement :=
  (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oge (Etempvar _m tulong)
                                           (Econst_int (Int.repr 4) tint)
                                           tint)
                              (Ssequence
                                (Sset _t'15
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Etempvar _st tulong) (tptr tuchar))
                                    tuchar))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'15 tuchar)
                                               (Econst_int (Int.repr 120) tint)
                                               tint)
                                  (Sset _t'3
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'16
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Etempvar _st tulong)
                                            (tptr tuchar)) tuchar))
                                      (Sset _t'3
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'16 tuchar)
                                            (Econst_int (Int.repr 88) tint)
                                            tint) tbool)))
                                    (Sset _t'3
                                      (Ecast (Etempvar _t'3 tint) tbool)))))
                              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _t'3 tint)
                              (Ssequence
                                (Sset _t'13
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                      (Ebinop Oadd (Etempvar _st tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong) (tptr tuchar)) tuchar))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'13 tuchar)
                                               (Econst_int (Int.repr 110) tint)
                                               tint)
                                  (Sset _t'4
                                    (Ecast (Econst_int (Int.repr 1) tint)
                                      tbool))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'14
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _s (tptr tuchar))
                                            (Ebinop Oadd
                                              (Etempvar _st tulong)
                                              (Econst_int (Int.repr 1) tint)
                                              tulong) (tptr tuchar)) tuchar))
                                      (Sset _t'4
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'14 tuchar)
                                            (Econst_int (Int.repr 78) tint)
                                            tint) tbool)))
                                    (Sset _t'4
                                      (Ecast (Etempvar _t'4 tint) tbool)))))
                              (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'4 tint)
                            (Ssequence
                              (Sset _t'12
                                (Ederef
                                  (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                    (Ebinop Oadd (Etempvar _st tulong)
                                      (Econst_int (Int.repr 2) tint) tulong)
                                    (tptr tuchar)) tuchar))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _t'12 tuchar)
                                    (Econst_int (Int.repr 45) tint) tint)
                                  tbool)))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Sset _t'11
                              (Ederef
                                (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                  (Ebinop Oadd (Etempvar _st tulong)
                                    (Econst_int (Int.repr 3) tint) tulong)
                                  (tptr tuchar)) tuchar))
                            (Sset _t'6
                              (Ecast
                                (Ebinop Oeq (Etempvar _t'11 tuchar)
                                  (Econst_int (Int.repr 45) tint) tint)
                                tbool)))
                          (Sset _t'6 (Econst_int (Int.repr 0) tint)))).

Definition s_nonace : statement :=
  (Scall None
                          (Evar _pr_put (Tfunction
                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                           (tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                           (Ebinop Oadd (Etempvar _s (tptr tuchar))
                             (Etempvar _st tulong) (tptr tuchar)) ::
                           (Etempvar _m tulong) :: nil)).

Definition s_acechk : statement :=
  (Sifthenelse (Ebinop Oge
                                         (Ebinop Osub (Etempvar _m tulong)
                                           (Econst_int (Int.repr 4) tint)
                                           tulong)
                                         (Econst_long (Int64.repr 4294967295) tulong)
                                         tint)
                            (Sreturn (Some (Eunop Oneg
                                             (Econst_int (Int.repr 1) tint)
                                             tint)))
                            Sskip).

Definition s_call : statement :=
  (Scall None
                              (Evar _pr_decode (Tfunction
                                                 ((tptr tuchar) :: tulong ::
                                                  (tptr tuint) :: tulong ::
                                                  (tptr (Tstruct _pr_dec noattr)) ::
                                                  nil) tvoid cc_default))
                              ((Ebinop Oadd
                                 (Ebinop Oadd (Etempvar _s (tptr tuchar))
                                   (Etempvar _st tulong) (tptr tuchar))
                                 (Econst_int (Int.repr 4) tint)
                                 (tptr tuchar)) ::
                               (Ebinop Osub (Etempvar _m tulong)
                                 (Econst_int (Int.repr 4) tint) tulong) ::
                               (Etempvar _cps (tptr tuint)) ::
                               (Econst_int (Int.repr 512) tint) ::
                               (Eaddrof (Evar _d (Tstruct _pr_dec noattr))
                                 (tptr (Tstruct _pr_dec noattr))) :: nil)).

Definition s_okchk : statement :=
  (Ssequence
                                (Sset _t'10
                                  (Efield (Evar _d (Tstruct _pr_dec noattr))
                                    _ok tint))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _t'10 tint) tint)
                                  (Sreturn (Some (Eunop Oneg
                                                   (Econst_int (Int.repr 1) tint)
                                                   tint)))
                                  Sskip)).

Definition s_cploop : statement :=
  (Ssequence
                                (Sset _j
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tulong))
                                (Sloop
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Evar _d (Tstruct _pr_dec noattr))
                                          _count tulong))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _j tulong)
                                                     (Etempvar _t'9 tulong)
                                                     tint)
                                        Sskip
                                        Sbreak))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _cps (tptr tuint))
                                                (Etempvar _j tulong)
                                                (tptr tuint)) tuint))
                                          (Scall (Some _t'2)
                                            (Evar _pr_utf8 (Tfunction
                                                             (tulong ::
                                                              (tptr tuchar) ::
                                                              nil) tulong
                                                             cc_default))
                                            ((Etempvar _t'8 tuint) ::
                                             (Evar _u (tarray tuchar 4)) ::
                                             nil)))
                                        (Sset _ul (Etempvar _t'2 tulong)))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _ul tulong)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Sreturn (Some (Eunop Oneg
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)))
                                          Sskip)
                                        (Scall None
                                          (Evar _pr_put (Tfunction
                                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                                           (Evar _u (tarray tuchar 4)) ::
                                           (Etempvar _ul tulong) :: nil)))))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)))).

Definition s_cpbody : statement :=
  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Evar _d (Tstruct _pr_dec noattr))
                                          _count tulong))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _j tulong)
                                                     (Etempvar _t'9 tulong)
                                                     tint)
                                        Sskip
                                        Sbreak))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'8
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _cps (tptr tuint))
                                                (Etempvar _j tulong)
                                                (tptr tuint)) tuint))
                                          (Scall (Some _t'2)
                                            (Evar _pr_utf8 (Tfunction
                                                             (tulong ::
                                                              (tptr tuchar) ::
                                                              nil) tulong
                                                             cc_default))
                                            ((Etempvar _t'8 tuint) ::
                                             (Evar _u (tarray tuchar 4)) ::
                                             nil)))
                                        (Sset _ul (Etempvar _t'2 tulong)))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _ul tulong)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Sreturn (Some (Eunop Oneg
                                                           (Econst_int (Int.repr 1) tint)
                                                           tint)))
                                          Sskip)
                                        (Scall None
                                          (Evar _pr_put (Tfunction
                                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                                           (Evar _u (tarray tuchar 4)) ::
                                           (Etempvar _ul tulong) :: nil))))).

Definition s_cpincr : statement :=
  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tulong)
                                      (Econst_int (Int.repr 1) tint) tulong)).

Definition s_rest : statement :=
  (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _e tulong)
                                     (Etempvar _n tulong) tint)
                        Sbreak
                        Sskip)
                      (Ssequence
                        (Scall None
                          (Evar _pr_put (Tfunction
                                          ((tptr (Tstruct _pr_sink noattr)) ::
                                           (tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                          ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
                           (Eaddrof (Evar _sep tuchar) (tptr tuchar)) ::
                           (Econst_int (Int.repr 1) tint) :: nil))
                        (Sset _st
                          (Ebinop Oadd (Etempvar _e tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))).

Definition s_tail : statement :=
  (Ssequence
          (Scall None
            (Evar _pr_put (Tfunction
                            ((tptr (Tstruct _pr_sink noattr)) ::
                             (tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
            ((Etempvar _k (tptr (Tstruct _pr_sink noattr))) ::
             (Eaddrof (Evar _nul tuchar) (tptr tuchar)) ::
             (Econst_int (Int.repr 1) tint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _k (tptr (Tstruct _pr_sink noattr)))
                    (Tstruct _pr_sink noattr)) _short_ tint))
              (Sifthenelse (Etempvar _t'7 tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))
            (Sreturn (Some (Econst_int (Int.repr 1) tint))))).


Local Open Scope logic.

Definition t_decA := Tstruct _pr_dec noattr.

Definition Delta_a2u : tycontext := func_tycontext f_pr_a2ulabel Vprog Gprog_a2ulabel nil.

Section Asserts.
Variables (shs: share) (ps: val) (s: list Z) (shk: share) (pk buf: val) (cap: Z) (init: list val)
  (shb shc: share) (pc: val) (v_sep v_nul v_d v_u: val).

(* The facts of the precondition (and ps a pointer: the body computes s + st). *)
Definition ar_ctx : Prop :=
  readable_share shs /\ writable_share shk /\ writable_share shb /\ writable_share shc /\ bytes_ok s /\
  Zlength s < Int64.max_unsigned /\ 1 <= cap <= Int64.max_unsigned /\ Zlength init = cap /\ isptr ps.

(* The model's run of the whole string. *)
Definition A0 : Z * sink := a2u_labels cap ([], false) (labels s).

(* The ret_assert of the body (after start_function). *)
Definition ar_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint
      (EX short: bool, EX cinit': list val,
       PROP (Zlength cinit' = label_cap)
       RETURN (Vint (Int.repr (fst (a2ulabel s cap))))
       SEP (arr0 shs tuchar (Zlength s) (vb s) ps;
            data_at shk t_sink (sink_rep buf cap (snd (a2ulabel s cap), short)) pk;
            sink_buf shb buf cap init (snd (a2ulabel s cap));
            data_at shc (tarray tuint label_cap) cinit' pc))%argsassert)
    (stackframe_of f_pr_a2ulabel).

(* The invariant of the label loop: st the start of the current label, k the sink, cv the scratch array. *)
Definition ar_inv : environ -> mpred :=
  EX st: Z, EX k: sink, EX cv: list val,
  PROP (0 <= st <= Zlength s; sink_ok cap k; Zlength cv = label_cap;
        a2u_labels cap k (labels (rem s st)) = A0)
  LOCAL (temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

(* The exit of the label loop (after the last label): the model's result is that of the final NUL. *)
Definition ar_brk : environ -> mpred :=
  EX k: sink, EX cv: list val,
  PROP (sink_ok cap k; Zlength cv = label_cap;
        A0 = (if snd (put cap k [0]) then 0 else 1, put cap k [0]))
  LOCAL (temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

(* The ret_assert of the loop body. *)
Definition ar_RB : ret_assert := loop1_ret_assert ar_inv (overridePost ar_brk ar_post).

Variables (st: Z) (k: sink) (cv: list val).

(* The facts at every point of one iteration. *)
Definition it_ok : Prop :=
  0 <= st <= Zlength s /\ sink_ok cap k /\ Zlength cv = label_cap /\ a2u_labels cap k (labels (rem s st)) = A0.

(* Before the search of the label's end. *)
Definition find_pre : environ -> mpred :=
  PROP ()
  LOCAL (temp _e (Vlong (Int64.repr st)); temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

Definition find_post : environ -> mpred :=
  PROP ()
  LOCAL (temp _e (Vlong (Int64.repr (lab_end s st))); temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

(* The label [st, e) found, m = e - st. *)
Definition lab_pre : environ -> mpred :=
  PROP ()
  LOCAL (temp _m (Vlong (Int64.repr (lab_end s st - st))); temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

(* After the ACE test: t'6 is the test's value. *)
Definition test_post : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'6 (Val.of_bool (is_ace (lab s st)));
         temp _m (Vlong (Int64.repr (lab_end s st - st))); temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _st (Vlong (Int64.repr st));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k); data_at shc (tarray tuint label_cap) cv pc).

(* After the label (it succeeded: a failure returns): k1 the sink. *)
Definition lab_post : environ -> mpred :=
  EX k1: sink, EX cv1: list val,
  PROP (label_step cap k (lab s st) = (true, k1); sink_ok cap k1; Zlength cv1 = label_cap)
  LOCAL (temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u; data_at_ Tsh t_decA v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k1) pk;
       sink_buf shb buf cap init (fst k1); data_at shc (tarray tuint label_cap) cv1 pc).

(* In an ACE label, after the decoding succeeded into cps: the code-point loop starts. *)
Definition ace_mid (cps: list Z) : environ -> mpred :=
  PROP ()
  LOCAL (temp _e (Vlong (Int64.repr (lab_end s st)));
         temp _s ps; temp _n (Vlong (Int64.repr (Zlength s))); temp _k pk; temp _cps pc;
         lvar _u (tarray tuchar 4) v_u; lvar _d t_decA v_d; lvar _nul tuchar v_nul; lvar _sep tuchar v_sep)
  SEP (data_at_ Tsh (tarray tuchar 4) v_u;
       data_at Tsh t_decA (Vint (Int.repr 1), Vlong (Int64.repr (Zlength cps))) v_d;
       data_at Tsh tuchar (Vint (Int.repr 0)) v_nul; data_at Tsh tuchar (Vint (Int.repr 46)) v_sep;
       arr0 shs tuchar (Zlength s) (vb s) ps; data_at shk t_sink (sink_rep buf cap k) pk;
       sink_buf shb buf cap init (fst k);
       data_at shc (tarray tuint label_cap) (vb cps ++ sublist (Zlength cps) label_cap cv) pc).

End Asserts.

Lemma sub64_repr: forall a b, Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_sub; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.

Lemma add64_repr: forall a b, Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof. intros. apply Int64.eqm_samerepr. apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr. Qed.
