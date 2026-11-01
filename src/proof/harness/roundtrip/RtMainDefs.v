(* The main of harness/x_roundtrip.c, cut into pieces: the statements of its tails (verbatim sub-terms of f_main's
   body), the assertions at each cut, and the piece lemmas' common shapes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.roundtrip.RtProg.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The tails of main's body                                               *)
(* ---------------------------------------------------------------------- *)

Definition stmt_lab_final : statement :=
(Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _want (tptr tuchar))
                                                                    (Etempvar _at tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _ossl_shim_fail_next tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _ossl_shim_zalloc_failed tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _ossl_shim_live tlong)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'17)
                                                                    (Evar _ossl_a2ulabel 
                                                                    (Tfunction
                                                                    ((tptr tschar) ::
                                                                    (tptr tschar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ecast
                                                                    (Etempvar _lab (tptr tuchar))
                                                                    (tptr tschar)) ::
                                                                    (Ecast
                                                                    (Etempvar _u (tptr tuchar))
                                                                    (tptr tschar)) ::
                                                                    (Etempvar _ulen tulong) ::
                                                                    nil))
                                                                    (Sset _r2
                                                                    (Etempvar _t'17 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Evar _ossl_shim_zalloc_failed tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'20 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r2 tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall (Some _t'18)
                                                                    (Evar _same_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _u (tptr tuchar)) ::
                                                                    (Etempvar _want (tptr tuchar)) ::
                                                                    (Etempvar _ulen tulong) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'18 tint) ::
                                                                    nil))))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _r2 tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Evar _ossl_shim_live tlong))
                                                                    (Scall None
                                                                    (Evar _gp_assert 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oeq
                                                                    (Etempvar _t'19 tlong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint) ::
                                                                    nil))))))))).

Definition stmt_lab_utf8 : statement :=
(Ssequence
                                                                  (Ssequence
                                                                    (Sset _j
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Etempvar _m tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _cps (tptr tuint))
                                                                    (Etempvar _j tulong)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Scall (Some _t'16)
                                                                    (Evar _pr_utf8 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'21 tuint) ::
                                                                    (Ebinop Oadd
                                                                    (Etempvar _want (tptr tuchar))
                                                                    (Etempvar _at tulong)
                                                                    (tptr tuchar)) ::
                                                                    nil)))
                                                                    (Sset _at
                                                                    (Ebinop Oadd
                                                                    (Etempvar _at tulong)
                                                                    (Etempvar _t'16 tulong)
                                                                    tulong))))
                                                                    (Sset _j
                                                                    (Ebinop Oadd
                                                                    (Etempvar _j tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                  stmt_lab_final).

Definition stmt_lab : statement :=
(Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _lab (tptr tuchar))
                                                      (Econst_int (Int.repr 0) tint)
                                                      (tptr tuchar)) tuchar)
                                                  (Econst_int (Int.repr 120) tint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _lab (tptr tuchar))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Econst_int (Int.repr 110) tint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _lab (tptr tuchar))
                                                          (Econst_int (Int.repr 2) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Econst_int (Int.repr 45) tint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _lab (tptr tuchar))
                                                            (Econst_int (Int.repr 3) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Econst_int (Int.repr 45) tint))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'22
                                                            (Evar _elen tulong))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _lab (tptr tuchar))
                                                                (Ebinop Oadd
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  (Etempvar _t'22 tulong)
                                                                  tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Econst_int (Int.repr 0) tint)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'13)
                                                              (Evar _quickproof_malloc 
                                                              (Tfunction
                                                                (tulong ::
                                                                 nil)
                                                                (tptr tvoid)
                                                                cc_default))
                                                              ((Etempvar _ulen tulong) ::
                                                               nil))
                                                            (Sset _u
                                                              (Etempvar _t'13 (tptr tvoid))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'14)
                                                                (Evar _quickproof_malloc 
                                                                (Tfunction
                                                                  (tulong ::
                                                                   nil)
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                                ((Etempvar _ulen tulong) ::
                                                                 nil))
                                                              (Sset _want
                                                                (Etempvar _t'14 (tptr tvoid))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _u (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                  (Sset _t'15
                                                                    (Econst_int (Int.repr 1) tint))
                                                                  (Sset _t'15
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _want (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                (Sifthenelse (Etempvar _t'15 tint)
                                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                  Sskip))
                                                              (Ssequence
                                                                (Sset _at
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                stmt_lab_utf8))))))))).

Definition stmt_if : statement :=
(Ssequence
                                            (Sifthenelse (Etempvar _one_label tint)
                                              stmt_lab
                                              Sskip)
                                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))).

Definition stmt_mallocs : statement :=
(Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'27 (Evar _elen tulong))
                              (Scall (Some _t'7)
                                (Evar _quickproof_malloc (Tfunction
                                                         (tulong :: nil)
                                                         (tptr tvoid)
                                                         cc_default))
                                ((Etempvar _t'27 tulong) :: nil)))
                            (Sset _enc (Etempvar _t'7 (tptr tvoid))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'8)
                                (Evar _quickproof_malloc (Tfunction
                                                         (tulong :: nil)
                                                         (tptr tvoid)
                                                         cc_default))
                                ((Ebinop Omul (Etempvar _m tulong)
                                   (Esizeof tuint tulong) tulong) :: nil))
                              (Sset _out (Etempvar _t'8 (tptr tvoid))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _enc (tptr tuchar))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    (Ssequence
                                      (Sset _t'26 (Evar _elen tulong))
                                      (Sset _t'9
                                        (Ecast
                                          (Ebinop Cop.One (Etempvar _t'26 tulong)
                                            (Econst_int (Int.repr 0) tint)
                                            tint) tbool)))
                                    (Sset _t'9
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _t'9 tint)
                                    (Sset _t'10
                                      (Econst_int (Int.repr 1) tint))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _out (tptr tuint))
                                                   (Ecast
                                                     (Econst_int (Int.repr 0) tint)
                                                     (tptr tvoid)) tint)
                                      (Ssequence
                                        (Sset _t'10
                                          (Ecast
                                            (Ebinop Cop.One (Etempvar _m tulong)
                                              (Econst_int (Int.repr 0) tint)
                                              tint) tbool))
                                        (Sset _t'10
                                          (Ecast (Etempvar _t'10 tint) tbool)))
                                      (Sset _t'10
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tbool)))))
                                (Sifthenelse (Etempvar _t'10 tint)
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                  Sskip))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'25 (Evar _elen tulong))
                                  (Scall None
                                    (Evar _copy_bytes (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                    ((Etempvar _enc (tptr tuchar)) ::
                                     (Ebinop Oadd
                                       (Etempvar _lab (tptr tuchar))
                                       (Econst_int (Int.repr 4) tint)
                                       (tptr tuchar)) ::
                                     (Etempvar _t'25 tulong) :: nil)))
                                (Ssequence
                                  (Sassign (Evar _olen tuint)
                                    (Ecast (Etempvar _m tulong) tuint))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'24 (Evar _elen tulong))
                                        (Scall (Some _t'11)
                                          (Evar _ossl_punycode_decode 
                                          (Tfunction
                                            ((tptr tschar) :: tulong ::
                                             (tptr tuint) :: (tptr tuint) ::
                                             nil) tint cc_default))
                                          ((Ecast
                                             (Etempvar _enc (tptr tuchar))
                                             (tptr tschar)) ::
                                           (Etempvar _t'24 tulong) ::
                                           (Etempvar _out (tptr tuint)) ::
                                           (Eaddrof (Evar _olen tuint)
                                             (tptr tuint)) :: nil)))
                                      (Sset _r (Etempvar _t'11 tint)))
                                    (Ssequence
                                      (Scall None
                                        (Evar _gp_assert (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Ebinop Oeq (Etempvar _r tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) :: nil))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'23 (Evar _olen tuint))
                                          (Scall None
                                            (Evar _gp_assert (Tfunction
                                                               (tint :: nil)
                                                               tvoid
                                                               cc_default))
                                            ((Ebinop Oeq
                                               (Etempvar _t'23 tuint)
                                               (Etempvar _m tulong) tint) ::
                                             nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'12)
                                              (Evar _same_uints (Tfunction
                                                                  ((tptr tuint) ::
                                                                   (tptr tuint) ::
                                                                   tulong ::
                                                                   nil) tint
                                                                  cc_default))
                                              ((Etempvar _out (tptr tuint)) ::
                                               (Etempvar _cps (tptr tuint)) ::
                                               (Etempvar _m tulong) :: nil))
                                            (Scall None
                                              (Evar _gp_assert (Tfunction
                                                                 (tint ::
                                                                  nil) tvoid
                                                                 cc_default))
                                              ((Etempvar _t'12 tint) :: nil)))
                                          stmt_if))))))))).

Definition stmt_ecap : statement :=
(Ssequence
                  (Sset _ecap
                    (Ebinop Oadd
                      (Ebinop Omul (Econst_int (Int.repr 16) tint)
                        (Etempvar _m tulong) tulong)
                      (Econst_int (Int.repr 1) tint) tulong))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                                 (tptr tvoid) cc_default))
                        ((Ebinop Oadd
                           (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                             (Etempvar _ecap tulong) tulong)
                           (Econst_int (Int.repr 1) tint) tulong) :: nil))
                      (Sset _lab (Etempvar _t'5 (tptr tvoid))))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _lab (tptr tuchar))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        Sskip)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _pr_encode (Tfunction
                                               ((tptr tuint) :: tulong ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tulong) :: nil) tint
                                               cc_default))
                            ((Etempvar _cps (tptr tuint)) ::
                             (Etempvar _m tulong) ::
                             (Ebinop Oadd (Etempvar _lab (tptr tuchar))
                               (Econst_int (Int.repr 4) tint) (tptr tuchar)) ::
                             (Etempvar _ecap tulong) ::
                             (Eaddrof (Evar _elen tulong) (tptr tulong)) ::
                             nil))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'6 tint)
                                         tint)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                            Sskip))
                        stmt_mallocs)))).

Definition stmt_loop1 : statement :=
(Ssequence
                (Ssequence
                  (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                                     (Etempvar _m tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Scall None
                          (Evar _nondet_bytes (Tfunction
                                                ((tptr tuchar) :: tulong ::
                                                 nil) tvoid cc_default))
                          ((Ecast
                             (Ebinop Oadd (Etempvar _cps (tptr tuint))
                               (Etempvar _j tulong) (tptr tuint))
                             (tptr tuchar)) :: (Esizeof tuint tulong) :: nil))
                        (Ssequence
                          (Ssequence
                            (Sset _t'33
                              (Ederef
                                (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                  (Etempvar _j tulong) (tptr tuint)) tuint))
                            (Scall None
                              (Evar _gp_assume (Tfunction (tint :: nil) tvoid
                                                 cc_default))
                              ((Ebinop Ole (Etempvar _t'33 tuint)
                                 (Econst_int (Int.repr 1114111) tint) tint) ::
                               nil)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'31
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                      (Etempvar _j tulong) (tptr tuint))
                                    tuint))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'31 tuint)
                                               (Econst_int (Int.repr 46) tint)
                                               tint)
                                  (Sset _t'4 (Econst_int (Int.repr 1) tint))
                                  (Ssequence
                                    (Sset _t'32
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _cps (tptr tuint))
                                          (Etempvar _j tulong) (tptr tuint))
                                        tuint))
                                    (Sset _t'4
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'32 tuint)
                                          (Econst_int (Int.repr 0) tint)
                                          tint) tbool)))))
                              (Sifthenelse (Etempvar _t'4 tint)
                                (Sset _one_label
                                  (Econst_int (Int.repr 0) tint))
                                Sskip))
                            (Ssequence
                              (Sset _t'28
                                (Ederef
                                  (Ebinop Oadd (Etempvar _cps (tptr tuint))
                                    (Etempvar _j tulong) (tptr tuint)) tuint))
                              (Sifthenelse (Ebinop Olt (Etempvar _t'28 tuint)
                                             (Econst_int (Int.repr 128) tint)
                                             tint)
                                (Sset _ulen
                                  (Ebinop Oadd (Etempvar _ulen tulong)
                                    (Econst_int (Int.repr 1) tint) tulong))
                                (Ssequence
                                  (Sset _t'29
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _cps (tptr tuint))
                                        (Etempvar _j tulong) (tptr tuint))
                                      tuint))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _t'29 tuint)
                                                 (Econst_int (Int.repr 2048) tint)
                                                 tint)
                                    (Sset _ulen
                                      (Ebinop Oadd (Etempvar _ulen tulong)
                                        (Econst_int (Int.repr 2) tint)
                                        tulong))
                                    (Ssequence
                                      (Sset _t'30
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _cps (tptr tuint))
                                            (Etempvar _j tulong)
                                            (tptr tuint)) tuint))
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _t'30 tuint)
                                                     (Econst_int (Int.repr 65536) tint)
                                                     tint)
                                        (Sset _ulen
                                          (Ebinop Oadd
                                            (Etempvar _ulen tulong)
                                            (Econst_int (Int.repr 3) tint)
                                            tulong))
                                        (Sset _ulen
                                          (Ebinop Oadd
                                            (Etempvar _ulen tulong)
                                            (Econst_int (Int.repr 4) tint)
                                            tulong))))))))))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                stmt_ecap).

(* ---------------------------------------------------------------------- *)
(* The context and the postcondition of the pieces                        *)
(* ---------------------------------------------------------------------- *)

Definition Delta_main : tycontext := func_tycontext f_main (QPvarspecs p) Gmain nil.

(* start_function's POSTCONDITION for main_spec_std. *)
Definition main_post : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* main's body is Ssequence BIG (return 0) and BIG always returns: the pieces are tails of BIG, with the normal
   postcondition FF (Main.v: semax_seq with FF first). *)
Definition main_ret : ret_assert := overridePost FF main_post.

(* After the if (one_label) of the second half: what return 0 needs. *)
Definition Q_ret (vo ve: val) : environ -> mpred :=
  PROP () LOCAL (lvar _olen tuint vo; lvar _elen tulong ve)
  SEP (data_at_ Tsh tuint vo; data_at_ Tsh tulong ve; TT).

(* ---------------------------------------------------------------------- *)
(* The model's view of the code points                                    *)
(* ---------------------------------------------------------------------- *)

(* one_label: no code point is '.' or NUL. *)
Definition one_label_ok (cps: list Z) : bool := forallb (fun c => (negb (c =? 46) && negb (c =? 0))%bool) cps.

(* The UTF-8 form of the code points. *)
Definition utf8s (cps: list Z) : list Z := concat (map utf8 cps).

(* ulen: the UTF-8 form and its NUL. *)
Definition ulen_of (cps: list Z) : Z := Zlength (utf8s cps) + 1.

(* The globals main keeps from globvars2pred, mem_mgr, and TT for everything dropped (malloc tokens, has_ext, ...). *)
Definition main_frame (gv: globals) : list mpred :=
  [OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; OpensslPunycode.proof.punycode.PunySpec.xn_lit gv;
   OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0; mem_mgr gv; TT].

(* "xn--" then the encoding: the string ossl_a2ulabel gets. *)
Definition ace (e: list Z) : list Z := [120; 110; 45; 45] ++ e.

(* The buffer lab after pr_encode: 4 octets, the encoding, the rest of its 16 m + 6 octets. *)
Definition lab_after_encode (m: Z) (e: list Z) : list val :=
  Zrepeat Vundef 4 ++ vb e ++ Zrepeat Vundef (16 * m + 2 - Zlength e).

(* ---------------------------------------------------------------------- *)
(* The assertions at the cuts                                             *)
(* ---------------------------------------------------------------------- *)

(* Before stmt_loop1: m drawn, cps allocated (arr0: nothing when m = 0), one_label = 1, ulen = 1. *)
Definition P_loop1 (gv: globals) (m: Z) (pc vo ve: val) : environ -> mpred :=
  PROPx [0 <= m <= 512]
  (LOCALx [temp _ulen (Vlong (Int64.repr 1)); temp _one_label (Vint (Int.repr 1)); temp _cps pc;
           temp _m (Vlong (Int64.repr m)); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (arr0 Ews tuint m (Zrepeat Vundef m) pc :: data_at_ Tsh tuint vo :: data_at_ Tsh tulong ve ::
         main_frame gv))).

(* Before stmt_ecap: the code points drawn. *)
Definition P_ecap (gv: globals) (cps: list Z) (pc vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps]
  (LOCALx [temp _ulen (Vlong (Int64.repr (ulen_of cps)));
           temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (arr0 Ews tuint (Zlength cps) (vb cps) pc :: data_at_ Tsh tuint vo :: data_at_ Tsh tulong ve ::
         main_frame gv))).

(* Before stmt_mallocs: pr_encode succeeded with e (elen = |e|) in lab. *)
Definition P_mallocs (gv: globals) (cps e: list Z) (pc plab vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1]
  (LOCALx [temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps)));
           temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at Ews (tarray tuchar (16 * Zlength cps + 6)) (lab_after_encode (Zlength cps) e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at_ Tsh tuint vo :: data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

(* Before stmt_if: the decoder's checks passed. *)
Definition P_if (gv: globals) (cps e: list Z) (pc plab vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1]
  (LOCALx [temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps)));
           temp _one_label (Vint (Int.repr (if one_label_ok cps then 1 else 0))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at Ews (tarray tuchar (16 * Zlength cps + 6)) (lab_after_encode (Zlength cps) e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo ::
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

(* Before stmt_lab (the then-branch): P_if with one_label. *)
Definition P_lab (gv: globals) (cps e: list Z) (pc plab vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1; one_label_ok cps = true]
  (LOCALx [temp _lab plab; temp _ulen (Vlong (Int64.repr (ulen_of cps))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at Ews (tarray tuchar (16 * Zlength cps + 6)) (lab_after_encode (Zlength cps) e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo ::
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

(* Before stmt_lab_utf8: lab is the string "xn--" e, u and want allocated (ulen octets each), at = 0. *)
Definition P_utf8 (gv: globals) (cps e: list Z) (pc plab pu pw vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1; one_label_ok cps = true]
  (LOCALx [temp _at (Vlong (Int64.repr 0)); temp _want pw; temp _u pu; temp _lab plab;
           temp _ulen (Vlong (Int64.repr (ulen_of cps))); temp _cps pc;
           temp _m (Vlong (Int64.repr (Zlength cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at_ Ews (tarray tuchar (ulen_of cps)) pw :: data_at_ Ews (tarray tuchar (ulen_of cps)) pu ::
         OpensslPunycode.proof.shim.ShimSpec.cstr Ews (ace e) plab ::
         arr0 Ews tuint (Zlength cps) (vb cps) pc ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo ::
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

(* Before stmt_lab_final: want holds the UTF-8 form (its last octet still unset), at = |utf8s cps|. *)
Definition P_final (gv: globals) (cps e: list Z) (plab pu pw vo ve: val) : environ -> mpred :=
  PROPx [Zlength cps <= 512; Forall (fun c => 0 <= c <= 1114111) cps; encode cps = Some e;
         Zlength e <= 16 * Zlength cps + 1; one_label_ok cps = true]
  (LOCALx [temp _at (Vlong (Int64.repr (Zlength (utf8s cps)))); temp _want pw; temp _u pu; temp _lab plab;
           temp _ulen (Vlong (Int64.repr (ulen_of cps))); gvars gv; lvar _olen tuint vo; lvar _elen tulong ve]
  (SEPx (data_at Ews (tarray tuchar (ulen_of cps)) (vb (utf8s cps) ++ [Vundef]) pw ::
         data_at_ Ews (tarray tuchar (ulen_of cps)) pu ::
         OpensslPunycode.proof.shim.ShimSpec.cstr Ews (ace e) plab ::
         data_at Tsh tuint (Vint (Int.repr (Zlength cps))) vo ::
         data_at Tsh tulong (Vlong (Int64.repr (Zlength e))) ve ::
         main_frame gv))).

(* ---------------------------------------------------------------------- *)
(* The model fact of the second half (MainModel.v proves it from the roundtrip theorem)  *)
(* ---------------------------------------------------------------------- *)

(* ossl_a2ulabel's model on "xn--" e with exactly the room of the UTF-8 form and its NUL: one label, decoded back
   to cps, every write fits. *)
Definition a2u_model_stmt : Prop :=
  forall cps e,
    Zlength cps <= 512 -> Forall (fun c => 0 <= c <= 1114111) cps -> encode cps = Some e ->
    Zlength e <= 16 * Zlength cps + 1 -> one_label_ok cps = true ->
    a2ulabel (ace e) (ulen_of cps) = (1, utf8s cps ++ [0]).

(* ---------------------------------------------------------------------- *)
(* The statements of the pieces (each proved in its own file from the next one, chained in Main.v) *)
(* ---------------------------------------------------------------------- *)

Definition piece_final_stmt : Prop :=
  forall (Espec: OracleKind) gv cps e plab pu pw vo ve,
    semax Delta_main (P_final gv cps e plab pu pw vo ve) stmt_lab_final (overridePost (Q_ret vo ve) main_ret).

Definition piece_utf8_stmt : Prop :=
  forall (Espec: OracleKind) gv cps e pc plab pu pw vo ve,
    semax Delta_main (P_utf8 gv cps e pc plab pu pw vo ve) stmt_lab_utf8 (overridePost (Q_ret vo ve) main_ret).

Definition piece_lab_stmt : Prop :=
  forall (Espec: OracleKind) gv cps e pc plab vo ve,
    semax Delta_main (P_lab gv cps e pc plab vo ve) stmt_lab (overridePost (Q_ret vo ve) main_ret).

Definition piece_if_stmt : Prop :=
  forall (Espec: OracleKind) gv cps e pc plab vo ve,
    semax Delta_main (P_if gv cps e pc plab vo ve) stmt_if main_ret.

Definition piece_mallocs_stmt : Prop :=
  forall (Espec: OracleKind) gv cps e pc plab vo ve,
    semax Delta_main (P_mallocs gv cps e pc plab vo ve) stmt_mallocs main_ret.

Definition piece_ecap_stmt : Prop :=
  forall (Espec: OracleKind) gv cps pc vo ve,
    semax Delta_main (P_ecap gv cps pc vo ve) stmt_ecap main_ret.

Definition piece_loop1_stmt : Prop :=
  forall (Espec: OracleKind) gv m pc vo ve,
    semax Delta_main (P_loop1 gv m pc vo ve) stmt_loop1 main_ret.
