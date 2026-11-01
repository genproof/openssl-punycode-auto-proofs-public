(* The body of pr_utf8, part C: the four-octet case and the code points above 0x10FFFF (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.BodyRtUtf8Lib.

Definition stmt_utf8_c : statement :=
(Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _c tulong)
                       (Econst_int (Int.repr 1114111) tint) tint)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oadd (Econst_int (Int.repr 240) tint)
                  (Ebinop Odiv (Etempvar _c tulong)
                    (Econst_int (Int.repr 262144) tint) tulong) tulong)
                tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                    (Ebinop Omod
                      (Ebinop Odiv (Etempvar _c tulong)
                        (Econst_int (Int.repr 4096) tint) tulong)
                      (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tuchar))
                      (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                  (Ecast
                    (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                      (Ebinop Omod
                        (Ebinop Odiv (Etempvar _c tulong)
                          (Econst_int (Int.repr 64) tint) tulong)
                        (Econst_int (Int.repr 64) tint) tulong) tulong)
                    tuchar))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _o (tptr tuchar))
                        (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
                    (Ecast
                      (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                        (Ebinop Omod (Etempvar _c tulong)
                          (Econst_int (Int.repr 64) tint) tulong) tulong)
                      tuchar))
                  (Sreturn (Some (Econst_int (Int.repr 4) tint)))))))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))).

Lemma utf8_piece_c {Espec: OracleKind}: forall c sh o old,
  writable_share sh -> 0 <= c <= Int64.max_unsigned -> Zlength old = Zlength (utf8 c) -> 65536 <= c ->
  semax (func_tycontext f_pr_utf8 Vprog Gprog_none nil) (PROP () LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o) SEP (arr0 sh tuchar (Zlength (utf8 c)) old o))
    stmt_utf8_c
    (frame_ret_assert (function_body_ret_assert tulong
     (PROP () RETURN (Vlong (Int64.repr (Zlength (utf8 c))))
      SEP (arr0 sh tuchar (Zlength (utf8 c)) (vb (utf8 c)) o)))
    (stackframe_of f_pr_utf8)).
Proof.
  intros c sh o old SH H H0 H2. unfold stmt_utf8_c. abbreviate_semax.
  forward_if (PROP (1114111 < c) LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o)
    SEP (arr0 sh tuchar (Zlength (utf8 c)) old o)).
  { rewrite !Int64.unsigned_repr in H1 by rep_lia.
    assert (E: utf8 c = [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64])
      by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_ge c 2048)), (proj2 (Z.ltb_ge c 65536)),
            (proj2 (Z.leb_le c 1114111)) by lia; auto).
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    rewrite E in H0.
    change (Zlength [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64]) with 4 in *.
    forward. forward. forward. forward. forward. rewrite upd_4 by auto. utf8_vals.
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    change (Zlength [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64]) with 4.
    entailer!.
    utf8_fin c. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. lia. }
  Intros.
  assert (E: utf8 c = [])
    by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_ge c 2048)), (proj2 (Z.ltb_ge c 65536)),
          (proj2 (Z.leb_gt c 1114111)) by lia; auto).
  forward. rewrite E. unfold arr0. simpl. entailer!.
Qed.
