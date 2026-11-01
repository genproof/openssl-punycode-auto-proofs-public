(* The body of pr_utf8, part B: from the three-octet case on (part of BodiesRt.v). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.harness.x_roundtrip.code.
Require Import OpensslPunycode.proof.harness.BodyRtUtf8Lib.
Require Import OpensslPunycode.proof.harness.BodyRtUtf8C.

Definition stmt_utf8_b : statement :=
(Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _c tulong)
                     (Econst_int (Int.repr 65536) tint) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oadd (Econst_int (Int.repr 224) tint)
                (Ebinop Odiv (Etempvar _c tulong)
                  (Econst_int (Int.repr 4096) tint) tulong) tulong) tuchar))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                  (Ebinop Omod
                    (Ebinop Odiv (Etempvar _c tulong)
                      (Econst_int (Int.repr 64) tint) tulong)
                    (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tuchar))
                    (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                    (Ebinop Omod (Etempvar _c tulong)
                      (Econst_int (Int.repr 64) tint) tulong) tulong) tuchar))
              (Sreturn (Some (Econst_int (Int.repr 3) tint))))))
        Sskip)
      stmt_utf8_c).

Lemma utf8_piece_b {Espec: OracleKind}: forall c sh o old,
  writable_share sh -> 0 <= c <= Int64.max_unsigned -> Zlength old = Zlength (utf8 c) -> 2048 <= c ->
  semax (func_tycontext f_pr_utf8 Vprog Gprog_none nil) (PROP () LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o) SEP (arr0 sh tuchar (Zlength (utf8 c)) old o))
    stmt_utf8_b
    (frame_ret_assert (function_body_ret_assert tulong
     (PROP () RETURN (Vlong (Int64.repr (Zlength (utf8 c))))
      SEP (arr0 sh tuchar (Zlength (utf8 c)) (vb (utf8 c)) o)))
    (stackframe_of f_pr_utf8)).
Proof.
  intros c sh o old SH H H0 H2. unfold stmt_utf8_b. abbreviate_semax.
  forward_if (PROP (65536 <= c) LOCAL (temp _c (Vlong (Int64.repr c)); temp _o o)
    SEP (arr0 sh tuchar (Zlength (utf8 c)) old o)).
  { rewrite !Int64.unsigned_repr in H1 by rep_lia.
    assert (E: utf8 c = [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64])
      by (unfold utf8; rewrite (proj2 (Z.ltb_ge c 128)), (proj2 (Z.ltb_ge c 2048)), (proj2 (Z.ltb_lt c 65536)) by lia; auto).
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    rewrite E in H0. change (Zlength [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64]) with 3 in *.
    forward. forward. forward. forward. rewrite upd_3 by auto. utf8_vals.
    rewrite E. unfold arr0. rewrite if_false by (rewrite !Zlength_cons, Zlength_nil; lia).
    change (Zlength [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64]) with 3. entailer!.
    utf8_fin c. }
  { forward. entailer!. rewrite !Int64.unsigned_repr in H1 by rep_lia. lia. }
  Intros. apply utf8_piece_c; auto.
Qed.
