(* The body of copy_of (harness/laws_common.h): NULL for a NULL source, else malloc(n) and the n octets copied one
   by one while the copy is non-NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Lemma body_copy_of : semax_body Vprog Gprog_copy_of f_copy_of copy_of_spec.
Proof.
  start_function.
  set (N := Zlength bs) in *.
  forward_if (PROP (src <> nullval)
    LOCAL (temp _source src; temp _n (Vlong (Int64.repr n)); gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src)).
  { destruct (eq_dec src nullval) as [E|E].
    - subst src. entailer!.
    - apply derives_trans with (malloc_token Ews (tarray tuchar N) src * data_at sh (tarray tuchar N) (vb bs) src * TT)%logic;
        [ cancel | apply cmn_src_tc_test; auto; simpl; rep_lia ]. }
  { forward. Exists nullval. rewrite !if_true by auto. entailer!. }
  { forward. rewrite if_false by auto. entailer!. }
  Intros.
  forward_call (tarray tuchar n, gv).
  { simpl; rep_lia. }
  Intros p.
  forward.
  destruct (eq_dec p nullval) as [Hp|Hp].
  - subst p.
    forward_loop (PROP () LOCAL (temp _copy nullval; temp _i (Vlong (Int64.repr 0)); temp _source src;
        temp _n (Vlong (Int64.repr n)); gvars gv) SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src))
      break: (PROP () LOCAL (temp _copy nullval) SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src)).
    + entailer!.
    + forward_if (temp _t'2 (Vint (Int.repr 0))).
      { discriminate. }
      { forward. entailer!. }
      forward_if. { exfalso; lia. }
      forward. entailer!.
    + forward. Exists nullval. destruct (eq_dec src nullval); [ contradiction | ].
      destruct (eq_dec nullval nullval); [ | contradiction ]. entailer!.
  - forward_loop (EX i: Z,
        PROP (0 <= i <= n)
        LOCAL (temp _copy p; temp _i (Vlong (Int64.repr i)); temp _source src;
               temp _n (Vlong (Int64.repr n)); gvars gv)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (sublist 0 i (vb bs) ++ Zrepeat Vundef (n - i)) p))
      continue: (EX i: Z,
        PROP (0 <= i < n)
        LOCAL (temp _copy p; temp _i (Vlong (Int64.repr i)); temp _source src;
               temp _n (Vlong (Int64.repr n)); gvars gv)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (sublist 0 (i + 1)%Z (vb bs) ++ Zrepeat Vundef (n - (i + 1))%Z) p))
      break: (
        PROP ()
        LOCAL (temp _copy p)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuchar N) src; data_at sh (tarray tuchar N) (vb bs) src; malloc_token Ews (tarray tuchar n) p;
             data_at Ews (tarray tuchar n) (sublist 0 n (vb bs)) p)).
    + Exists 0. entailer!. unfold data_at_, field_at_. simpl. entailer!.
    + Intros i.
      forward_if (temp _t'2 (Vint (Int.repr (if zlt i n then 1 else 0)))).
      { forward. entailer!. destruct (zlt _ _); auto. }
      { contradiction. }
      forward_if.
      * destruct (zlt i n); [ | exfalso; lia ].
        assert (Hb: 0 <= Znth i bs <= 255) by (apply (proj1 (Forall_Znth _ _) H); lia).
        assert (HZ: Znth i (vb bs) = Vint (Int.repr (Znth i bs))) by (unfold vb; rewrite Znth_map by lia; auto).
        forward.
        { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZ. simpl.
          rewrite Int.unsigned_repr by rep_lia. rep_lia. }
        change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite HZ.
        forward.
        Exists i. entailer!.
        apply derives_refl'. f_equal. list_solve.
      * destruct (zlt i n); [ discriminate | ].
        forward. entailer!.
        replace (n - i) with 0 by lia. replace i with n by lia. simpl. rewrite app_nil_r. auto.
    + Intros i. forward. Exists (i + 1). entailer!.
    + forward. Exists p. rewrite !if_false by auto. entailer!.
      unfold vb. rewrite sublist_map. auto.
Qed.
