(* Piece 6 of the main of harness/api_decode_capacity.c: the loop that copies the c initial values of out into
   saved (DcapMainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.api_decode_capacity.code.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapProg.
Require Import OpensslPunycode.proof.laws.api_decode_capacity.DcapMainDefs.
Local Open Scope logic.

Module PS := OpensslPunycode.proof.punycode.PunySpec.
Module CM := OpensslPunycode.proof.laws.common.HelperSpec.

Lemma piece6 : piece7_stmt -> piece6_stmt.
Proof.
  intros H7 Espec gv vc ve vf bs pi c init po ps. unfold pre6, lvars3, T6, ret0, main_post, Delta_main.
  abbreviate_semax. Intros. forward.
  (* cap = 0: both arrays are empty (arr0 is emp) and the loop exits at once. *)
  destruct (zeq c 0) as [Hc0|Hc0].
  - assert (init = []) by (apply Zlength_nil_inv; lia). subst init c.
    forward_loop (
        PROP ()
        LOCAL (temp _i (Vint (Int.repr 0)); temp _saved ps; temp _out po; temp _cap (Vint (Int.repr 0));
               temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
               lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
        SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint 0 (vb []) po;
             arr0 Ews tuint 0 (Zrepeat Vundef 0) ps;
             data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
             PunySpec.puny_consts gv; mem_mgr gv; TT))
      break: (
        PROP ()
        LOCAL (temp _saved ps; temp _out po; temp _cap (Vint (Int.repr 0));
               temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
               lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
        SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; arr0 Ews tuint 0 (vb []) po;
             arr0 Ews tuint 0 (Zrepeat Vundef 0) ps;
             data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
             PunySpec.puny_consts gv; mem_mgr gv; TT)).
    + entailer!.
    + forward_if.
      * lia.
      * forward. entailer!.
    + unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
      eapply semax_pre; [ | apply (H7 Espec gv vc ve vf bs pi 0 [] po ps) ]. unfold pre7, lvars3.
      entailer!.
  (* cap > 0: after i rounds, saved holds the first i values of out, the rest uninitialised. *)
  - unfold arr0 at 2 3; rewrite !if_false by auto.
    forward_loop (EX i: Z,
        PROP (0 <= i <= c)
        LOCAL (temp _i (Vint (Int.repr i)); temp _saved ps; temp _out po; temp _cap (Vint (Int.repr c));
               temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
               lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
        SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at Ews (tarray tuint c) (vb init) po;
             data_at Ews (tarray tuint c) (sublist 0 i (vb init) ++ Zrepeat Vundef (c - i)) ps;
             data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
             PunySpec.puny_consts gv; mem_mgr gv; TT))
      continue: (EX i: Z,
        PROP (0 <= i < c)
        LOCAL (temp _i (Vint (Int.repr i)); temp _saved ps; temp _out po; temp _cap (Vint (Int.repr c));
               temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
               lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
        SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at Ews (tarray tuint c) (vb init) po;
             data_at Ews (tarray tuint c) (sublist 0 (i + 1) (vb init) ++ Zrepeat Vundef (c - (i + 1))) ps;
             data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
             PunySpec.puny_consts gv; mem_mgr gv; TT))
      break: (
        PROP ()
        LOCAL (temp _saved ps; temp _out po; temp _cap (Vint (Int.repr c));
               temp _input pi; temp _len (Vlong (Int64.repr (Zlength bs))); gvars gv;
               lvar _count tuint vc; lvar _exact_count tuint ve; lvar _fewer_count tuint vf)
        SEP (arr0 Ews tuchar (Zlength bs) (vb bs) pi; data_at Ews (tarray tuint c) (vb init) po;
             data_at Ews (tarray tuint c) (vb init) ps;
             data_at_ Tsh tuint vc; data_at_ Tsh tuint ve; data_at_ Tsh tuint vf;
             PunySpec.puny_consts gv; mem_mgr gv; TT)).
    + Exists 0. entailer!. autorewrite with sublist. cancel.
    + Intros i.
      forward_if.
      * forward.
        { entailer!. unfold vb. rewrite Znth_map by lia. simpl; auto. }
        forward. Exists i. entailer!.
        replace (upd_Znth i (sublist 0 i (vb init) ++ Zrepeat Vundef (Zlength init - i)) (Znth i (vb init)))
          with (sublist 0 (i + 1) (vb init) ++ Zrepeat Vundef (Zlength init - (i + 1))) by list_solve.
        cancel.
      * forward. entailer!. replace i with (Zlength init) by lia.
        autorewrite with sublist. rewrite sublist_same; [cancel | auto | unfold vb; rewrite Zlength_map; auto].
    + Intros i. forward. Exists (i + 1). entailer!.
    + unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
      eapply semax_pre; [ | apply (H7 Espec gv vc ve vf bs pi c init po ps) ]. unfold pre7, lvars3.
      replace (arr0 Ews tuint c (vb init)) with (data_at Ews (tarray tuint c) (vb init))
        by (unfold arr0; destruct (Z.eq_dec c 0); [contradiction | reflexivity]).
      entailer!.
Qed.
