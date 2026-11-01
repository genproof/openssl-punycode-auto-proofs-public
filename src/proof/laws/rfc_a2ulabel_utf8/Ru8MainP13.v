(* A piece of the main of harness/rfc_a2ulabel_utf8.c (Ru8MainDefs): the loop of gp_assume(label[i] != '.' &&
   label[i] != 0) over the octets of s. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_a2ulabel_utf8.code.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Prog.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8Model.
Require Import OpensslPunycode.proof.laws.rfc_a2ulabel_utf8.Ru8MainDefs.

(* The octet label[i] of the buffer "xn--" ++ s ++ NUL, for i in the range of s: the octet i - 4 of s.  Stated
   for any Inhabitant of val, the one a load leaves in LOCAL. *)
Lemma ru8p13_znth {d: Inhabitant val} (s: list Z) (i: Z) :
  4 <= i < Zlength s + 4 -> @Znth val d i (vb (xn ++ s ++ [0])) = Vint (Int.repr (Znth (i - 4) s)).
Proof.
  intros Hi. unfold Znth. rewrite if_false by lia. rewrite if_false by lia.
  unfold vb. rewrite map_app. rewrite app_nth2 by (rewrite length_map; unfold xn; simpl; lia).
  rewrite length_map. change (length xn) with 4%nat.
  replace (Z.to_nat i - 4)%nat with (Z.to_nat (i - 4)) by lia.
  rewrite map_app, app_nth1 by (rewrite length_map; rewrite Zlength_correct in Hi; lia).
  rewrite nth_map' with (d' := 0) by (rewrite Zlength_correct in Hi; lia). reflexivity.
Qed.

(* Statement 13, the loop over i in [4, len + 4): each turn gp_assume's postcondition adds that octet i - 4 of s is
   neither '.' nor NUL, so the invariant holds for the prefix of s already seen; at the end for all of s, which is
   the precondition of the next piece. *)
Lemma piece13 : piece14_stmt -> piece13_stmt.
Proof.
  intros H14 Espec gv vc len s pl pc outlen ob pout psaved pw. unfold pre13, T13, ret0, main_post, Delta_main.
  abbreviate_semax.
  Intros.
  forward_for_simple_bound (len + 4)
    (EX i: Z, PROP (Forall (fun c => c <> 46 /\ c <> 0) (sublist 0 (i - 4) s))
      LOCAL (temp _want pw; temp _saved psaved; temp _out pout; temp _outlen (Vlong (Int64.repr outlen));
         temp _cps pc; temp _label pl; temp _len (Vlong (Int64.repr len)); gvars gv; lvar _count tuint vc)
      SEP (data_at Ews (tarray tuchar (len + 5)) (vb (xn ++ s ++ [0])) pl;
       data_at Ews (tarray tuint 512) (Zrepeat Vundef 512) pc;
       data_at Ews (tarray tuchar outlen) (vb ob) pout; data_at Ews (tarray tuchar outlen) (vb ob) psaved;
       data_at Ews (tarray tuchar 2049) (Zrepeat Vundef 2049) pw;
       data_at_ Tsh tuint vc; mem_mgr gv; OpensslPunycode.proof.punycode.PunySpec.puny_consts gv;
       OpensslPunycode.proof.punycode.PunySpec.xn_lit gv; OpensslPunycode.proof.shim.ShimSpec.shim_state gv 0 0 0;
       TT)).
  - entailer!.
  - assert (Hc: 0 <= Znth (i - 4) s <= 255)
      by (unfold bytes_ok in H1; rewrite Forall_Znth in H1; apply H1; lia).
    forward.
    { rewrite ru8p13_znth by lia. entailer!. simpl. try rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    rewrite ru8p13_znth by lia.
    forward_if (temp _t'13 (Vint (Int.repr
      (if Z.eq_dec (Znth (i - 4) s) 46 then 0 else if Z.eq_dec (Znth (i - 4) s) 0 then 0 else 1)))).
    + forward.
      { rewrite ru8p13_znth by lia. entailer!. all: simpl; try rewrite Int.unsigned_repr by rep_lia; rep_lia. }
      rewrite ru8p13_znth by lia.
      forward.
      entailer!. rewrite if_false by auto.
      destruct (zeq (Znth (i - 4) s) 0), (Z.eq_dec (Znth (i - 4) s) 0); try contradiction; reflexivity.
    + forward. rewrite if_true by auto. entailer!.
    + forward_call (Int.repr
        (if Z.eq_dec (Znth (i - 4) s) 46 then 0 else if Z.eq_dec (Znth (i - 4) s) 0 then 0 else 1)).
      Intros.
      assert (Hn: Znth (i - 4) s <> 46 /\ Znth (i - 4) s <> 0).
      { destruct (Z.eq_dec (Znth (i - 4) s) 46); [ contradiction H8; reflexivity | ].
        destruct (Z.eq_dec (Znth (i - 4) s) 0); [ contradiction H8; reflexivity | auto ]. }
      entailer!.
      replace (i + 1 - 4) with (i - 4 + 1) by lia.
      rewrite (sublist_split 0 (i - 4) (i - 4 + 1)) by lia. rewrite sublist_len_1 by lia.
      apply Forall_app; split; auto.
  - Intros. replace (len + 4 - 4) with (Zlength s) in H6 by lia. rewrite sublist_same in H6 by lia.
    unfold abbreviate in Delta, POSTCONDITION, MORE_COMMANDS; subst Delta POSTCONDITION MORE_COMMANDS.
    eapply semax_pre; [ | apply (H14 Espec gv vc len s pl pc outlen ob pout psaved pw) ].
    unfold pre14. entailer!.
Qed.
