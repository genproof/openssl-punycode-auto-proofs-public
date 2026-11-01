(* Piece A of the main of harness/rfc_samples.c: the body of the loop for sample s (RsmMainDefs.iter_stmt): the
   length of the literal (the loop up to its NUL), out = any_uints(points[s]) and its NULL test; the rest is
   piece B. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.harness.rfc_samples.code.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmProg.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmModel.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainDefs.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainLib.
Require Import OpensslPunycode.proof.laws.rfc_samples.RsmMainB.
Local Open Scope logic.

(* The data of the samples stay folded (entailer! would unfold them). *)
Opaque pts dec enc lit_ids start expected.

Lemma iter_piece : iter_stmt.
Proof.
  intros Espec gv vc s H.
  unfold iter_pre, iter_post, iter_next, main_post, Delta_main, loop_body. abbreviate_semax.
    destruct (sample_facts s H) as (Hlit & Hb & Hl & Hd).
    pose proof (Znth_pts_range s H) as Hk. pose proof (start_bound s H) as Hst.
    assert (Hp: Znth s (map gv lit_ids) = gv (Znth s lit_ids))
      by (apply Znth_map; rewrite Zlength_lit_ids; lia).
    rewrite (lits_split gv s H). unfold encoded_at, points_at. Intros.
    remember (gv (Znth s lit_ids)) as pl eqn:Epl.
    assert (Hpl: lit gv s = data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl)
      by (rewrite Epl; reflexivity).
    clear Epl. rewrite Hpl.
    forward.
    forward_loop (EX len: Z,
      PROP (0 <= len <= Zlength (enc s))
      LOCAL (temp _len (Vlong (Int64.repr len)); temp _s (Vint (Int.repr s));
             temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
      SEP (data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl;
           lits_but gv s; data_at Ers (tarray (tptr tschar) 19) (map gv lit_ids) (gv _encoded);
           data_at Ers (tarray tuchar 19) (vb pts) (gv _points); decoded_at gv; data_at_ Tsh tuint vc;
           OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT))
    break: (
      PROP ()
      LOCAL (temp _len (Vlong (Int64.repr (Zlength (enc s)))); temp _s (Vint (Int.repr s));
             temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
      SEP (data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl;
           lits_but gv s; data_at Ers (tarray (tptr tschar) 19) (map gv lit_ids) (gv _encoded);
           data_at Ers (tarray tuchar 19) (vb pts) (gv _points); decoded_at gv; data_at_ Tsh tuint vc;
           OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
    { Exists 0. entailer!. }
    { Intros len.
      forward.
      match goal with |- context [temp _t'13 ?x] => replace x with pl by (rewrite <- Hp; reflexivity) end.
      assert (Hz: Znth len (vb (enc s ++ [0])) = Vint (Int.repr (Znth len (enc s ++ [0])))).
      { unfold vb. rewrite Znth_map by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia). reflexivity. }
      assert (Hnz: len < Zlength (enc s) -> 0 < Znth len (enc s ++ [0]) < 128).
      { intros Hlt. rewrite app_Znth1 by lia. rewrite Forall_forall in Hb. apply Hb. apply Znth_In. lia. }
      assert (He: len = Zlength (enc s) -> Znth len (enc s ++ [0]) = 0).
      { intros ->. rewrite app_Znth2 by lia. rewrite Z.sub_diag. reflexivity. }
      forward.
      { entailer!.
        match goal with |- context [is_int _ _ ?x] => replace x with (Vint (Int.repr (Znth len (enc s ++ [0]))))
          by (rewrite <- Hz; reflexivity) end.
        destruct (zlt len (Zlength (enc s))).
        - specialize (Hnz l). simpl. rewrite Int.signed_repr by rep_lia. rep_lia.
        - rewrite He by lia. simpl. rewrite Int.signed_repr by rep_lia. rep_lia. }
      match goal with |- context [temp _t'14 ?x] => replace x with (Vint (Int.repr (Znth len (enc s ++ [0]))))
        by (rewrite <- Hz; reflexivity) end.
      forward_if.
      { assert (len < Zlength (enc s)) by (destruct (Z.eq_dec len (Zlength (enc s))); [ specialize (He e); lia | lia ]).
        forward. Exists (len + 1). entailer!. }
      { assert (len = Zlength (enc s)) by (destruct (zlt len (Zlength (enc s))); [ specialize (Hnz l); lia | lia ]).
        subst len. forward. entailer!. }
    }
    remember (Znth s pts) as k eqn:Ek.
    assert (Hpk: Znth s (vb pts) = Vint (Int.repr k)) by (subst k; unfold vb; rewrite Znth_map by (rewrite Zlength_pts; lia); reflexivity).
    forward.
    { match goal with |- context [tc_val _ ?x] => replace x with (Vint (Int.repr k))
        by (rewrite <- Hpk; reflexivity) end.
      entailer!; try (simpl; rep_lia). }
    match goal with |- context [temp _t'12 ?x] => replace x with (Vint (Int.repr k)) by (rewrite <- Hpk; reflexivity) end.
    forward_call (k, gv).
    Intros vr. destruct vr as [po vs]. simpl fst in *; simpl snd in *.
    forward.
    sep_apply (@split_block C.CS tuint k (vb vs) po eq_refl). Intros.
    forward_if (PROP (po <> nullval)
      LOCAL (temp _out po; temp _len (Vlong (Int64.repr (Zlength (enc s)))); temp _s (Vint (Int.repr s));
             temp _at (Vlong (Int64.repr (start s))); gvars gv; lvar _count tuint vc)
      SEP (@mtok C.CS tuint k po; @marr C.CS tuint k (vb vs) po;
           data_at Ers (tarray tschar (Zlength (enc s) + 1)) (vb (enc s ++ [0])) pl;
           lits_but gv s; data_at Ers (tarray (tptr tschar) 19) (map gv lit_ids) (gv _encoded);
           data_at Ers (tarray tuchar 19) (vb pts) (gv _points); decoded_at gv; data_at_ Tsh tuint vc;
           OpensslPunycode.proof.punycode.PunySpec.puny_consts gv; mem_mgr gv; TT)).
    { match goal with |- context [@marr _ ?t ?n ?v po] =>
        apply derives_trans with (@mtok C.CS t n po * @marr C.CS t n v po * TT)%logic end;
        [ cancel | apply block_tc_test; [ intros; simpl; lia | simpl; lia | lia ] ]. }
    { forward. Exists (Int.repr 0). entailer!. }
    { forward. entailer!. }
    Intros. unfold mtok, marr. rewrite !if_false by assumption.
    subst k.
    eapply semax_pre; [ | apply (pieceB Espec gv vc s pl po vs H H2 H0 H1 Hp Hpl) ].
    unfold preB. entailer!.
Qed.
