(* Piece 6 of the main of harness/x_a2ulabel.c: the input string and its copy (MainDefs). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.shim.ShimSpec.
Require OpensslPunycode.proof.punycode.PunySpec.
Require OpensslPunycode.proof.harness.RefRt.
Require OpensslPunycode.proof.harness.RefA2u.
Require Import OpensslPunycode.harness.x_a2ulabel.code.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uProg.
Require Import OpensslPunycode.proof.harness.a2ulabel.A2uMainDefs.
(* QuickProof's nondet_bytes takes buf = NULL when n = 0; here buf is a pointer (isptr, or a field_compatible
   fact), so the specification's conditional pre- and postcondition are their non-NULL branch. *)
Ltac nonnull_tac := let H := fresh in intro H;
  first [ assumption
        | match goal with Hp: ?p <> nullval |- _ => rewrite H in Hp; contradiction end
        | match goal with Hp: isptr ?p |- _ => rewrite H in Hp; simpl in Hp; contradiction end
        | match goal with Hp: field_compatible _ _ ?p |- _ =>
            rewrite H in Hp; destruct Hp as [Hp _]; simpl in Hp; contradiction end ].

Lemma merge_last sh n (l: list val) p:
  0 <= n -> Zlength l = n ->
  (data_at sh (tarray tuchar n) l p *
   data_at_ sh (Tarray tuchar 1 noattr) (field_address0 (Tarray tuchar (n + 1) noattr) (SUB n) p))%logic
  |-- data_at sh (tarray tuchar (n + 1)) (l ++ [Vundef]) p.
Proof.
  intros. rewrite (split2_data_at_Tarray_app n (n + 1) sh tuchar l [Vundef] p) by (auto; list_solve).
  replace (n + 1 - n) with 1 by lia. rewrite data_at__eq. apply derives_refl.
Qed.

Lemma data_at_arr0_nz6 (cs1 cs2: compspecs) sh n v p:
  n <> 0 -> @data_at cs1 sh (tarray tuchar n) v p = @arr0 cs2 sh tuchar n v p.
Proof. intros. unfold arr0. rewrite if_false by auto. apply data_at_tuchar_cs. Qed.

Lemma piece6 {Espec: OracleKind} gv v_k n pin psnap pcps:
  (forall bs, semax Delta_main (pre10 gv v_k n bs pin psnap pcps) (Ssequence T10 ret0) main_post) ->
  semax Delta_main (pre6 gv v_k n pin psnap pcps) (Ssequence T6 ret0) main_post.
Proof.
  intros H10. unfold pre6, T6, ret0, main_post, Delta_main. abbreviate_semax.
  Intros.
  assert_PROP (field_compatible (tarray tuchar (n + 1)) [] pin) as FCin by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Ews (n + 1) n pin) by (auto; lia).
  replace (n + 1 - n) with 1 by lia.
  change (Tarray tuchar n noattr) with (tarray tuchar n). Intros.
  forward_call (pin, n, Ews).
  { rewrite if_false by nonnull_tac. cancel. }
  Intros bs. rewrite if_false by nonnull_tac.
  sep_apply (merge_last Ews n (map (fun b : Z => Vint (Int.repr b)) bs) pin); [ lia | list_solve | ].
  forward.
  replace (upd_Znth n (map (fun b : Z => Vint (Int.repr b)) bs ++ [Vundef]) (Vint (Int.zero_ext 8 (Int.repr 0))))
    with (vb (bs ++ [0])).
  2: { unfold vb. rewrite map_app. change (Int.zero_ext 8 (Int.repr 0)) with (Int.repr 0). simpl. list_solve. }
  rewrite (data_at__tarray Ews tuchar (n + 1)).
  replace (n + 1) with (Zlength (bs ++ [0])) by list_solve.
  rewrite !(data_at_arr0_nz6 CS OpensslPunycode.proof.harness.RefRt.CS) by list_solve.
  forward_call (Ews, psnap, Zrepeat (default_val tuchar) (Zlength (bs ++ [0])), Ews, pin, bs ++ [0]).
  { entailer!. rewrite Zlength_app, Zlength_cons, Zlength_nil. simpl. reflexivity. }
  { split; [ | split ].
    - unfold bytes_ok; rewrite Forall_app; split; auto; repeat constructor; rep_lia.
    - list_solve.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl; rep_lia. }
  rewrite <- !(data_at_arr0_nz6 CS OpensslPunycode.proof.harness.RefRt.CS) by list_solve.
  replace (Zlength (bs ++ [0])) with (n + 1) by list_solve.
  forward.
  eapply semax_pre; [ | apply (H10 bs) ].
  unfold pre10, in_ok. entailer!.
Qed.
