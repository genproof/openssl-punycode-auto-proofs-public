(* Piece 12 of the main of harness/api_a2ulabel_size.c (AszMainDefs): size = 0, the loop to the first NUL of big
   (the octets w' that the first call wrote before its NUL are all nonzero, and they fit in biglen), size++. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.harness.api_a2ulabel_size.code.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszProg.
Require Import OpensslPunycode.proof.laws.api_a2ulabel_size.AszMainDefs.
Local Open Scope logic.

(* The octet of big at a position up to its first NUL. *)
Lemma big_at (w': list Z) (tb: list val) i:
  0 <= i <= Zlength w' -> Znth i (vb (w' ++ [0]) ++ tb) = Vint (Int.repr (Znth i (w' ++ [0]))).
Proof.
  intros. rewrite app_Znth1 by (unfold vb; list_solve). unfold vb. rewrite Znth_map by list_solve. reflexivity.
Qed.

Lemma big_octet (w': list Z) i:
  Forall (fun b => 1 <= b <= 255) w' -> 0 <= i <= Zlength w' ->
  0 <= Znth i (w' ++ [0]) <= 255 /\ (Znth i (w' ++ [0]) = 0 <-> i = Zlength w').
Proof.
  intros F Hi. destruct (Z.eq_dec i (Zlength w')) as [-> | N].
  - rewrite app_Znth2 by lia. rewrite Z.sub_diag, Znth_0_cons. split; [ lia | tauto ].
  - rewrite app_Znth1 by lia. rewrite Forall_forall in F.
    specialize (F (Znth i w') ltac:(apply Znth_In; lia)). lia.
Qed.

Lemma piece12 : piece15_stmt -> piece12_stmt.
Proof.
  intros H15 Espec gv biglen pbig w' tb outlen pout ov r.
  unfold pre12, T12, ret0, main_post, Delta_main. abbreviate_semax.
  Intros. pose proof (Zlength_nonneg w').
  forward.
  forward_loop (EX i: Z,
    PROP (0 <= i <= Zlength w')
    LOCAL (temp _size (Vlong (Int64.repr i)); temp _r (Vint (Int.repr r)); temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig; temp _biglen (Vlong (Int64.repr biglen));
           gvars gv)
    SEP (data_at Ews (tarray tuchar biglen) (vb (w' ++ [0]) ++ tb) pbig;
         data_at Ews (tarray tuchar outlen) ov pout; TT))
  break: (
    PROP ()
    LOCAL (temp _size (Vlong (Int64.repr (Zlength w'))); temp _r (Vint (Int.repr r)); temp _out pout;
           temp _outlen (Vlong (Int64.repr outlen)); temp _big pbig; temp _biglen (Vlong (Int64.repr biglen));
           gvars gv)
    SEP (data_at Ews (tarray tuchar biglen) (vb (w' ++ [0]) ++ tb) pbig;
         data_at Ews (tarray tuchar outlen) ov pout; TT)).
  { Exists 0. entailer!. }
  { Intros i. destruct (big_octet w' i H0 H5) as [Hb Hz].
    forward_if (temp _t'13 (Vint (Int.repr (if Z.eq_dec i (Zlength w') then 0 else 1)))).
    - forward.
      { entailer!. rewrite big_at by lia. simpl. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      rewrite big_at by lia.
      forward. entailer!.
      destruct (Z.eq_dec i (Zlength w')) as [E | E].
      + rewrite (proj2 Hz E). reflexivity.
      + destruct (zeq (Znth i (w' ++ [0])) 0) as [Z0 | Z0]; [ exfalso; apply E; apply Hz; exact Z0 | reflexivity ].
    - lia.
    - forward_if.
      + forward. Exists (i + 1). entailer!.
        destruct (Z.eq_dec i (Zlength w')); lia.
      + forward. entailer!.
        destruct (Z.eq_dec i (Zlength w')); [ subst; auto | discriminate ].
  }
  forward.
  eapply semax_pre; [ | apply (H15 Espec gv biglen pbig w' tb outlen pout ov r) ].
  unfold pre15. entailer!.
Qed.
