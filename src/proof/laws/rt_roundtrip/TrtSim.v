(* The decoder follows the encoder for any number of code points, each any unsigned int (the simulation of
   Roundtrip.sim_pass / sim_rounds without their bounds of 512 code points <= 0x10FFFF).  At each delta the decoder
   either reads it back and stays in step with the encoder, or its digit loop overflows (the insertion state
   i + delta exceeds maxint) and it fails; the overflow needs (largest - 127) * m > 2^32, m the number of code
   points.  Hence the decoder's result is the input back, or a failure beyond that bound. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.RtDigits.
Require Import OpensslPunycode.proof.model.Roundtrip.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtModelStmt.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtDigits.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fold_max_ge : forall l acc,
  acc <= fold_left Z.max l acc /\ (forall x, In x l -> x <= fold_left Z.max l acc).
Proof.
  induction l as [|y l IH]; intros acc; simpl; [split; [lia | intros; contradiction]|].
  destruct (IH (Z.max acc y)) as [A B]. split; [lia|].
  intros x [Hx|Hx]; [subst; lia | auto].
Qed.

Lemma largest_ge : forall l x, In x l -> x <= largest l.
Proof. intros. apply (proj2 (fold_max_ge l 0)); auto. Qed.

(* The encoder's bias stays at most 215 (adapt_bound), from its initial 72. *)
Lemma pass_bias : forall l mm delta bias h b out delta' bias' h' out',
  enc_pass l mm delta bias h b out = Some (delta', bias', h', out') -> 0 <= delta <= maxint -> 0 <= h ->
  bias <= 215 -> bias' <= 215.
Proof.
  induction l as [|c l IH]; intros mm delta bias h b out delta' bias' h' out' H Hd Hh Hb;
    [rewrite enc_pass_nil in H | rewrite enc_pass_cons in H].
  - inv H. auto.
  - destruct (c <? mm) eqn:E1.
    + destruct (maxint <? delta + 1) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
      eapply IH; [exact H | lia | lia | auto].
    + destruct (c =? mm) eqn:E3.
      * eapply IH; [exact H | unfold maxint; lia | lia |]. apply adapt_bound; lia.
      * eapply IH; [exact H | lia | lia | auto].
Qed.

Section Sim.
Variable cps : list Z.
Variable e : list Z.
Variable cap b : Z.
Context (Hcps : Forall (fun c => 0 <= c <= maxint) cps).
Context (Hcap : Zlength cps <= cap).

(* The bound of the law, under which the decoder never overflows. *)
Definition sim_bound : Prop := (largest cps - 127) * Zlength cps <= 2 ^ 32.

(* What the decoder gives: the code points back, or a failure, the latter only beyond the bound. *)
Definition sim_good (res : bool * list Z) : Prop := res = (true, cps) \/ (fst res = false /\ ~ sim_bound).

(* The decoder through one pass of the encoder for the code point mm: in step with it (the invariant of
   Roundtrip.sim_pass, with n_dec >= 128), or failed beyond the bound. *)
Lemma sim_pass_any : forall mm, mm <= maxint -> In mm cps ->
  forall l pre delta bias h out delta' bias' h' out' n_dec i_dec,
  cps = pre ++ l ->
  enc_pass l mm delta bias h b out = Some (delta', bias', h', out') ->
  (exists r, e = out' ++ r) ->
  h = Zlength (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) l) ->
  delta + i_dec = (mm - n_dec) * (h + 1) + Zlength (filter (fun c => c <=? mm) pre) ->
  0 <= delta <= maxint -> 128 <= n_dec <= mm -> bias <= 215 ->
  (h = b /\ i_dec = 0 \/ b < h /\ 1 <= i_dec) ->
  (exists n_dec' i_dec',
    (forall fd, steps e (Z.to_nat (h' - h) + fd) cap (Zlength out) n_dec i_dec bias
                  (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) l)
                = steps e fd cap (Zlength out') n_dec' i_dec' bias' (filter (fun c => c <=? mm) cps)) /\
    delta' + i_dec' = (mm - n_dec') * (h' + 1) + h' /\ 128 <= n_dec' <= mm /\
    (h' = b /\ i_dec' = 0 \/ b < h' /\ 1 <= i_dec')) \/
  (~ sim_bound /\
   forall fd, fst (steps e (Z.to_nat (h' - h) + fd) cap (Zlength out) n_dec i_dec bias
                     (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) l)) = false).
Proof.
  intros mm Hmm Hin.
  induction l as [|c l IH];
    intros pre delta bias h out delta' bias' h' out' n_dec i_dec Hc Hp He Hh Hi Hd Hn Hbias Hb.
  - rewrite enc_pass_nil in Hp. inv Hp. left. exists n_dec, i_dec.
    rewrite app_nil_r in *. cbn [filter] in *. try rewrite app_nil_r in *.
    split; [intros fd; rewrite Z.sub_diag, Hc; reflexivity|]. split; [lia|]. split; auto.
  - rewrite enc_pass_cons in Hp.
    set (cnt := Zlength (filter (fun c => c <=? mm) pre)) in *.
    assert (Hcnt: 0 <= cnt <= h) by (subst cnt; rewrite Hh, Zlength_app; pose proof (Zlength_nonneg (filter (fun c => c <? mm) (c :: l))); pose proof (Zlength_nonneg (filter (fun c => c <=? mm) pre)); lia).
    destruct (c <? mm) eqn:E1.
    + destruct (maxint <? delta + 1) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
      assert (Heq: filter (fun c => c <=? mm) (pre ++ [c]) ++ filter (fun c => c <? mm) l
                   = filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) (c :: l)).
      { rewrite filter_app, <- app_assoc. cbn [filter]. rewrite E1.
        rewrite (proj2 (Z.leb_le c mm)) by (apply Z.ltb_lt in E1; lia). reflexivity. }
      assert (P1: cps = (pre ++ [c]) ++ l) by (rewrite Hc, <- app_assoc; reflexivity).
      assert (P2: h = Zlength (filter (fun c => c <=? mm) (pre ++ [c]) ++ filter (fun c => c <? mm) l))
        by (rewrite Heq; auto).
      assert (P3: delta + 1 + i_dec = (mm - n_dec) * (h + 1) + Zlength (filter (fun c => c <=? mm) (pre ++ [c]))).
      { rewrite filter_app, Zlength_app. cbn [filter].
        rewrite (proj2 (Z.leb_le c mm)) by (apply Z.ltb_lt in E1; lia). rewrite Zlength_cons, Zlength_nil.
        subst cnt. lia. }
      destruct (IH (pre ++ [c]) (delta + 1) bias h out delta' bias' h' out' n_dec i_dec P1 Hp He P2 P3
                  ltac:(lia) Hn Hbias Hb) as [[n1 [i1 [S1 R1]]]|[NB S1]].
      * left. exists n1, i1. rewrite <- Heq. split; auto.
      * right. rewrite <- Heq. split; auto.
    + destruct (c =? mm) eqn:E3.
      * apply Z.eqb_eq in E3; subst c.
        set (ds := enc_digits 64 delta 36 bias) in *.
        pose proof Hp as Hp'.
        apply pass_shape in Hp'; [|unfold maxint; lia]. destruct Hp' as [A [B [r1 [C [D F]]]]].
        destruct He as [r He].
        assert (Heq: filter (fun c => c <=? mm) (pre ++ [mm]) ++ filter (fun c => c <? mm) l
                     = insert_at cnt mm (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) (mm :: l))).
        { rewrite filter_app, <- app_assoc. cbn [filter]. rewrite Z.leb_refl, Z.ltb_irrefl.
          subst cnt; rewrite insert_at_app; reflexivity. }
        assert (Hh1: h + 1 = Zlength (filter (fun c => c <=? mm) (pre ++ [mm]) ++ filter (fun c => c <? mm) l)).
        { rewrite Heq. unfold insert_at. cbn [filter] in Hh |- *. rewrite Z.ltb_irrefl in *. list_solve. }
        assert (P1: cps = (pre ++ [mm]) ++ l) by (rewrite Hc, <- app_assoc; reflexivity).
        assert (P3: 0 + (cnt + 1) = (mm - mm) * (h + 1 + 1) + Zlength (filter (fun c => c <=? mm) (pre ++ [mm]))).
        { rewrite filter_app, Zlength_app. cbn [filter]. rewrite Z.leb_refl, Zlength_cons, Zlength_nil.
          subst cnt; lia. }
        assert (Hlt: h < Zlength cps).
        { rewrite Hc, Hh, !Zlength_app. cbn [filter]. rewrite Z.ltb_irrefl, Zlength_cons.
          pose proof (Zlength_filter_le (fun c => c <=? mm) pre).
          pose proof (Zlength_filter_le (fun c => c <? mm) l). lia. }
        assert (He2: e = out ++ ds ++ r1 ++ r) by (rewrite He, C, <- !app_assoc; reflexivity).
        pose proof (digits_enc_digits_any out (r1 ++ r) delta bias i_dec ltac:(lia) ltac:(lia) Hbias) as Hdg.
        cbv zeta in Hdg. fold ds in Hdg. rewrite <- He2 in Hdg.
        pose proof (enc_digits_nonnil 64 delta 36 bias) as Hds. fold ds in Hds.
        assert (Hnot: Zlength e <=? Zlength out = false)
          by (apply Z.leb_gt; rewrite He2, !Zlength_app; pose proof (Zlength_nonneg (r1 ++ r)); list_solve).
        assert (Hfuel: forall fd, (Z.to_nat (h' - h) + fd)%nat = S (Z.to_nat (h' - (h + 1)) + fd)%nat)
          by (intros; pose proof (Zlength_nonneg (filter (fun c => c =? mm) l)); lia).
        destruct (Z.leb_spec (i_dec + delta) maxint) as [Hfit|Hover].
        -- assert (Hstep: forall fd,
              steps e (S fd) cap (Zlength out) n_dec i_dec bias
                (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) (mm :: l))
              = steps e fd cap (Zlength (out ++ ds)) mm (cnt + 1) (adapt delta (h + 1) (h =? b))
                (filter (fun c => c <=? mm) (pre ++ [mm]) ++ filter (fun c => c <? mm) l)).
           { intros fd. rewrite steps_S, Hnot, Hdg. rewrite <- Hh.
             assert (Hdiv: (i_dec + delta) / (h + 1) = mm - n_dec)
               by (apply Zdiv_unique with cnt; lia).
             assert (Hmod: (i_dec + delta) mod (h + 1) = cnt)
               by (apply Zmod_unique with (mm - n_dec); lia).
             cbv zeta. rewrite Hdiv, Hmod.
             replace (n_dec + (mm - n_dec)) with mm by lia.
             rewrite (proj2 (Z.ltb_ge maxint mm)) by lia.
             rewrite (proj2 (Z.leb_gt cap h)) by lia.
             replace (i_dec + delta - i_dec) with delta by lia.
             replace (i_dec =? 0) with (h =? b)
               by (destruct Hb as [[-> ->]|[Hb1 Hb2]]; [rewrite !Z.eqb_refl; auto
                   | rewrite (proj2 (Z.eqb_neq h b)), (proj2 (Z.eqb_neq i_dec 0)) by lia; auto]).
             rewrite <- Heq, Zlength_app. reflexivity. }
           destruct (IH (pre ++ [mm]) 0 (adapt delta (h + 1) (h =? b)) (h + 1) (out ++ ds) delta' bias' h' out'
                        mm (cnt + 1) P1 Hp (ex_intro _ r He) Hh1 P3 ltac:(unfold maxint; lia) ltac:(lia)
                        ltac:(apply adapt_bound; lia) ltac:(right; lia)) as [[n1 [i1 [S1 R1]]]|[NB S1]].
           ++ left. exists n1, i1. split; [|exact R1].
              intros fd. rewrite Hfuel, Hstep. apply S1.
           ++ right. split; auto. intros fd. rewrite Hfuel, Hstep. apply S1.
        -- right. split.
           ++ intros HB. unfold sim_bound in HB.
              assert (Hmax: mm <= largest cps) by (apply largest_ge; auto).
              assert ((mm - n_dec) * (h + 1) <= (largest cps - 128) * Zlength cps)
                by (apply Z.mul_le_mono_nonneg; lia).
              unfold maxint in Hover. nia.
           ++ intros fd. rewrite Hfuel, steps_S, Hnot, Hdg. reflexivity.
      * assert (Heq: filter (fun c => c <=? mm) (pre ++ [c]) ++ filter (fun c => c <? mm) l
                   = filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) (c :: l)).
        { rewrite filter_app, <- app_assoc. cbn [filter]. rewrite E1.
          apply Z.ltb_ge in E1. apply Z.eqb_neq in E3.
          rewrite (proj2 (Z.leb_gt c mm)) by lia. reflexivity. }
        assert (P1: cps = (pre ++ [c]) ++ l) by (rewrite Hc, <- app_assoc; reflexivity).
        assert (P2: h = Zlength (filter (fun c => c <=? mm) (pre ++ [c]) ++ filter (fun c => c <? mm) l))
          by (rewrite Heq; auto).
        assert (P3: delta + i_dec = (mm - n_dec) * (h + 1) + Zlength (filter (fun c => c <=? mm) (pre ++ [c]))).
        { rewrite filter_app, Zlength_app. cbn [filter].
          apply Z.ltb_ge in E1. apply Z.eqb_neq in E3.
          rewrite (proj2 (Z.leb_gt c mm)) by lia. rewrite Zlength_nil.
          subst cnt. lia. }
        destruct (IH (pre ++ [c]) delta bias h out delta' bias' h' out' n_dec i_dec P1 Hp He P2 P3
                    Hd Hn Hbias Hb) as [[n1 [i1 [S1 R1]]]|[NB S1]].
        -- left. exists n1, i1. rewrite <- Heq. split; auto.
        -- right. rewrite <- Heq. split; auto.
Qed.

(* The decoder through the remaining rounds of the encoder: the code points back, or a failure beyond the bound. *)
Lemma sim_rounds_any : forall f n delta bias h out n_dec i_dec,
  enc_rounds cps f n delta bias h b out = Some e ->
  h = Zlength (filter (fun c => c <? n) cps) ->
  delta + i_dec = (n - n_dec) * (h + 1) -> 0 <= delta -> 128 <= n_dec <= n -> bias <= 215 ->
  (h = b /\ i_dec = 0 \/ b < h /\ 1 <= i_dec) ->
  forall fd, Zlength cps - h <= Z.of_nat fd ->
  sim_good (steps e fd cap (Zlength out) n_dec i_dec bias (filter (fun c => c <? n) cps)).
Proof.
  induction f; intros n delta bias h out n_dec i_dec H Hh Hi Hd Hn Hbias Hb fd Hfd; [discriminate|].
  pose proof H as Hsh. apply rounds_shape in Hsh; auto. destruct Hsh as [r0 [He0 _]].
  rewrite enc_rounds_S in H; cbv zeta in H.
  destruct (Zlength cps <=? h) eqn:Eh.
  - inv H. apply Z.leb_le in Eh. left.
    assert (filter (fun c => c <? n) cps = cps) by (apply filter_all; lia).
    destruct fd; [simpl; congruence|]. rewrite steps_S, Z.leb_refl. congruence.
  - apply Z.leb_gt in Eh.
    destruct ((maxint <? delta) || ((maxint - delta) / (h + 1) <? min_ge cps n - n)) eqn:Ec; [discriminate|].
    apply orb_false_iff in Ec; destruct Ec as [Ec1 Ec2]; apply Z.ltb_ge in Ec1; apply Z.ltb_ge in Ec2.
    rewrite Hh in Eh. destruct (filter_lt_exists n cps Eh) as [c [Hc Hnc]].
    pose proof Hcps as Hcps2. rewrite Forall_forall in Hcps2.
    destruct (min_ge_spec cps n c Hc Hnc ltac:(specialize (Hcps2 c Hc); lia)) as [M1 [M2 M3]].
    rewrite <- Hh in Eh.
    set (mm := min_ge cps n) in *.
    assert (0 <= h) by (rewrite Hh; apply Zlength_nonneg).
    assert (Hbd: (mm - n) * (h + 1) <= maxint - delta).
    { pose proof (Z.mul_div_le (maxint - delta) (h + 1) ltac:(lia)). nia. }
    destruct (enc_pass cps mm (delta + (mm - n) * (h + 1)) bias h b out) as [[[[d1 b1] h1] o1]|] eqn:Ep;
      [|discriminate].
    pose proof Ep as Ep'. apply pass_shape in Ep'; [|nia]. destruct Ep' as [A [B [r1 [C [D F]]]]].
    assert (Hb1: b1 <= 215) by (eapply pass_bias; [exact Ep | nia | lia | auto]).
    assert (Hh1: h1 = Zlength (filter (fun c => c <? mm + 1) cps)).
    { rewrite B, Hh, <- filter_le_lt, filter_le_count, (filter_lt_eq n mm); auto. }
    pose proof H as Hsh. apply rounds_shape in Hsh; [|auto|auto|lia]. destruct Hsh as [r2 [He2 _]].
    assert (Hlt: filter (fun c => c <? n) cps = filter (fun c => c <? mm) cps) by (apply filter_lt_eq; auto).
    assert (Hmm: mm <= maxint) by (specialize (Hcps2 mm M1); lia).
    assert (h1 <= Zlength cps) by (rewrite Hh1; apply Zlength_filter_le).
    pose proof (Zlength_nonneg (filter (fun c => c =? mm) cps)).
    replace fd with (Z.to_nat (h1 - h) + (fd - Z.to_nat (h1 - h)))%nat by lia.
    destruct (sim_pass_any mm Hmm M1 cps [] (delta + (mm - n) * (h + 1)) bias h out d1 b1 h1 o1 n_dec i_dec
                eq_refl Ep (ex_intro _ r2 He2)) as [[n1 [i1 [S1 [R1 [R2 R3]]]]]|[NB S1]].
    + cbn [filter app]. rewrite <- Hlt; auto.
    + cbn [filter Zlength]. rewrite Zlength_nil. nia.
    + split; [nia|lia].
    + lia.
    + auto.
    + auto.
    + cbn [filter app] in S1. rewrite Hlt, S1.
      rewrite filter_le_lt.
      apply (IHf (mm + 1) (d1 + 1) b1 h1 o1 n1 i1 H Hh1); try lia.
    + right. split; auto. cbn [filter app] in S1. rewrite Hlt. apply S1.
Qed.

End Sim.
