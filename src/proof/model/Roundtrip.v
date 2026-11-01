(* The roundtrip theorem of the model, in plain Coq: RFC 3492 decoding inverts the encoder (the bootstring
   invariant), for at most 512 code points <= 0x10FFFF, and what the encoder writes. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.model.RtDigits.
Import ListNotations.
Local Open Scope Z_scope.

(* decode (encode cps) = cps, into any output bound >= |cps|. *)
Definition decode_encode_stmt : Prop :=
  forall cps e cap,
    Zlength cps <= label_cap -> Zlength cps <= cap ->
    Forall (fun c => 0 <= c <= 1114111) cps ->
    encode cps = Some e ->
    decode e cap = (true, cps).

(* The octets of an encoding: the delimiter, lowercase letters and digits, and the basic code points of cps. *)
Definition encode_chars_stmt : Prop :=
  forall cps e,
    Forall (fun c => 0 <= c <= Int.max_unsigned) cps ->
    encode cps = Some e ->
    Forall (fun c => c = 45 \/ (97 <= c <= 122) \/ (48 <= c <= 57) \/ (c < 128 /\ In c cps)) e.

(* ---------------------------------------------------------------------- *)
(* Helper lemmas                                                          *)
(* ---------------------------------------------------------------------- *)

Definition dchar (c: Z) : Prop := (97 <= c <= 122) \/ (48 <= c <= 57).

Lemma Zlength_filter_le : forall (f: Z -> bool) l, Zlength (filter f l) <= Zlength l.
Proof.
  intros f l; induction l as [|x l IH]; simpl; [lia|].
  destruct (f x); rewrite ?Zlength_cons; lia.
Qed.

Lemma filter_all : forall (f: Z -> bool) l, Zlength l <= Zlength (filter f l) -> filter f l = l.
Proof.
  intros f l; induction l as [|x l IH]; simpl; intros H; [auto|].
  pose proof (Zlength_filter_le f l).
  destruct (f x); rewrite ?Zlength_cons in H.
  - rewrite IH; auto; lia.
  - lia.
Qed.

Lemma filter_lt_exists : forall n l,
  Zlength (filter (fun c => c <? n) l) < Zlength l -> exists c, In c l /\ n <= c.
Proof.
  intros n l; induction l as [|x l IH]; simpl; intros H; [rewrite Zlength_nil in H; lia|].
  destruct (x <? n) eqn:E.
  - rewrite !Zlength_cons in H. destruct IH as [c [Hc Hn]]; [lia|]. exists c; auto.
  - apply Z.ltb_ge in E. exists x; auto.
Qed.

Lemma filter_lt_eq : forall n mm l, n <= mm -> (forall c, In c l -> n <= c -> mm <= c) ->
  filter (fun c => c <? n) l = filter (fun c => c <? mm) l.
Proof.
  intros n mm l H1 H2; apply filter_ext_in; intros a Ha.
  destruct (Z_lt_le_dec a n); [rewrite !(proj2 (Z.ltb_lt _ _)) by lia; auto|].
  specialize (H2 a Ha l0). rewrite !(proj2 (Z.ltb_ge _ _)) by lia; auto.
Qed.

Lemma filter_le_lt : forall mm l,
  filter (fun c => c <=? mm) l = filter (fun c => c <? mm + 1) l.
Proof.
  intros; apply filter_ext; intros a.
  destruct (Z_le_gt_dec a mm); [rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; auto
  | rewrite (proj2 (Z.leb_gt _ _)), (proj2 (Z.ltb_ge _ _)) by lia; auto].
Qed.

Lemma filter_le_count : forall mm l,
  Zlength (filter (fun c => c <=? mm) l)
  = Zlength (filter (fun c => c <? mm) l) + Zlength (filter (fun c => c =? mm) l).
Proof.
  intros mm l; induction l as [|x l IH]; simpl; [auto|].
  destruct (Z.lt_trichotomy x mm) as [E|[E|E]].
  - rewrite (proj2 (Z.leb_le x mm)), (proj2 (Z.ltb_lt x mm)), (proj2 (Z.eqb_neq x mm)) by lia.
    rewrite !Zlength_cons; lia.
  - subst; rewrite Z.leb_refl, Z.ltb_irrefl, Z.eqb_refl, !Zlength_cons; lia.
  - rewrite (proj2 (Z.leb_gt x mm)), (proj2 (Z.ltb_ge x mm)), (proj2 (Z.eqb_neq x mm)) by lia; auto.
Qed.

Lemma min_ge_fold : forall n l acc,
  let r := fold_left (fun acc c => if (n <=? c) && (c <? acc) then c else acc) l acc in
  (r = acc \/ (In r l /\ n <= r)) /\ r <= acc /\ (forall c, In c l -> n <= c -> r <= c).
Proof.
  intros n l; induction l as [|x l IH]; intros acc; simpl.
  - split; [left; auto | split; [lia | intros; contradiction]].
  - destruct ((n <=? x) && (x <? acc)) eqn:E.
    + apply andb_true_iff in E; destruct E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2.
      destruct (IH x) as [A [B C]]. split; [|split].
      * right. destruct A as [A|[A1 A2]]; [rewrite A; split; [left|]; auto | split; [right|]; auto].
      * lia.
      * intros c [Hc|Hc] Hn; [subst; lia | auto].
    + destruct (IH acc) as [A [B C]]. split; [|split].
      * destruct A as [A|[A1 A2]]; [left; auto | right; split; [right|]; auto].
      * auto.
      * intros c [Hc|Hc] Hn; [subst c | auto].
        apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E; lia | apply Z.ltb_ge in E; lia].
Qed.

Lemma min_ge_spec : forall cps n c, In c cps -> n <= c -> c <= maxint ->
  In (min_ge cps n) cps /\ n <= min_ge cps n /\ (forall c', In c' cps -> n <= c' -> min_ge cps n <= c').
Proof.
  intros cps n c Hc Hn Hm; unfold min_ge.
  destruct (min_ge_fold n cps (maxint + 1)) as [A [B C]].
  split; [|split]; auto.
  - destruct A as [A|[A1 A2]]; auto. specialize (C c Hc Hn). lia.
  - destruct A as [A|[A1 A2]]; auto. specialize (C c Hc Hn). lia.
Qed.

Lemma enc_digits_nonnil : forall f q k bias, 1 <= Zlength (enc_digits f q k bias).
Proof.
  intros [|f] q k bias; simpl; [|destruct (q <? threshold k bias)]; rewrite Zlength_cons; list_solve.
Qed.

Lemma enc_pass_nil : forall n delta bias h b out,
  enc_pass [] n delta bias h b out = Some (delta, bias, h, out).
Proof. reflexivity. Qed.

Lemma enc_pass_cons : forall c l n delta bias h b out,
  enc_pass (c :: l) n delta bias h b out =
    if c <? n then
      if maxint <? delta + 1 then None else enc_pass l n (delta + 1) bias h b out
    else if c =? n then
      enc_pass l n 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias)
    else enc_pass l n delta bias h b out.
Proof. reflexivity. Qed.

Lemma enc_rounds_S : forall cps f n delta bias h b out,
  enc_rounds cps (S f) n delta bias h b out =
    if Zlength cps <=? h then Some out else
    let mm := min_ge cps n in
    if (maxint <? delta) || ((maxint - delta) / (h + 1) <? mm - n) then None else
    match enc_pass cps mm (delta + (mm - n) * (h + 1)) bias h b out with
    | None => None
    | Some (delta1, bias1, h1, out1) => enc_rounds cps f (mm + 1) (delta1 + 1) bias1 h1 b out1
    end.
Proof. reflexivity. Qed.

(* The encoder's pass: delta stays in 0..maxint, h counts the code points mm, and it appends digits. *)
Lemma pass_shape : forall l mm delta bias h b out delta' bias' h' out',
  enc_pass l mm delta bias h b out = Some (delta', bias', h', out') -> 0 <= delta <= maxint ->
  0 <= delta' <= maxint /\ h' = h + Zlength (filter (fun c => c =? mm) l) /\
  exists r, out' = out ++ r /\ Forall dchar r /\ h' - h <= Zlength r.
Proof.
  induction l as [|c l IH]; intros mm delta bias h b out delta' bias' h' out' H Hd;
    [rewrite enc_pass_nil in H | rewrite enc_pass_cons in H].
  - inv H. split; auto. split; [cbn [filter]; rewrite Zlength_nil; lia|].
    exists []. rewrite app_nil_r. split; auto. split; auto. rewrite Zlength_nil; lia.
  - destruct (c <? mm) eqn:E1.
    + destruct (maxint <? delta + 1) eqn:E2; [discriminate|]. apply Z.ltb_ge in E2.
      apply IH in H; [|lia]. destruct H as [A [B C]]. split; auto. split; auto.
      cbn [filter]. rewrite (proj2 (Z.eqb_neq c mm)) by (apply Z.ltb_lt in E1; lia); auto.
    + destruct (c =? mm) eqn:E3.
      * apply IH in H; [|unfold maxint; lia]. destruct H as [A [B [r [C [D F]]]]].
        split; auto. cbn [filter]; rewrite E3, Zlength_cons; split; [lia|].
        exists (enc_digits 64 delta 36 bias ++ r). rewrite <- app_assoc in C. split; auto.
        split; [apply Forall_app; split; auto; apply enc_digits_chars; lia|].
        pose proof (enc_digits_nonnil 64 delta 36 bias). rewrite Zlength_app; lia.
      * apply IH in H; [|lia]. destruct H as [A [B C]]. split; auto.
        cbn [filter]; rewrite E3; auto.
Qed.

Section Rounds.
Variable cps : list Z.
Context (Hcps : Forall (fun c => 0 <= c <= maxint) cps).

(* The encoder's rounds: h counts the code points < n, delta >= 0, and they append digits. *)
Lemma rounds_shape : forall f n delta bias h b out e,
  enc_rounds cps f n delta bias h b out = Some e ->
  h = Zlength (filter (fun c => c <? n) cps) -> 0 <= delta ->
  exists r, e = out ++ r /\ Forall dchar r /\ Zlength cps - h <= Zlength r.
Proof.
  induction f; intros n delta bias h b out e H Hh Hd; [discriminate|].
  rewrite enc_rounds_S in H; cbv zeta in H.
  destruct (Zlength cps <=? h) eqn:Eh.
  - inv H. exists []. rewrite app_nil_r. split; auto. split; auto. apply Z.leb_le in Eh. rewrite Zlength_nil; lia.
  - apply Z.leb_gt in Eh.
    destruct ((maxint <? delta) || ((maxint - delta) / (h + 1) <? min_ge cps n - n)) eqn:Ec; [discriminate|].
    apply orb_false_iff in Ec; destruct Ec as [Ec1 Ec2]; apply Z.ltb_ge in Ec1; apply Z.ltb_ge in Ec2.
    rewrite Hh in Eh. destruct (filter_lt_exists n cps Eh) as [c [Hc Hnc]].
    rewrite Forall_forall in Hcps.
    destruct (min_ge_spec cps n c Hc Hnc (proj2 (Hcps c Hc))) as [M1 [M2 M3]].
    rewrite <- Hh in Eh.
    set (mm := min_ge cps n) in *.
    assert (0 <= h) by (rewrite Hh; apply Zlength_nonneg).
    assert (Hb: (mm - n) * (h + 1) <= maxint - delta).
    { pose proof (Z.mul_div_le (maxint - delta) (h + 1) ltac:(lia)). nia. }
    destruct (enc_pass cps mm (delta + (mm - n) * (h + 1)) bias h b out) as [[[[d1 b1] h1] o1]|] eqn:Ep;
      [|discriminate].
    apply pass_shape in Ep; [|nia]. destruct Ep as [A [B [r1 [C [D F]]]]].
    apply IHf in H; [| |lia].
    + destruct H as [r2 [G [I J]]]. exists (r1 ++ r2). rewrite G, C, app_assoc. split; auto.
      split; [apply Forall_app; auto|]. rewrite Zlength_app. lia.
    + rewrite B, Hh, <- filter_le_lt, filter_le_count, (filter_lt_eq n mm); auto.
Qed.

End Rounds.

(* ---------------------------------------------------------------------- *)
(* The simulation: the decoder follows the encoder                        *)
(* ---------------------------------------------------------------------- *)

Lemma steps_S : forall inp f cap pos n i bias out,
  steps inp (S f) cap pos n i bias out =
  if Zlength inp <=? pos then (true, out) else
  match digits inp (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias with
  | None => (false, out)
  | Some (i1, pos1) =>
    let c := Zlength out in
    let bias1 := adapt (i1 - i) (c + 1) (i =? 0) in
    let n1 := n + i1 / (c + 1) in
    if maxint <? n1 then (false, out) else
    let i2 := i1 mod (c + 1) in
    if cap <=? c then (false, out) else
    steps inp f cap pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out)
  end.
Proof. reflexivity. Qed.

Lemma insert_at_app : forall A B x, insert_at (Zlength A) x (A ++ B) = A ++ x :: B.
Proof.
  intros; unfold insert_at.
  rewrite sublist_app1 by list_solve. rewrite sublist_same by list_solve.
  rewrite sublist_app2 by list_solve. rewrite Zlength_app, Z.sub_diag.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
  rewrite sublist_same by list_solve. auto.
Qed.

Section Sim.
Variable cps : list Z.
Variable e : list Z.
Variable cap b : Z.
Context (Hcps : Forall (fun c => 0 <= c <= 1114111) cps).
Context (Hlen : Zlength cps <= 512).
Context (Hcap : Zlength cps <= cap).

Lemma sim_pass : forall mm l pre delta bias h out delta' bias' h' out' n_dec i_dec,
  cps = pre ++ l -> mm <= 1114111 ->
  enc_pass l mm delta bias h b out = Some (delta', bias', h', out') ->
  (exists r, e = out' ++ r) ->
  h = Zlength (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) l) ->
  delta + i_dec = (mm - n_dec) * (h + 1) + Zlength (filter (fun c => c <=? mm) pre) ->
  0 <= delta <= maxint -> 0 <= n_dec <= mm ->
  (h = b /\ i_dec = 0 \/ b < h /\ 1 <= i_dec) ->
  exists n_dec' i_dec',
    (forall fd, steps e (Z.to_nat (h' - h) + fd) cap (Zlength out) n_dec i_dec bias
                  (filter (fun c => c <=? mm) pre ++ filter (fun c => c <? mm) l)
                = steps e fd cap (Zlength out') n_dec' i_dec' bias' (filter (fun c => c <=? mm) cps)) /\
    delta' + i_dec' = (mm - n_dec') * (h' + 1) + h' /\ 0 <= n_dec' <= mm /\
    (h' = b /\ i_dec' = 0 \/ b < h' /\ 1 <= i_dec').
Proof.
  induction l as [|c l IH];
    intros pre delta bias h out delta' bias' h' out' n_dec i_dec Hc Hmm Hp He Hh Hi Hd Hn Hb.
  - rewrite enc_pass_nil in Hp. inv Hp. exists n_dec, i_dec.
    rewrite app_nil_r in *. cbn [filter] in *. rewrite app_nil_r in *.
    split; [intros fd; rewrite Z.sub_diag; reflexivity|]. split; [lia|]. split; auto.
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
      destruct (IH (pre ++ [c]) (delta + 1) bias h out delta' bias' h' out' n_dec i_dec P1 Hmm Hp He P2 P3
                  ltac:(lia) Hn Hb) as [n1 [i1 [S1 R1]]].
      exists n1, i1. rewrite <- Heq. split; auto.
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
        destruct (IH (pre ++ [mm]) 0 (adapt delta (h + 1) (h =? b)) (h + 1) (out ++ ds) delta' bias' h' out'
                      mm (cnt + 1) P1 Hmm Hp (ex_intro _ r He) Hh1 P3 ltac:(unfold maxint; lia) ltac:(lia)
                      ltac:(right; lia)) as [n1 [i1 [S1 R1]]].
        exists n1, i1. split; [|exact R1].
           intros fd.
           replace (Z.to_nat (h' - h) + fd)%nat with (S (Z.to_nat (h' - (h + 1)) + fd))%nat
             by (pose proof (Zlength_nonneg (filter (fun c => c =? mm) l)); lia).
           rewrite steps_S.
           assert (Hlt: h < Zlength cps).
           { rewrite Hc, Hh, !Zlength_app. cbn [filter]. rewrite Z.ltb_irrefl, Zlength_cons.
             pose proof (Zlength_filter_le (fun c => c <=? mm) pre).
             pose proof (Zlength_filter_le (fun c => c <? mm) l). lia. }
           assert (Hbd: i_dec + delta <= 600000000).
           { rewrite Z.add_comm, Hi.
             assert ((mm - n_dec) * (h + 1) <= 1114111 * 513) by (apply Z.mul_le_mono_nonneg; lia).
             lia. }
           pose proof (digits_enc_digits out (r1 ++ r) delta bias i_dec ltac:(lia) ltac:(lia) Hbd) as Hdg.
           cbv zeta in Hdg. fold ds in Hdg.
           assert (He2: e = out ++ ds ++ r1 ++ r) by (rewrite He, C, <- !app_assoc; reflexivity).
           rewrite <- He2 in Hdg.
           pose proof (enc_digits_nonnil 64 delta 36 bias). fold ds in H.
           rewrite (proj2 (Z.leb_gt _ _)) by (rewrite He2, !Zlength_app; pose proof (Zlength_nonneg (r1 ++ r)); list_solve).
           rewrite Hdg. rewrite <- Hh.
           assert (Hdiv: (i_dec + delta) / (h + 1) = mm - n_dec)
             by (apply Zdiv_unique with cnt; lia).
           assert (Hmod: (i_dec + delta) mod (h + 1) = cnt)
             by (apply Zmod_unique with (mm - n_dec); lia).
           cbv zeta. rewrite Hdiv, Hmod.
           replace (n_dec + (mm - n_dec)) with mm by lia.
           rewrite (proj2 (Z.ltb_ge maxint mm)) by (unfold maxint; lia).
           rewrite (proj2 (Z.leb_gt cap h)) by lia.
           replace (i_dec + delta - i_dec) with delta by lia.
           replace (i_dec =? 0) with (h =? b)
             by (destruct Hb as [[-> ->]|[Hb1 Hb2]]; [rewrite !Z.eqb_refl; auto
                 | rewrite (proj2 (Z.eqb_neq h b)), (proj2 (Z.eqb_neq i_dec 0)) by lia; auto]).
           rewrite <- Heq. rewrite Zlength_app in S1. apply S1.
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
        destruct (IH (pre ++ [c]) delta bias h out delta' bias' h' out' n_dec i_dec P1 Hmm Hp He P2 P3
                    Hd Hn Hb) as [n1 [i1 [S1 R1]]].
        exists n1, i1. rewrite <- Heq. split; auto.
Qed.

Lemma sim_rounds : forall f n delta bias h out n_dec i_dec,
  enc_rounds cps f n delta bias h b out = Some e ->
  h = Zlength (filter (fun c => c <? n) cps) ->
  delta + i_dec = (n - n_dec) * (h + 1) -> 0 <= delta -> 0 <= n_dec <= n ->
  (h = b /\ i_dec = 0 \/ b < h /\ 1 <= i_dec) ->
  forall fd, Zlength cps - h <= Z.of_nat fd ->
  steps e fd cap (Zlength out) n_dec i_dec bias (filter (fun c => c <? n) cps) = (true, cps).
Proof.
  assert (Hcps': Forall (fun c => 0 <= c <= maxint) cps)
    by (eapply Forall_impl; [|exact Hcps]; intros a Ha; simpl in Ha; unfold maxint; lia).
  induction f; intros n delta bias h out n_dec i_dec H Hh Hi Hd Hn Hb fd Hfd; [discriminate|].
  pose proof H as Hsh. apply rounds_shape in Hsh; auto. destruct Hsh as [r0 [He0 _]].
  rewrite enc_rounds_S in H; cbv zeta in H.
  destruct (Zlength cps <=? h) eqn:Eh.
  - inv H. apply Z.leb_le in Eh.
    assert (filter (fun c => c <? n) cps = cps) by (apply filter_all; lia).
    destruct fd; [simpl; congruence|]. rewrite steps_S, Z.leb_refl. congruence.
  - apply Z.leb_gt in Eh.
    destruct ((maxint <? delta) || ((maxint - delta) / (h + 1) <? min_ge cps n - n)) eqn:Ec; [discriminate|].
    apply orb_false_iff in Ec; destruct Ec as [Ec1 Ec2]; apply Z.ltb_ge in Ec1; apply Z.ltb_ge in Ec2.
    rewrite Hh in Eh. destruct (filter_lt_exists n cps Eh) as [c [Hc Hnc]].
    pose proof Hcps as Hcps2. rewrite Forall_forall in Hcps2.
    destruct (min_ge_spec cps n c Hc Hnc ltac:(specialize (Hcps2 c Hc); unfold maxint; lia)) as [M1 [M2 M3]].
    rewrite <- Hh in Eh.
    set (mm := min_ge cps n) in *.
    assert (0 <= h) by (rewrite Hh; apply Zlength_nonneg).
    assert (Hbd: (mm - n) * (h + 1) <= maxint - delta).
    { pose proof (Z.mul_div_le (maxint - delta) (h + 1) ltac:(lia)). nia. }
    destruct (enc_pass cps mm (delta + (mm - n) * (h + 1)) bias h b out) as [[[[d1 b1] h1] o1]|] eqn:Ep;
      [|discriminate].
    pose proof Ep as Ep'. apply pass_shape in Ep'; [|nia]. destruct Ep' as [A [B [r1 [C [D F]]]]].
    assert (Hh1: h1 = Zlength (filter (fun c => c <? mm + 1) cps)).
    { rewrite B, Hh, <- filter_le_lt, filter_le_count, (filter_lt_eq n mm); auto. }
    pose proof H as Hsh. apply rounds_shape in Hsh; [|auto|auto|lia]. destruct Hsh as [r2 [He2 _]].
    assert (Hlt: filter (fun c => c <? n) cps = filter (fun c => c <? mm) cps) by (apply filter_lt_eq; auto).
    assert (Hmm: mm <= 1114111) by (specialize (Hcps2 mm M1); lia).
    destruct (sim_pass mm cps [] (delta + (mm - n) * (h + 1)) bias h out d1 b1 h1 o1 n_dec i_dec
                eq_refl Hmm Ep (ex_intro _ r2 He2)) as [n1 [i1 [S1 [R1 [R2 R3]]]]].
    + cbn [filter app]. rewrite <- Hlt; auto.
    + cbn [filter Zlength]. rewrite Zlength_nil. nia.
    + split; [nia|lia].
    + lia.
    + auto.
    + assert (h1 <= Zlength cps) by (rewrite Hh1; apply Zlength_filter_le).
      pose proof (Zlength_nonneg (filter (fun c => c =? mm) cps)).
      replace fd with (Z.to_nat (h1 - h) + (fd - Z.to_nat (h1 - h)))%nat by lia.
      cbn [filter app] in S1. rewrite Hlt, S1.
      rewrite filter_le_lt.
      pose proof (Zlength_nonneg (filter (fun c => c =? mm) cps)).
      apply (IHf (mm + 1) (d1 + 1) b1 h1 o1 n1 i1 H Hh1); try lia.
Qed.

End Sim.

Lemma last_delim_from_app : forall l1 l2 j acc,
  last_delim_from (l1 ++ l2) j acc = last_delim_from l2 (j + Zlength l1) (last_delim_from l1 j acc).
Proof.
  induction l1 as [|x l1 IH]; intros; simpl.
  - rewrite Zlength_nil, Z.add_0_r; auto.
  - rewrite IH, Zlength_cons. f_equal. lia.
Qed.

Lemma last_delim_from_none : forall l j acc, Forall dchar l -> last_delim_from l j acc = acc.
Proof.
  induction l as [|x l IH]; intros j acc H; simpl; auto.
  inv H. rewrite IH; auto. unfold dchar in H2. rewrite (proj2 (Z.eqb_neq x 45)) by lia. auto.
Qed.

Lemma basic_prefix_all : forall l, Forall (fun c => c < 128) l -> basic_prefix l = l.
Proof.
  induction l as [|x l IH]; intros H; simpl; auto. inv H. rewrite (proj2 (Z.ltb_lt x 128)) by auto.
  rewrite IH; auto.
Qed.

Lemma filter_basic : forall l, Forall (fun c => c < 128 /\ In c l) (filter (fun c => c <? 128) l).
Proof.
  intros l. apply Forall_forall. intros x Hx. apply filter_In in Hx. destruct Hx as [H1 H2].
  apply Z.ltb_lt in H2. auto.
Qed.


Lemma encode_shape : forall cps e,
  Forall (fun c => 0 <= c <= maxint) cps -> encode cps = Some e ->
  let basics := filter (fun c => c <? 128) cps in
  exists r, e = (if 0 <? Zlength basics then basics ++ [45] else basics) ++ r /\ Forall dchar r /\
            Zlength cps - Zlength basics <= Zlength r.
Proof.
  intros cps e Hc He. unfold encode in He. cbv zeta.
  apply rounds_shape in He; auto. lia.
Qed.

Theorem roundtrip_model : decode_encode_stmt /\ encode_chars_stmt.
Proof.
  split.
  - intros cps e cap Hlen Hcap Hcps He.
    assert (Hcps': Forall (fun c => 0 <= c <= maxint) cps)
      by (eapply Forall_impl; [|exact Hcps]; intros a Ha; simpl in Ha; unfold maxint; lia).
    destruct (encode_shape cps e Hcps' He) as [r [Er [Dr Lr]]].
    set (basics := filter (fun c => c <? 128) cps) in *.
    set (b := Zlength basics) in *.
    set (out0 := if 0 <? b then basics ++ [45] else basics) in *.
    assert (Hb0: 0 <= b) by apply Zlength_nonneg.
    assert (Hbl: b <= Zlength cps) by apply Zlength_filter_le.
    assert (Hld: last_delim e = b).
    { unfold last_delim. rewrite Er. subst out0. destruct (0 <? b) eqn:Eb.
      - rewrite <- app_assoc, last_delim_from_app. cbn [app last_delim_from].
        rewrite Z.eqb_refl, last_delim_from_none; auto.
      - apply Z.ltb_ge in Eb. assert (basics = []) by (apply Zlength_nil_inv; lia).
        rewrite H. cbn [app]. rewrite last_delim_from_none; auto. subst b; rewrite H; auto. }
    assert (Hbas: Forall (fun c => c < 128) basics)
      by (eapply Forall_impl; [|apply filter_basic]; simpl; intros a [Ha _]; auto).
    assert (Hpre: sublist 0 b e = basics).
    { rewrite Er. subst out0. destruct (0 <? b); [rewrite <- app_assoc|];
        rewrite sublist_app1 by (subst b; lia); apply sublist_same; auto. }
    unfold decode. rewrite Hld, Hpre, basic_prefix_all by auto.
    rewrite (proj2 (Z.ltb_ge cap b)) by lia. rewrite Z.ltb_irrefl.
    replace (if b =? 0 then 0 else b + 1) with (Zlength out0).
    2:{ subst out0. destruct (0 <? b) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
        - rewrite (proj2 (Z.eqb_neq b 0)) by lia. rewrite Zlength_app, Zlength_cons, Zlength_nil. auto.
        - rewrite (proj2 (Z.eqb_eq b 0)) by lia. subst b; lia. }
    unfold encode in He. fold basics b out0 in He.
    apply (sim_rounds cps e cap b Hcps Hlen Hcap (S (length cps)) 128 0 72 b out0 128 0 He);
      auto; try lia.
    rewrite <- Zlength_correct. rewrite Er, Zlength_app. pose proof (Zlength_nonneg out0). lia.
  - intros cps e Hcps He.
    assert (Hcps': Forall (fun c => 0 <= c <= maxint) cps)
      by (eapply Forall_impl; [|exact Hcps]; intros a Ha; simpl in Ha; exact Ha).
    destruct (encode_shape cps e Hcps' He) as [r [Er [Dr Lr]]].
    rewrite Er. apply Forall_app. split.
    + pose proof (filter_basic cps) as Hb.
      destruct (0 <? _); [apply Forall_app; split|].
      * eapply Forall_impl; [|exact Hb]. simpl; intros; auto.
      * constructor; auto.
      * eapply Forall_impl; [|exact Hb]. simpl; intros; auto.
    + eapply Forall_impl; [|exact Dr]. unfold dchar; intros a Ha; right; destruct Ha; [left|right; left]; auto.
Qed.

Definition decode_encode : decode_encode_stmt := proj1 roundtrip_model.
Definition encode_chars : encode_chars_stmt := proj2 roundtrip_model.
