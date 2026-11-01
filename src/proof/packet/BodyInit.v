(* A body of the WPACKET functions (patch/units/packet_ext.c), under Packet.CS; assembled in Bodies.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require Import OpensslPunycode.proof.shim.ShimSpec.
Require Import OpensslPunycode.proof.packet.PacketSpec.
Require Import OpensslPunycode.packet.code.

(* The composites of the shim unit are among those of the packet unit: a type is no larger under Shim.CS. *)
Lemma shim_cenv_in_packet: forall id co,
  Maps.PTree.get id (@cenv_cs OpensslPunycode.proof.shim.ShimSpec.CS) = Some co ->
  exists co', Maps.PTree.get id (@cenv_cs CS) = Some co' /\ co_sizeof co' = co_sizeof co.
Proof.
  intros id co H. apply Maps.PTree.elements_correct in H.
  vm_compute in H. destruct H as [H|[]]. inv H.
  eexists; split; [vm_compute; reflexivity | reflexivity].
Qed.

Lemma sizeof_composite: forall (cs: compspecs) i a,
  (@sizeof cs (Tstruct i a) = match Maps.PTree.get i (@cenv_cs cs) with Some co => co_sizeof co | None => 0 end) /\
  (@sizeof cs (Tunion i a) = match Maps.PTree.get i (@cenv_cs cs) with Some co => co_sizeof co | None => 0 end).
Proof. split; reflexivity. Qed.

Lemma sizeof_shim_le: forall t,
  @sizeof OpensslPunycode.proof.shim.ShimSpec.CS t <= @sizeof CS t.
Proof.
  induction t; try (simpl; lia).
  - simpl. pose proof (@Ctypes.sizeof_pos (@cenv_cs OpensslPunycode.proof.shim.ShimSpec.CS) t).
    apply Z.mul_le_mono_nonneg_r; [lia | exact IHt].
  - rewrite (proj1 (sizeof_composite _ i a)), (proj1 (sizeof_composite CS i a)).
    destruct (Maps.PTree.get i (@cenv_cs OpensslPunycode.proof.shim.ShimSpec.CS)) eqn:E.
    + destruct (shim_cenv_in_packet _ _ E) as [co' [E' S]]. rewrite E', S. lia.
    + destruct (Maps.PTree.get i (@cenv_cs CS)); [pose proof (co_sizeof_pos c) | ]; lia.
  - rewrite (proj2 (sizeof_composite _ i a)), (proj2 (sizeof_composite CS i a)).
    destruct (Maps.PTree.get i (@cenv_cs OpensslPunycode.proof.shim.ShimSpec.CS)) eqn:E.
    + destruct (shim_cenv_in_packet _ _ E) as [co' [E' S]]. rewrite E', S. lia.
    + destruct (Maps.PTree.get i (@cenv_cs CS)); [pose proof (co_sizeof_pos c) | ]; lia.
Qed.

Lemma default_pkt: default_val t_pkt = (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))).
Proof. reflexivity. Qed.

Lemma body_init_static_len_ok :
  semax_body Vprog Gprog_init_static_len f_WPACKET_init_static_len WPACKET_init_static_len_spec.
Proof.
  start_function.
  forward_call 0.
  assert_PROP (isptr buf) by entailer!.
  forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (if Z.eq_dec cap 0 then 0 else 1)));
      temp _max (Vlong (Int64.repr (maxmaxsize_model 0))); temp _pkt pkt; temp _buf buf;
      temp _len (Vlong (Int64.repr cap)); temp _lenbytes (Vlong (Int64.repr 0)); gvars gv)
    SEP (zero_tok cap tk buf; data_at_ shp t_pkt pkt; data_at shb (tarray tuchar cap) init buf;
         shim_state gv fn zf live; mem_mgr gv)).
  { apply denote_tc_test_eq_split; [| apply valid_pointer_null].
    unfold zero_tok. destruct (Z.eq_dec (Zlength init) 0).
    - do 4 apply sepcon_valid_pointer1. apply malloc_token_valid_pointer. pose proof (sizeof_shim_le tk). lia.
    - do 2 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr; [auto | simpl; rep_lia]. }
  { forward. entailer!. destruct (Z.eq_dec (Zlength init) 0).
    - rewrite e. reflexivity.
    - unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia. destruct zlt; try lia. reflexivity. }
  { subst buf; contradiction. }
  destruct (Z.eq_dec cap 0).
  - forward_if.
    + forward. Exists 0 nullval fn zf live. entailer!. Exists (default_val t_pkt). entailer!.
    + exfalso; apply H4; reflexivity.
  - forward_if.
    + inv H4.
    + rewrite data_at__eq, default_pkt. forward. forward.
      change (maxmaxsize_model 0) with Int64.max_unsigned.
      forward_if (PROP () LOCAL (temp _t'3 (Vlong (Int64.repr cap)); temp _pkt pkt; temp _buf buf;
          temp _lenbytes (Vlong (Int64.repr 0)); gvars gv)
        SEP (zero_tok cap tk buf;
             data_at shp t_pkt (Vlong (Int64.repr (Int.signed (Int.repr 0))),
                                (buf, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))) pkt;
             data_at shb (tarray tuchar cap) init buf; shim_state gv fn zf live; mem_mgr gv)).
      * lia.
      * forward. entailer!.
      * forward. forward.
        forward_call (gv, shp, pkt, nullval, buf, Vundef, Vundef, Vlong (Int64.repr cap), Vundef, Vint (Int.repr 0),
                      fn, zf, live).
        Intros vret. destruct vret as [[[sub fn'] zf'] live']. simpl fst in *. simpl snd in *.
        forward.
        Exists (if eq_dec sub nullval then 0 else 1) sub fn' zf' live'.
        destruct (eq_dec sub nullval).
        -- rewrite if_true by auto. Exists (nullval, (buf, (Vlong (Int64.repr 0), (Vlong (Int64.repr 0),
              (Vlong (Int64.repr (Zlength init)), (sub, Vint (Int.repr 0))))))). entailer!.
        -- rewrite if_false by lia. unfold wpkt, sub_rec, pkt_rep. simpl vb. rewrite Zlength_nil, sublist_same by lia.
           entailer!. constructor.
Qed.
