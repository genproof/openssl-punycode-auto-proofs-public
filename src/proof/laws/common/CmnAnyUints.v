(* The body of any_uints (harness/laws_common.h): malloc(n * 4), then n arbitrary unsigned ints from nondet_u32
   stored one by one while the block is non-NULL. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.laws.common.HelperSpec.
Require Import OpensslPunycode.proof.laws.common.CmnLib.
Require Import OpensslPunycode.harness.rfc_digit_case.code.

Lemma body_any_uints : semax_body Vprog Gprog_any_uints f_any_uints any_uints_spec.
Proof.
  start_function.
  forward_call (tarray tuint n, gv).
  { entailer!. simpl. unfold Vptrofs, Ptrofs.to_int64; simpl. rewrite Z.max_r by lia. f_equal. f_equal. f_equal. lia. }
  { simpl; rep_lia. }
  Intros p.
  forward.
  destruct (eq_dec p nullval) as [Hp|Hp].
  - subst p.
    forward_loop (PROP () LOCAL (temp _values nullval; temp _i (Vlong (Int64.repr 0));
        temp _n (Vlong (Int64.repr n)); gvars gv) SEP (mem_mgr gv))
      break: (PROP () LOCAL (temp _values nullval) SEP (mem_mgr gv)).
    + entailer!.
    + forward_if (temp _t'2 (Vint (Int.repr 0))).
      { discriminate. }
      { forward. entailer!. }
      forward_if. { elim H1'; auto. }
      forward. entailer!.
    + forward. Exists nullval (Zrepeat 0 n). rewrite if_true by auto. entailer!. split.
      * apply Zlength_Zrepeat. lia.
      * apply Forall_forall. intros x Hx. unfold Zrepeat in Hx. apply repeat_spec in Hx. subst x. rep_lia.
  - forward_loop (EX i: Z, EX vs: list Z,
        PROP (0 <= i <= n; Zlength vs = i; Forall (fun x => 0 <= x <= Int.max_unsigned) vs)
        LOCAL (temp _values p; temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr n)); gvars gv)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuint n) p;
             data_at Ews (tarray tuint n) (vb vs ++ Zrepeat Vundef (n - i)) p))
      continue: (EX i: Z, EX vs: list Z,
        PROP (0 <= i < n; Zlength vs = (i + 1)%Z; Forall (fun x => 0 <= x <= Int.max_unsigned) vs)
        LOCAL (temp _values p; temp _i (Vlong (Int64.repr i)); temp _n (Vlong (Int64.repr n)); gvars gv)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuint n) p;
             data_at Ews (tarray tuint n) (vb vs ++ Zrepeat Vundef (n - (i + 1))%Z) p))
      break: (EX vs: list Z,
        PROP (Zlength vs = n; Forall (fun x => 0 <= x <= Int.max_unsigned) vs)
        LOCAL (temp _values p)
        SEP (mem_mgr gv; malloc_token Ews (tarray tuint n) p; data_at Ews (tarray tuint n) (vb vs) p)).
    + Exists 0 (@nil Z). entailer!. unfold data_at_, field_at_. simpl. entailer!.
    + Intros i vs.
      forward_if (temp _t'2 (Vint (Int.repr (if zlt i n then 1 else 0)))).
      { forward. entailer!. destruct (zlt _ _); auto. }
      { contradiction. }
      forward_if.
      * destruct (zlt i n); [ | exfalso; lia ].
        forward_call tt. Intros x.
        forward.
        Exists i (vs ++ [x]). entailer!.
        { split; [ list_solve | apply Forall_app; split; auto ]. }
        unfold vb. rewrite map_app. simpl.
        apply derives_refl'. f_equal. list_solve.
      * destruct (zlt i n); [ discriminate | ].
        forward. Exists vs. entailer!.
        replace (n - Zlength vs) with 0 by lia. simpl. rewrite app_nil_r. auto.
    + Intros i vs. forward. Exists (i + 1) vs. entailer!.
    + Intros vs. forward. Exists p vs. rewrite if_false by auto. entailer!.
Qed.
