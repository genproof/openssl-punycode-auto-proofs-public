(* A fact the bodies of any_bytes, any_uints and copy_of share: the test of malloc's result against NULL is
   defined (a non-NULL result is a valid pointer, through its data, or its malloc token when the block is empty). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.

Lemma cmn_malloc_tc_test0 {cs: compspecs} (t: type) (p: val) (P: mpred):
  0 <= sizeof t ->
  (if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p) * P
  |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Ht. destruct (eq_dec p nullval).
  - subst. simpl. entailer!.
  - destruct (zlt 0 (sizeof t)).
    + sep_apply (data_at__valid_ptr Ews t p); [ auto | lia | ]. entailer!.
    + sep_apply (malloc_token_valid_pointer Ews t p); [ lia | ]. entailer!.
Qed.

(* The same test when the block is known to be non-NULL and initialised. *)
Lemma cmn_malloc_tc_test1 {cs: compspecs} (t: type) (p: val) (v: reptype t) (P: mpred):
  p <> nullval -> 0 <= sizeof t ->
  malloc_token Ews t p * data_at Ews t v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hp Ht. sep_apply (data_at_data_at_ Ews t v p).
  apply derives_trans with ((if eq_dec p nullval then emp else malloc_token Ews t p * data_at_ Ews t p) * P)%logic.
  - rewrite if_false by auto. cancel.
  - apply cmn_malloc_tc_test0; auto.
Qed.

(* The same test on a source block held with its malloc token and any readable share (copy_of's source). *)
Lemma cmn_src_tc_test {cs: compspecs} (sh: share) (t: type) (v: reptype t) (p: val) (P: mpred):
  readable_share sh -> 0 <= sizeof t ->
  malloc_token Ews t p * data_at sh t v p * P |-- denote_tc_test_eq p (Vlong (Int64.repr 0)).
Proof.
  intros Hsh Ht. destruct (zlt 0 (sizeof t)).
  - sep_apply (data_at_valid_ptr sh t v p); [ apply readable_nonidentity; auto | lia | ]. entailer!.
  - sep_apply (malloc_token_valid_pointer Ews t p); [ lia | ]. entailer!.
Qed.
