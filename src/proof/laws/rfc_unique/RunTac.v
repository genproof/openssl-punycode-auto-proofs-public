(* A faster step of VST's forward_call for the main of harness/rfc_unique.c.

   After a call, forward_call removes the assigned temporary from LOCAL (simplify_remove_localdef_temp of
   VST.floyd.forward), deciding each `rlt_ident_eq i j` (Pos.eq_dec) by `simpl`.  The identifiers of this harness are
   the encodings of their names: _input1 and _input2 agree on their 30 low bits, _len1 and _len2 on 18, and `simpl`
   takes exponential time in the length of the common part (minutes for input2 = any_bytes(len2) with input1 in
   LOCAL).  This version decides each comparison with Pos.eqb by vm_compute and puts the decision in its place, then
   proceeds as VST's tactic does; the result is checked by the same `change`. *)
Require Import VST.floyd.proofauto.

Lemma rlt_ident_eq_true i j: Pos.eqb i j = true -> i = j.
Proof. apply Pos.eqb_eq. Qed.
Lemma rlt_ident_eq_false i j: Pos.eqb i j = false -> i <> j.
Proof. apply Pos.eqb_neq. Qed.

Ltac run_decide_idents u :=
  match u with
  | context C [rlt_ident_eq ?i ?j] =>
      let b := eval vm_compute in (Pos.eqb i j) in
      let r := match b with
               | true => constr:(@left (i = j) (i <> j) (rlt_ident_eq_true i j eq_refl))
               | false => constr:(@right (i = j) (i <> j) (rlt_ident_eq_false i j eq_refl))
               end in
      let u' := context C [r] in run_decide_idents u'
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L]  =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := run_decide_idents u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.
