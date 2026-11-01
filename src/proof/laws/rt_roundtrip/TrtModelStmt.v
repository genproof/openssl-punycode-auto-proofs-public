(* The round trip of law rt_roundtrip in the model, as a statement: Model.decode inverts Model.encode for any
   number of code points, each any unsigned int, into an output of exactly their number, whenever the decoder's
   insertion state (largest code point - 127) * m stays within 2^32; beyond, it gives them back or fails.  Its
   proof is TrtModel.trt_model; the main of the harness takes the statement as a hypothesis. *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

(* The largest of the code points, 0 for none (what the harness's loop computes). *)
Definition largest (cps: list Z) : Z := fold_left Z.max cps 0.

Definition trt_model_stmt : Prop :=
  forall cps e,
    Forall (fun c => 0 <= c <= maxint) cps ->
    encode cps = Some e ->
    Zlength cps <= Zlength e /\
    (fst (decode e (Zlength cps)) = true -> snd (decode e (Zlength cps)) = cps) /\
    ((largest cps - 127) * Zlength cps <= 2 ^ 32 -> decode e (Zlength cps) = (true, cps)).
