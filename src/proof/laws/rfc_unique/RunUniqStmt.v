(* Law rfc_unique: the model fact its checks need, stated in plain Coq (proved in RunUniq.v).

   Two inputs that Model.decode decodes, with the same capacity, into the same code points are the same octets,
   except that an octet among the deltas (after the last '-', or anywhere when the last '-' is at 0) may be the
   same letter in the other case.  The letter test is written as the harness computes it: `c | 32` is the
   lowercase form of a letter c, and lies in 'a' .. 'z' only for letters. *)
From Coq Require Import ZArith List.
Require Import VST.floyd.functional_base.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Import ListNotations.
Local Open Scope Z_scope.

Definition unique_stmt : Prop :=
  forall inp1 inp2 cap out,
  bytes_ok inp1 -> bytes_ok inp2 ->
  decode inp1 cap = (true, out) -> decode inp2 cap = (true, out) ->
  Zlength inp1 = Zlength inp2 /\
  forall j, 0 <= j < Zlength inp1 -> Znth j inp1 <> Znth j inp2 ->
    (last_delim inp1 < j \/ last_delim inp1 = 0) /\
    97 <= Z.lor (Znth j inp1) 32 <= 122 /\ Z.lor (Znth j inp2) 32 = Z.lor (Znth j inp1) 32.
