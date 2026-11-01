(* encode, the pass over the code points for the code point n of a round: the state before the code point j and
   the body of the loop over j__2 after its test (verbatim from the law's code.v, inside tstmt_passloop). *)
Require Import VST.floyd.proofauto.
Require Import OpensslPunycode.proof.common.Bytes.
Require Import OpensslPunycode.proof.model.Model.
Require OpensslPunycode.proof.harness.RefRt.
Require Import OpensslPunycode.proof.harness.EncModel.
Require Import OpensslPunycode.proof.harness.EncDefs.
Require Import OpensslPunycode.harness.rt_roundtrip.code.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtProg.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtSpec.
Require Import OpensslPunycode.proof.laws.rt_roundtrip.TrtEncDefs.
Local Open Scope logic.

(* The state of the pass for code point n before the code point j (the temp j__2 holds jv): the encoding continues
   with the pass over the code points from j on (kont), h counts the code points equal to n before j.  f: the fuel
   of the rounds after this one, h0: h at the start of the pass, B: the number of basic code points. *)
Definition tpass_st (shc: share) (pc: val) (cps: list Z) (sho: share) (po: val) (room: Z) (oinit: list val)
  (shl: share) (pl: val) (f: nat) (n h0 B j jv: Z) : environ -> mpred :=
  EX delta: Z, EX bias: Z, EX h: Z, EX out: list Z,
  PROP (encode cps = kont cps f n (sublist j (Zlength cps) cps) delta bias h B out;
        (h = h0 + cnt_eq n (sublist 0 j cps))%Z; 0 <= delta <= maxint; 0 <= bias <= 2400; Zlength out <= room)
  LOCAL (temp _n (Vlong (Int64.repr n)); temp _delta (Vlong (Int64.repr delta));
         temp _bias (Vlong (Int64.repr bias)); temp _b (Vlong (Int64.repr B)); temp _h (Vlong (Int64.repr h));
         temp _j__2 (Vlong (Int64.repr jv)); temp _cps pc; temp _m (Vlong (Int64.repr (Zlength cps)));
         temp _out po; temp _room (Vlong (Int64.repr room)); temp _len pl)
  SEP (arr0 shc tuint (Zlength cps) (vb cps) pc; arr0 sho tuchar room (bufv out room oinit) po;
       data_at shl tulong (Vlong (Int64.repr (Zlength out))) pl).

Definition tstmt_passbody := (Ssequence (Ssequence (Sset _t'13 (Ederef (Ebinop Oadd (Etempvar _cps (tptr tuint))
  (Etempvar _j__2 tulong) (tptr tuint)) tuint)) (Sifthenelse (Ebinop Olt (Etempvar _t'13 tuint) (Etempvar _n tulong)
  tint) (Ssequence (Sset _delta (Ebinop Oadd (Etempvar _delta tulong) (Econst_int (Int.repr 1) tint) tulong))
  (Sifthenelse (Ebinop Ogt (Etempvar _delta tulong) (Econst_int (Int.repr (-1)) tuint) tint) (Sreturn (Some
  (Econst_int (Int.repr 0) tint))) Sskip)) Sskip)) (Ssequence (Sset _t'12 (Ederef (Ebinop Oadd (Etempvar _cps (tptr
  tuint)) (Etempvar _j__2 tulong) (tptr tuint)) tuint)) (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tuint) (Etempvar _n
  tulong) tint) tstmt_digs Sskip))).

(* tstmt_passloop is the for loop over j__2 with the body tstmt_passbody. *)
Lemma tstmt_passloop_eq: tstmt_passloop = Ssequence (Sset _j__2 (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _j__2 tulong) (Etempvar _m tulong) tint) Sskip Sbreak)
    tstmt_passbody)
  (Sset _j__2 (Ebinop Oadd (Etempvar _j__2 tulong) (Econst_int (Int.repr 1) tint) tulong))).
Proof. reflexivity. Qed.

(* The constant (unsigned) -1 of the overflow test delta > 0xFFFFFFFF, converted to unsigned long: maxint. *)
Lemma uint_m1_long: Int64.repr (Int.unsigned (Int.repr (-1))) = Int64.repr maxint.
Proof. reflexivity. Qed.
