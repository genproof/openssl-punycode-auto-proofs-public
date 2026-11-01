(* The model of the openssl-punycode laws, in plain Coq: a transcription of harness/puny_ref.h (RFC 3492 decoding
   and encoding, RFC 3629 UTF-8, the static-WPACKET sink and the conversion of ossl_a2ulabel).

   Integers are Z (mathematical); the C reference uses 64-bit arithmetic with explicit comparisons against
   maxint = 2^32 - 1, and no 64-bit overflow happens there, so the C values are these.  Octets and code points are
   Z (octets 0..255).  Loops are Fixpoints with fuel; the definitions say how much fuel suffices (see each).

  *)
From Coq Require Import ZArith List Lia.
Require Import VST.floyd.functional_base.
Import ListNotations.
Local Open Scope Z_scope.

Definition maxint : Z := 4294967295.          (* PR_MAXINT, OpenSSL's maxint: 2^32 - 1 *)
Definition label_cap : Z := 512.              (* PR_LABEL_CAP, LABEL_BUF_SIZE *)

(* ---------------------------------------------------------------------- *)
(* RFC 3492 section 5 and 6.1                                             *)
(* ---------------------------------------------------------------------- *)

(* pr_digit_value: the digit-value of an octet, 36 when it has none. *)
Definition digit_value (c: Z) : Z :=
  if (65 <=? c) && (c <=? 90) then c - 65
  else if (97 <=? c) && (c <=? 122) then c - 97
  else if (48 <=? c) && (c <=? 57) then c - 48 + 26
  else 36.

(* pr_digit_char: the (lowercase) octet of a digit-value d < 36. *)
Definition digit_char (d: Z) : Z := if d <? 26 then 97 + d else 48 + (d - 26).

(* pr_threshold *)
Definition threshold (k bias: Z) : Z :=
  if k <=? bias then 1 else if bias + 26 <=? k then 26 else k - bias.

(* The loop of pr_adapt: while delta > 455, delta := delta / 35 and k := k + 36.  Fuel f suffices when
   delta < 455 * 35^f (adapt uses 64: every delta < 2^64). *)
Fixpoint adapt_loop (fuel: nat) (delta k: Z) : Z :=
  match fuel with
  | O => k + (36 * delta) / (delta + 38)
  | S f => if 455 <? delta then adapt_loop f (delta / 35) (k + 36) else k + (36 * delta) / (delta + 38)
  end.

(* pr_adapt (RFC 3492 6.1); numpoints >= 1. *)
Definition adapt (delta numpoints: Z) (firsttime: bool) : Z :=
  let d := if firsttime then delta / 700 else delta / 2 in
  let d := d + d / numpoints in
  adapt_loop 64 d 0.

(* ---------------------------------------------------------------------- *)
(* RFC 3492 6.2: decoding (pr_decode)                                     *)
(* ---------------------------------------------------------------------- *)

(* The position of the last delimiter '-' (45) of the input, 0 when there is none. *)
Fixpoint last_delim_from (l: list Z) (j acc: Z) : Z :=
  match l with
  | [] => acc
  | c :: l' => last_delim_from l' (j + 1) (if c =? 45 then j else acc)
  end.
Definition last_delim (l: list Z) : Z := last_delim_from l 0 0.

(* The longest prefix of basic code points (< 128). *)
Fixpoint basic_prefix (l: list Z) : list Z :=
  match l with
  | [] => []
  | c :: l' => if c <? 128 then c :: basic_prefix l' else []
  end.

(* Insert x at position i of l (0 <= i <= Zlength l). *)
Definition insert_at (i x: Z) (l: list Z) : list Z := sublist 0 i l ++ x :: sublist i (Zlength l) l.

Section Decode.
Variable inp: list Z.

(* The digit loop of one delta: from position pos with i, w, k and the bias; Some (i', pos') at the digit below
   its threshold (pos' the position after it), None on a failure (no digit left, no digit-value, an overflow).
   Fuel: exactly Z.to_nat (Zlength inp - pos) (each iteration consumes one octet; fuel 0 = no octet left). *)
Fixpoint digits (fuel: nat) (pos i w k bias: Z) : option (Z * Z) :=
  match fuel with
  | O => None
  | S f =>
    if Zlength inp <=? pos then None else
    let d := digit_value (Znth pos inp) in
    if 36 <=? d then None else
    let i1 := i + d * w in
    if maxint <? i1 then None else
    let t := threshold k bias in
    if d <? t then Some (i1, pos + 1) else
    let w1 := w * (36 - t) in
    if maxint <? w1 then None else
    digits f (pos + 1) i1 w1 (k + 36) bias
  end.

(* The main loop: one delta per iteration, from position pos with n, i, bias and the output so far out.
   (true, out) at the end of the input, (false, output so far) on a failure (the digit loop failed, n overflows,
   or the output already holds cap code points).
   Fuel: any f >= Zlength inp - pos (each iteration consumes at least one octet); decode uses length inp. *)
Fixpoint steps (fuel: nat) (cap pos n i bias: Z) (out: list Z) : bool * list Z :=
  match fuel with
  | O => (true, out)
  | S f =>
    if Zlength inp <=? pos then (true, out) else
    match digits (Z.to_nat (Zlength inp - pos)) pos i 1 36 bias with
    | None => (false, out)
    | Some (i1, pos1) =>
      let c := Zlength out in
      let bias1 := adapt (i1 - i) (c + 1) (i =? 0) in
      let n1 := n + i1 / (c + 1) in
      if maxint <? n1 then (false, out) else
      let i2 := i1 mod (c + 1) in
      if cap <=? c then (false, out) else
      steps f cap pos1 n1 (i2 + 1) bias1 (insert_at i2 n1 out)
    end
  end.

(* pr_decode into cap code points: (ok, the output so far).  The array of the C function then holds the output
   followed by its initial values (positions Zlength out .. cap - 1 untouched); d.count = Zlength out. *)
Definition decode (cap: Z) : bool * list Z :=
  let b := last_delim inp in
  if cap <? b then (false, []) else
  let bp := basic_prefix (sublist 0 b inp) in
  if Zlength bp <? b then (false, bp) else
  steps (length inp) cap (if b =? 0 then 0 else b + 1) 128 0 72 bp.

End Decode.

(* ---------------------------------------------------------------------- *)
(* RFC 3492 6.3: encoding (pr_encode)                                     *)
(* ---------------------------------------------------------------------- *)

(* The digits of q (the generalized variable-length integer) for the bias, from k: the octets the encoder writes.
   Fuel: q is at least divided by 10 per digit; 64 suffices for q < 2^64 (pr_encode's q <= maxint). *)
Fixpoint enc_digits (fuel: nat) (q k bias: Z) : list Z :=
  match fuel with
  | O => [digit_char q]
  | S f =>
    let t := threshold k bias in
    if q <? t then [digit_char q]
    else digit_char (t + (q - t) mod (36 - t)) :: enc_digits f ((q - t) / (36 - t)) (k + 36) bias
  end.

Section Encode.
Variable cps: list Z.

(* "let m = the minimum code point >= n in the input" (maxint + 1 when there is none). *)
Definition min_ge (n: Z) : Z :=
  fold_left (fun acc c => if (n <=? c) && (c <? acc) then c else acc) cps (maxint + 1).

(* One pass over the code points l (a suffix of cps) for the code point n: (delta, bias, h, out) after it, None on
   an overflow of delta.  b: the number of basic code points. *)
Fixpoint enc_pass (l: list Z) (n delta bias h b: Z) (out: list Z) : option (Z * Z * Z * list Z) :=
  match l with
  | [] => Some (delta, bias, h, out)
  | c :: l' =>
    if c <? n then
      if maxint <? delta + 1 then None else enc_pass l' n (delta + 1) bias h b out
    else if c =? n then
      enc_pass l' n 0 (adapt delta (h + 1) (h =? b)) (h + 1) b (out ++ enc_digits 64 delta 36 bias)
    else enc_pass l' n delta bias h b out
  end.

(* The rounds (one per code point value >= 128 present, in increasing order).  Fuel: each round handles at least
   one code point; encode uses length cps + 1. *)
Fixpoint enc_rounds (fuel: nat) (n delta bias h b: Z) (out: list Z) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
    if Zlength cps <=? h then Some out else
    let mm := min_ge n in
    if (maxint <? delta) || ((maxint - delta) / (h + 1) <? mm - n) then None else
    match enc_pass cps mm (delta + (mm - n) * (h + 1)) bias h b out with
    | None => None
    | Some (delta1, bias1, h1, out1) => enc_rounds f (mm + 1) (delta1 + 1) bias1 h1 b out1
    end
  end.

(* pr_encode without the output bound: Some (the octets), None on an overflow.  pr_encode(cps, m, o, ocap, &olen)
   returns 1 exactly when this is Some e with Zlength e <= ocap, and then o[0..olen) = e. *)
Definition encode : option (list Z) :=
  let basics := filter (fun c => c <? 128) cps in
  let b := Zlength basics in
  enc_rounds (S (length cps)) 128 0 72 b b (if 0 <? b then basics ++ [45] else basics).

End Encode.

(* ---------------------------------------------------------------------- *)
(* RFC 3629: UTF-8 (pr_utf8, codepoint2utf8)                              *)
(* ---------------------------------------------------------------------- *)

(* The octets of code point c; [] for c > 0x10FFFF (surrogates are encoded as three octets). *)
Definition utf8 (c: Z) : list Z :=
  if c <? 128 then [c]
  else if c <? 2048 then [192 + c / 64; 128 + c mod 64]
  else if c <? 65536 then [224 + c / 4096; 128 + (c / 64) mod 64; 128 + c mod 64]
  else if c <=? 1114111 then [240 + c / 262144; 128 + (c / 4096) mod 64; 128 + (c / 64) mod 64; 128 + c mod 64]
  else [].

(* ---------------------------------------------------------------------- *)
(* The static WPACKET sink (pr_sink / pr_put)                             *)
(* ---------------------------------------------------------------------- *)

(* A sink of capacity cap: the octets written (from the start of the buffer) and the short flag. *)
Definition sink : Type := (list Z * bool)%type.

(* pr_put: a write of bs is done when it fits in the room left, else not done at all and marks the sink short;
   writing nothing changes nothing. *)
Definition put (cap: Z) (k: sink) (bs: list Z) : sink :=
  if Zlength bs =? 0 then k
  else if cap - Zlength (fst k) <? Zlength bs then (fst k, true)
  else (fst k ++ bs, snd k).

(* ---------------------------------------------------------------------- *)
(* The conversion of ossl_a2ulabel (pr_a2ulabel)                          *)
(* ---------------------------------------------------------------------- *)

(* The labels of s: split at every '.' (46), empty labels included; never []. *)
Fixpoint labels_from (s: list Z) (cur: list Z) : list (list Z) :=
  match s with
  | [] => [cur]
  | c :: s' => if c =? 46 then cur :: labels_from s' [] else labels_from s' (cur ++ [c])
  end.
Definition labels (s: list Z) : list (list Z) := labels_from s [].

(* The ACE prefix "xn--" in any case. *)
Definition is_ace (l: list Z) : bool :=
  (4 <=? Zlength l) && ((Znth 0 l =? 120) || (Znth 0 l =? 88)) && ((Znth 1 l =? 110) || (Znth 1 l =? 78))
  && (Znth 2 l =? 45) && (Znth 3 l =? 45).

(* The UTF-8 forms of the code points, written one after the other; false at the first code point > 0x10FFFF
   (with the sink at that moment). *)
Fixpoint put_utf8s (cap: Z) (k: sink) (cps: list Z) : bool * sink :=
  match cps with
  | [] => (true, k)
  | c :: r => if Zlength (utf8 c) =? 0 then (false, k) else put_utf8s cap (put cap k (utf8 c)) r
  end.

(* One label: false when it does not decode (or a code point is above 0x10FFFF). *)
Definition label_step (cap: Z) (k: sink) (l: list Z) : bool * sink :=
  if is_ace l then
    let rest := sublist 4 (Zlength l) l in
    if maxint <=? Zlength rest then (false, k) else
    match decode rest label_cap with
    | (true, cps) => put_utf8s cap k cps
    | (false, _) => (false, k)
    end
  else (true, put cap k l).

(* The labels, each followed by '.' except the last, then the NUL: the result (-1, 0, 1) and the sink. *)
Fixpoint a2u_labels (cap: Z) (k: sink) (ls: list (list Z)) : Z * sink :=
  match ls with
  | [] => let k1 := put cap k [0] in (if snd k1 then 0 else 1, k1)
  | l :: ls' =>
    let (ok, k1) := label_step cap k l in
    if ok then
      match ls' with
      | [] => let k2 := put cap k1 [0] in (if snd k2 then 0 else 1, k2)
      | _ => a2u_labels cap (put cap k1 [46]) ls'
      end
    else (-1, k1)
  end.

(* pr_a2ulabel(s, n, k, cps) on a fresh sink of capacity cap (s: the string, no NUL): the result and the octets
   written to the start of the buffer (every other octet of it keeps its value). *)
Definition a2ulabel (s: list Z) (cap: Z) : Z * list Z :=
  let (r, k) := a2u_labels cap ([], false) (labels s) in (r, fst k).
