(* Intermediate Games *)
require import AllCore FMap FSet Distr NSL.
import GWAKEc AEADc.

(* Inlining and removing psk from instance state *)
module Game1 = {
  var state_map: (id * int, role * instance_state) fmap
  var psk_map: (id * id, pskey) fmap

  proc init_mem() : unit = {
    state_map <- empty;
    psk_map <- empty;
  }

  proc gen_pskey(a: id, b: id) : unit = {
    var k;
    if ((a, b) \notin psk_map) {
      k <$ dpskey;
      psk_map.[(a, b)] <- k;
    }
  }
  
  proc send_msg1(a, i, b) = {
    var na, ca;
    var mo <- None;
 
    if ((a, i) \notin state_map /\ (a, b) \in psk_map) {
      na <$ dnonce;
      ca <$ enc (oget psk_map.[(a, b)]) (msg1_data a b) na;
      mo <- Some ca;
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, na, ca) (a, ca));
    }
    return mo;
  }


  proc send_msg2(b, j, m1) = {
    var a, ca, role, st, nb, cb;
    var mo <- None;
 
    (a, ca) <- m1;
    (role, st) <- oget state_map.[(b, j)];
    if ((b, j) \notin state_map /\ (a, b) \in psk_map) {
      if (dec (oget psk_map.[(a, b)]) (msg1_data a b) ca is Some na) {
        nb <$ dnonce;
        cb <$ enc (oget psk_map.[(a, b)]) (msg2_data a b ca) nb;
        mo <- Some cb;
        state_map.[(b, j)] <- (Responder, RPending (a, witness, na, nb, ca, cb) m1 cb);
      } else {
        state_map.[(b, j)] <- (Responder, Aborted);
      }
    }
    return mo;
  }

  proc send_msg3(a, i, m2) = {
    var role, st, b, psk, na, ca, skey, ok, caf;
    var mo <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      if (st is IPending s m1) {
        (b, psk, na, ca) <- s;
        if (dec (oget psk_map.[(a, b)]) (msg2_data a b ca) m2 is Some nb) {
          ok <$ dnonce;
          caf <$ enc (oget psk_map.[(a, b)]) (msg3_data a b ca m2) ok;
          mo <- Some caf;
          skey <- prf (na, nb) (a, b);
          state_map.[(a, i)] <- (Initiator, Accepted (m1, m2, caf) skey);
         } else {
          state_map.[(a, i)] <- (Initiator, Aborted);
        }
      }
    }
    return mo;
  }

  proc send_fin(b, j, m3) = {
    var role, st, a, psk, na, nb, ca, cb, skey;
    var mo <- None;

    if ((b, j) \in state_map) {
      (role, st) <- oget state_map.[(b, j)];
      if (st is RPending s m1 m2) {
        (a, psk, na, nb, ca, cb) <- s;
        if (dec (oget psk_map.[(a, b)]) (msg3_data a b ca cb) m3 is Some nok) {
          skey <- prf (na, nb) (a, b);
          state_map.[(b, j)] <- (Responder, Accepted (m1, m2, m3) skey);
          mo <- Some ();
        } else {
          state_map.[(b, j)] <- (Responder, Aborted);
        }
      }
    }
    return mo;
  }

  proc rev_skey(a, i) = {
    var role, st, p_role, p_st, ps, p, k;
    var ko <- None;
 
    if ((a, i) \in state_map) {
      (role, st) <- oget state_map.[(a, i)];
      match st with
      | Accepted trace k' => {
        k <- k';
        (* Get partners *)
        ps <- get_partners (a, i) (Some trace) role state_map;
        if (card ps <= 1) {
          ps <- get_observed_partners (a, i) state_map;
          (* If we have no observed partners then, we can test *)
          if (card ps <> 0) {
            (* If a partner has revealed something, we must use the same key *)
            p <- pick ps;
            (p_role, p_st) <- oget state_map.[p];
            if (p_st is Observed _ p_k) {
              k <- p_k;
            }
          }
          ko <- Some k;
          state_map.[(a, i)] <- (role, Observed trace k);
        }
      }
      | Observed _ k'  => ko <- Some k';
      | IPending _ _   => { }
      | RPending _ _ _ => { }
      | Aborted        => { }
      end;
    }
    return ko;
  }
 
  proc test = rev_skey
}.

(* Decmap instead of real enc/dec *)
module Game2 = Game1 with {
  var dec_map: ((id * id) * msg_data * ctxt, nonce) fmap
  var bad : bool
  
  proc init_mem [
    -1 + { dec_map <- empty; },
    -1 + { bad <- false; }
  ]
  
  proc send_msg1 [
    ^if.^na<$ -,
    ^if.^ca<$ ~ {
      ca <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, ca) \in dec_map;
      na <$ dnonce;
      dec_map.[((a,b), msg1_data a b, ca)] <- na;
     }
  ]

  proc send_msg2 [
    ^if.^match ~ (dec_map.[((a, b), msg1_data a b, ca)]),
    ^if.^match#Some.^nb<$ -,
    ^if.^match#Some.^cb<$ ~ {
      cb <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, cb) \in dec_map;
      nb <$ dnonce;
      dec_map.[((a,b), msg2_data a b ca, cb)] <- nb;
     }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match ~ (dec_map.[((a, b), msg2_data a b ca, m2)]),
    ^if.^match#IPending.^match#Some.^ok<$ -,
    ^if.^match#IPending.^match#Some.^caf<$ ~ {
      caf <$ dctxt;
      bad <- bad \/ exists pk ad, (pk, ad, caf) \in dec_map;
      ok <$ dnonce;
      dec_map.[((a,b), msg3_data a b ca m2, caf)] <- ok;
     }
  ]
  proc send_fin [
    ^if.^match#RPending.^match ~ (dec_map.[((a, b), msg3_data a b ca cb, m3)])
  ]
}.

(* No ctxt collisions *)
module Game3 = Game2 with {
  proc send_msg1 [
    ^if.^bad<- + (!bad)
  ]

  proc send_msg2 [
    ^if.^match#Some.^bad<- + (!bad)
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^bad<- + (!bad)
  ]
}.

(* Simplify nonce retrieval *)
module Game4 = Game3 with {
  proc send_msg1 [
    ^if.^if.^state_map<- ~ {
      state_map.[(a, i)] <- (Initiator, IPending (b, witness, witness, ca) (a, ca));
    }
  ]

  proc send_msg2 [
    ^if.^match#Some.^if.^state_map<- ~ {
      state_map.[(b, j)] <- (Responder, RPending (a, witness, witness, witness, ca, cb) m1 cb);
    }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ { 
      skey <- prf (oget (dec_map.[((a, b), msg1_data a b, ca)]), nb) (a, b);
    } 
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- prf (oget (dec_map.[((a, b), msg1_data a b, ca)]), oget (dec_map.[((a, b), msg2_data a b ca, cb)])) (a, b);
    }
  ]
}.

(* Delay nonce sampling *)
module Game5 = Game4 with {
  var prfkey_map : (ctxt, nonce * nonce) fmap
  
  proc init_mem [
    -1 + { prfkey_map <- empty; }
  ]

  proc send_msg1 [
    ^if.^if.^na<$ -,
    ^if.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg1_data a b, ca)] <- witness;
    }
  ]

  proc send_msg2 [
    ^if.^match#Some.^if.^nb<$ -,
    ^if.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg2_data a b ca, cb)] <- witness;
    }
  ]

  proc send_msg3 [
    ^if.^match#IPending.^match#Some.^if.^ok<$ -,
    ^if.^match#IPending.^match#Some.^if.^dec_map<- ~ {
      dec_map.[((a, b), msg3_data a b ca m2, caf)] <- witness;
    },
    ^if.^match#IPending.^match#Some.^if.^skey<- ~ { 
      (na, ok) <$ dnonce `*` dnonce;
      prfkey_map.[caf] <- (na, ok);
      skey <- prf (na, ok) (a, b);
    } 
  ]

  proc send_fin [
    ^if.^match#RPending.^match#Some.^skey<- ~ {
      skey <- prf (oget prfkey_map.[m3]) (a, b);
    }
  ]
}.

(* ------------------------------------------------------------------------------------------ *)
(* Game 0 invariants *)

inductive GWAKE0_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| GWAKE0_undef of
    (sm.[a, i] = None)
| GWAKE0_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| GWAKE0_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & (pskm.[a, b] = Some kab)
| GWAKE0_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & (pskm.[b, a] = Some kba)
| GWAKE0_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| GWAKE0_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma GWAKE0_inv_neq a i c j v sm psk:
! (c = a /\ j = i) =>
GWAKE0_inv sm psk c j =>
GWAKE0_inv sm.[(a, i) <- v] psk c j.
proof.
move=> neq
[ 
| r 
| b na c1 kab
| b na nb c1 c2 kba
| r tr k
| r tr k
].
+ move=> smbj.
  apply GWAKE0_undef.
  by rewrite get_set_neqE.
+ move=> smbj.
  apply (GWAKE0_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ move=> smbj pskcb.
  apply (GWAKE0_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ move=> smbj pskcb.
  apply (GWAKE0_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ move=> smbj.
  apply (GWAKE0_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
move=> smbj.
apply (GWAKE0_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

hoare GWAKE0_inv_gen_pskey: GWAKE0(NSL).gen_pskey:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
if => //.
auto => />.
move => &m inv1 inv3 k _ a' i'.
case: (inv1 a' i'). 
+ move=> sm.
  by apply GWAKE0_undef.
+ move => r sm.
  exact (GWAKE0_aborted _ _ _ _ r).
+ move => b na c1 kab sm psk.
  apply (GWAKE0_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).
+ move => b na nb c1 c2 kba sm psk.
  apply (GWAKE0_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  smt(get_setE).
+ move => r tr k'.
  exact (GWAKE0_accepted _ _ _ _ r tr k').
move => r tr k'.
exact (GWAKE0_observed _ _ _ _ r tr k').
qed.
    
hoare GWAKE0_inv_send_msg1: GWAKE0(NSL).send_msg1:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proc; inline *.
sp; if => //.
auto => /> &m inv ainin abin na _ ca _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (GWAKE0_ipending _ _ _ _ b{m} na ca (oget GWAKEb.psk_map.[(a, b)]{m})).
  - by rewrite get_set_sameE.
  smt().
apply GWAKE0_inv_neq => //.
exact inv.
qed.
    
hoare GWAKE0_inv_send_msg2: GWAKE0(NSL).send_msg2:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ match None 2; 1: by auto.
  auto => /> &m decn st inv bjnin abin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (GWAKE0_aborted _ _ _ _ Responder). smt(get_setE).
  apply GWAKE0_inv_neq => //.
  exact inv.
match Some 5; 1: auto => /#.
auto => /> &m decn st inv bjnin abin n _ cb0 cin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_rpending _ _ _ _ a0{m} na{m} n ca{m} cb0 (oget GWAKEb.psk_map.[(a0, b)]{m})).
  - by rewrite get_setE eq_ai //=. 
  smt().
apply GWAKE0_inv_neq => //.
exact inv.
qed.

hoare GWAKE0_inv_send_msg3: GWAKE0(NSL).send_msg3:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: auto.
sp; match.
- match None 2; 1: by auto.
  auto => /> &m decn st inv aiin a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (GWAKE0_aborted _ _ _ _ Initiator). smt(get_setE).
  apply GWAKE0_inv_neq => //.
  exact inv.
match Some 6; 1: auto => /#.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply GWAKE0_inv_neq => //.
exact inv.
qed.

hoare GWAKE0_inv_send_fin: GWAKE0(NSL).send_fin:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
- match None 2; 1: by auto.
  auto => /> &m decn st inv bjin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (GWAKE0_aborted _ _ _ _ Responder). smt(get_setE).
  apply GWAKE0_inv_neq => //.
  exact inv.
match Some 4; 1: auto => /#.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (GWAKE0_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply GWAKE0_inv_neq => //.
exact inv.
qed.

hoare GWAKE0_inv_rev_skey: GWAKE0(NSL).rev_skey:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k).
  smt(get_setE).
apply GWAKE0_inv_neq => //.
exact inv.
qed.

hoare GWAKE0_inv_test: GWAKE0(NSL).test:
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i)
==> 
    (forall a i, GWAKE0_inv GWAKEb.state_map GWAKEb.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
auto => /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (GWAKE0_observed _ _ _ _ role{m} trace{m} k).
  smt(get_setE).
apply GWAKE0_inv_neq => //.
exact inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 1 invariants *)

inductive Game1_inv (sm: (id * int, role * instance_state) fmap) (pskm : (id * id, pskey) fmap) (a: id) (i: int) =
| Game1_undef of
    (sm.[a, i] = None)
| Game1_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Game1_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & ((a, b) \in pskm)
| Game1_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & ((b, a) \in pskm)
| Game1_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| Game1_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma Game1_inv_neq a i c j v sm psk:
! (c = a /\ j = i) =>
Game1_inv sm psk c j =>
Game1_inv sm.[(a, i) <- v] psk c j.
proof.
move=> neq
[ 
| r 
| b na c1 kab
| b na nb c1 c2 kba
| r tr k
| r tr k
].
+ move=> smbj.
  apply Game1_undef.
  by rewrite get_set_neqE.
+ move=> smbj.
  apply (Game1_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ move=> smbj pskcb.
  apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ move=> smbj pskcb.
  apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ move=> smbj.
  apply (Game1_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
move=> smbj.
apply (Game1_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

hoare Game1_inv_gen_pskey: Game1.gen_pskey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
if => //.
auto => />.
move => &m inv1 inv3 k _ a' i'.
case: (inv1 a' i'). 
+ move=> sm.
  by apply Game1_undef.
+ move => r sm.
  exact (Game1_aborted _ _ _ _ r).
+ move => b na c1 kab sm psk.
  apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).
+ move => b na nb c1 c2 kba sm psk.
  apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  smt(get_setE).
+ move => r tr k'.
  exact (Game1_accepted _ _ _ _ r tr k').
move => r tr k'.
exact (Game1_observed _ _ _ _ r tr k').
qed.
    
hoare Game1_inv_send_msg1: Game1.send_msg1:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
auto => /> &m inv ainin abin na _ ca _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game1_ipending _ _ _ _ b{m} na ca witness).
  - by rewrite get_set_sameE.
  smt().
apply Game1_inv_neq => //.
exact inv.
qed.
    
hoare Game1_inv_send_msg2: Game1.send_msg2:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Responder). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv bjnin abin n _ cb0 cin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_rpending _ _ _ _ a{m} na{m} n ca{m} cb0 witness).
  - by rewrite get_setE eq_ai //=. 
  smt().
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game1_inv_send_msg3: Game1.send_msg3:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Initiator). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv aiin n _ ca0 cin a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game1_inv_send_fin: Game1.send_fin:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Responder). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game1_inv_rev_skey: Game1.rev_skey:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
smt(get_setE).
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game1_inv_test: Game1.test:
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i)
==> 
    (forall a i, Game1_inv Game1.state_map Game1.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
smt(get_setE).
apply Game1_inv_neq => //.
exact inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 2 invariants *)

hoare Game2_inv_gen_pskey: Game2.gen_pskey:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
if => //.
auto => />.
move => &m inv1 inv3 k _ a' i'.
case: (inv1 a' i'). 
+ move=> sm.
  by apply Game1_undef.
+ move => r sm.
  exact (Game1_aborted _ _ _ _ r).
+ move => b na c1 kab sm psk.
  apply (Game1_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).
+ move => b na nb c1 c2 kba sm psk.
  apply (Game1_rpending _ _ _ _ b na nb c1 c2 kba) => //.
  smt(get_setE).
+ move => r tr k'.
  exact (Game1_accepted _ _ _ _ r tr k').
move => r tr k'.
exact (Game1_observed _ _ _ _ r tr k').
qed.
    
hoare Game2_inv_send_msg1: Game2.send_msg1:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
auto => /> &m inv ainin abin ca _ na _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game1_ipending _ _ _ _ b{m} na ca witness).
  - by rewrite get_set_sameE.
  smt().
apply Game1_inv_neq => //.
exact inv.
qed.
    
hoare Game2_inv_send_msg2: Game2.send_msg2:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Responder). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv bjnin abin cb0 _ n cin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_rpending _ _ _ _ a{m} na{m} n ca{m} cb0 witness).
  - by rewrite get_setE eq_ai //=. 
  smt().
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game2_inv_send_msg3: Game2.send_msg3:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Initiator). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv aiin ca0 _ n cin a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Initiator (m1{m}, m2{m}, ca0) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game2_inv_send_fin: Game2.send_fin:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game1_aborted _ _ _ _ Responder). smt(get_setE).
  apply Game1_inv_neq => //.
  exact inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => [eq_ai|neq_ai].
+ rewrite /get_as_Some //=.
  apply (Game1_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  - by rewrite get_setE eq_ai //=. 
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game2_inv_rev_skey: Game2.rev_skey:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
smt(get_setE).
apply Game1_inv_neq => //.
exact inv.
qed.

hoare Game2_inv_test: Game2.test:
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i)
==> 
    (forall a i, Game1_inv Game2.state_map Game2.psk_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => [eq_ai|neq_ai].
- apply (Game1_observed _ _ _ _ role{m} trace{m} k).
smt(get_setE).
apply Game1_inv_neq => //.
exact inv.
qed.

(* ------------------------------------------------------------------------------------------ *)
(* Game 3 invariants *)
inductive Game3_inv 
  (sm: (id * int, role * instance_state) fmap)
  (dm : ((id * id) * msg_data * ctxt, nonce) fmap)
  (a: id) (i: int)
=
| Game3_undef of
    (sm.[a, i] = None)
| Game3_aborted r of
    (sm.[a, i] = Some (r, Aborted))
| Game3_ipending b na c1 kab of
    (sm.[a, i] = Some (Initiator, IPending (b, kab, na, c1) (a, c1)))
  & (dm.[((a, b), msg1_data a b, c1)] = Some na)
| Game3_rpending b nb na c1 c2 kba of
    (sm.[a, i] = Some (Responder, RPending (b, kba, nb, na, c1, c2) (b, c1) c2))
  & (dm.[((b, a), msg1_data b a, c1)] = Some nb)
  & (dm.[((b, a), msg2_data b a c1, c2)] = Some na)
| Game3_accepted r tr k of
    (sm.[a, i] = Some (r, Accepted tr k))
| Game3_observed r tr k of
    (sm.[a, i] = Some (r, Observed tr k)).

lemma Game3_inv_neq_sm a i c j v sm dm:
! (c = a /\ j = i) =>
Game3_inv sm dm c j =>
Game3_inv sm.[(a, i) <- v] dm c j.
proof.
move=> neq
[ 
  smbj
| r smbj
| b na c1 kab smbj dmcb
| b na nb c1 c2 kba smbj dmcb
| r tr k smbj
| r tr k smbj
].
+ apply Game3_undef.
  by rewrite get_set_neqE.
+ apply (Game3_aborted _ _ _ _ r).
  by rewrite get_set_neqE.
+ apply (Game3_ipending _ _ _ _ b na c1 kab) => //.
  by rewrite get_set_neqE.
+ apply (Game3_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  by rewrite get_set_neqE.
+ apply (Game3_accepted _ _ _ _ r tr k)=> //.
  by rewrite get_set_neqE.
apply (Game3_observed _ _ _ _ r tr k)=> //.
by rewrite get_set_neqE.
qed.

lemma Game3_inv_neq_dm a i c n sm (dm : (_, _) fmap):
! (exists pk ad, (pk, ad, c) \in dm) =>
Game3_inv sm dm a i =>
forall pk ad, Game3_inv sm dm.[(pk, ad, c) <- n] a i.
proof.
move=> neq
[ 
  smbj pk ad
| r smbj pk ad
| b na c1 kab smbj dmcb pk ad
| b na nb c1 c2 kba smbj dmnb dmna pk ad
| r tr k smbj pk ad
| r tr k smbj pk ad
].
+ exact Game3_undef.
+ exact (Game3_aborted _ _ _ _ r).
+ apply (Game3_ipending _ _ _ _ b na c1 kab) => //.
  smt(get_setE).  
+ apply (Game3_rpending _ _ _ _ b na nb c1 c2 kba)=> //.
  + smt(get_setE).  
  smt(get_setE).  
+ exact (Game3_accepted _ _ _ _ r tr k)=> //.
exact (Game3_observed _ _ _ _ r tr k)=> //.
qed.

hoare Game3_inv_gen_pskey: Game3.gen_pskey:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
if => //.
by auto.
qed.
    
hoare Game3_inv_send_msg1: Game3.send_msg1:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ inv ainin abin _ uniq na _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game3_ipending _ _ _ _ b{m} na ca{m} witness).
  - by rewrite get_set_sameE.
  by rewrite get_set_sameE.
apply Game3_inv_neq_sm => //.
apply Game3_inv_neq_dm => //.
exact inv.
qed.
    
hoare Game3_inv_send_msg2: Game3.send_msg2:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match.
+ auto => /> &m decn st inv bjnin abin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game3_aborted _ _ _ _ Responder).
    by rewrite get_set_sameE. 
  apply Game3_inv_neq_sm => //.
  exact inv.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ decn st inv bjnin abin _ bad n _ a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ apply (Game3_rpending _ _ _ _ a{m} na{m} n ca{m} cb{m} witness).
  - by rewrite get_set_sameE.
  - by rewrite get_set_neqE /#. 
  by rewrite get_set_sameE.
apply Game3_inv_neq_sm => //.
apply Game3_inv_neq_dm => //.
exact inv.
qed.

hoare Game3_inv_send_msg3: Game3.send_msg3:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 2..5: auto.
sp; match.
+ auto => /> &m decn st inv abin a' i'.
  case ((a', i') = (a, i){m}) => /> => [|neq_ai].
  - apply (Game3_aborted _ _ _ _ Initiator).
    by rewrite get_set_sameE. 
  apply Game3_inv_neq_sm => //.
  exact inv.
seq 1 : (#pre); 1: by auto.
case (Game3.bad).
+ by rcondf ^if; auto=> />.
sp; if=> //.
auto => /> &m _ decn st inv aiin _ bad ok _ a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Initiator (m1{m}, m2{m}, caf{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE.
apply Game3_inv_neq_sm => //.
apply Game3_inv_neq_dm => //.
exact inv.
qed.

hoare Game3_inv_send_fin: Game3.send_fin:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1: auto; 2..4: auto.
sp; match.
- auto => /> &m decn st inv bjin a' i'.
  case ((a', i') = (b, j){m}) => /> => [|neq_ai].
  - apply (Game3_aborted _ _ _ _ Responder).
    by rewrite get_set_sameE.
  apply Game3_inv_neq_sm => //.
  exact inv.
auto => /> &m decn st inv bjin a' i'.
case ((a', i') = (b, j){m}) => /> => [|neq_ai].
+ apply (Game3_accepted _ _ _ _ Responder (m1{m}, m2{m}, m3{m}) (prf (na{m}, nb{m}) (a{m}, b{m}))).
  by rewrite get_set_sameE. 
apply Game3_inv_neq_sm => //.
exact inv.
qed.

hoare Game3_inv_rev_skey: Game3.rev_skey:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE. 
apply Game3_inv_neq_sm => //.
exact inv.
qed.

hoare Game3_inv_test: Game3.test:
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i)
==> 
    (forall a i, Game3_inv Game3.state_map Game3.dec_map a i).
proof.
proc; inline *.
sp; if => //.
sp; match; 1..2: auto; 2..3: auto.
sp; if => //.
wp 2.
conseq (: _ ==> true); last by auto.
move=> /> &m st inv aiin _ k a' i'.
case ((a', i') = (a, i){m}) => /> => [|neq_ai].
- apply (Game3_observed _ _ _ _ role{m} trace{m} k).
  by rewrite get_set_sameE. 
apply Game3_inv_neq_sm => //.
exact inv.
qed.
