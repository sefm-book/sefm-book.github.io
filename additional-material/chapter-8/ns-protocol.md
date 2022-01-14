# ns-protocol.csp
```
-------------------------------------------
-- 8.5.1 Encoding the message space in CSPm
-------------------------------------------

datatype MESSAGE = User.USER | Nonce.NONCE | Key.KEY | Enc.KEY.MESSAGE | Sq.Seq(MESSAGE)

datatype USER = A | B | I
datatype NONCE = NA | NB | NI
datatype KEY = PKA | PKB | PKI | SKA | SKB | SKI
PKEY = {PKA, PKB, PKI}
SKEY = {SKA, SKB, SKI}

pk(A) = PKA
pk(B) = PKB
pk(I) = PKI
sk(PKA) = SKA
sk(PKB) = SKB
sk(PKI) = SKI

datatype MESSAGE_LABEL = Msg1 | Msg2 | Msg3

MSG1_CONT = { Enc.pkb.(Sq.<Nonce.na, User.a>) | pkb <- PKEY, na <- NONCE, a <- USER }
MSG1_BODY = { (Msg1, c) | c <- MSG1_CONT }

MSG2_CONT = {Enc.pka.(Sq.<Nonce.na, Nonce.nb>) | pka <- PKEY, na <- NONCE, nb <- NONCE }
MSG2_BODY = { (Msg2, c) | c <- MSG2_CONT }

MSG3_CONT = { Enc.pkb.(Sq.<Nonce.nb>) | pkb <- PKEY, nb <- NONCE }
MSG3_BODY = { (Msg3, c) | c <- MSG3_CONT }

MSG_CONT = Union({MSG1_CONT, MSG2_CONT, MSG3_CONT})
MSG_BODY = Union({MSG1_BODY, MSG2_BODY, MSG3_BODY})

--------------------------
-- 8.5.2 Protocol encoding
--------------------------

channel send : USER . USER . MSG_BODY
channel recv : USER . USER . MSG_BODY

channel running, commit : USER . USER . NONCE

User_A = [] b : diff(USER,{A}) @
         send.A.b.(Msg1, Enc.pk(b).(Sq.<Nonce.NA, User.A>))
      -> [] nb : NONCE @
         recv.A.b.(Msg2, Enc.PKA.(Sq.<Nonce.NA, Nonce.nb>))
      -> commit.A.b.NA
      -> running.A.b.nb
      -> send.A.b.(Msg3, Enc.pk(b).(Sq.<Nonce.nb>))
      -> SKIP

User_B = [] na : NONCE, a : diff(USER,{B}) @
         recv.B.a.(Msg1, Enc.PKB.(Sq.<Nonce.na,User.a>))
      -> running.B.a.na
      -> send.B.a.(Msg2, Enc.pk(a).(Sq.<Nonce.na, Nonce.NB>))
      -> recv.B.a.(Msg3, Enc.PKB.(Sq.<Nonce.NB>))
      -> commit.B.a.NB
      -> SKIP

Network = send?a?b?m -> recv.b.a.m -> Network

Secure_System = (User_A ||| User_B) [| {|send, recv|} |] Network

--------------------------------------
-- 8.5.3 Encoding the intruder in CSPm
--------------------------------------

Fact = Union({
             {|User|},
             {|Nonce|},
             {|Key|},
             { Enc.k.(Sq.<Nonce.n, User.u>) | k<-PKEY, n <- NONCE, u <- USER },
             { Enc.k.(Sq.<Nonce.n, Nonce.n'>) | k<-PKEY, n <- NONCE, n' <- NONCE},
             { Enc.k.(Sq.<Nonce.n>) | k<-PKEY, n <-NONCE }})

Msg1_Encryption_Deduction_Rules =
  { (Enc.k.(Sq.<Nonce.n, User.u>), {Key.k, Nonce.n, User.u}) | k<-PKEY, n <- NONCE, u <- USER }

Msg2_Encryption_Deduction_Rules =
  { (Enc.k.(Sq.<Nonce.n, Nonce.n'>), {Key.k, Nonce.n, Nonce.n'}) | k<-PKEY, n <- NONCE, n' <- NONCE }

Msg3_Encryption_Deduction_Rules =
  { (Enc.k.(Sq.<Nonce.n>), {Key.k, Nonce.n}) | k<-PKEY, n <- NONCE }

Encryption_Deduction_Rules =
  Union({Msg1_Encryption_Deduction_Rules,
         Msg2_Encryption_Deduction_Rules,
         Msg3_Encryption_Deduction_Rules})

Msg1_Decryption_Deduction_Rules =
  { (Nonce.n ,{Enc.k.(Sq.<Nonce.n, User.u>), Key.sk(k)}) | k<-PKEY, n <- NONCE, u <- USER }

Msg2_Decryption_Deduction_Rules =
  { (Nonce.n , {Enc.k.(Sq.<Nonce.n, Nonce.n'>), Key.sk(k)}),
    (Nonce.n', {Enc.k.(Sq.<Nonce.n, Nonce.n'>), Key.sk(k)}) | k<-PKEY, n <- NONCE, n' <- NONCE }

Msg3_Decryption_Deduction_Rules =
  { (Nonce.n, {Enc.k.(Sq.<Nonce.n>), Key.sk(k)}) | k<-PKEY, n <- NONCE }

Decryption_Deduction_Rules =
  Union({Msg1_Decryption_Deduction_Rules,
         Msg2_Decryption_Deduction_Rules,
         Msg3_Decryption_Deduction_Rules})

Deduction_Rules =
  Union({Encryption_Deduction_Rules,
         Decryption_Deduction_Rules})

channel infer : Fact . Deduction_Rules


rule_head((f,_))  = f
rule_body((_,bs)) = bs

rules_match_head(h,Rs) = { r | r <- Rs, rule_head(r) == h }
rules_contain_body(b,Rs) = { r | r <- Rs, member(b, rule_body(r)) }

Unknown(F) =
  (member(F, MSG1_CONT) & [] x : diff(USER, {I}), y : USER @ send.x.y.(Msg1,F) -> Known(F))
  []
  (member(F, MSG2_CONT) & [] x : diff(USER, {I}), y : USER @ send.x.y.(Msg2,F) -> Known(F))
  []
  (member(F, MSG3_CONT) & [] x : diff(USER, {I}), y : USER @ send.x.y.(Msg3,F) -> Known(F))
  []
  ([] r : rules_match_head(F,Deduction_Rules) @ infer.F.r -> Known(F))

Known(F) =
  (
    member(F, MSG1_CONT) & (
                             ( [] x : USER, y : USER @ send.x.y.(Msg1,F) -> Known(F))
                             []
                             ( [] x : USER, y : USER @ recv.x.y.(Msg1,F) -> Known(F))
						   )
  )
  []
  (
    member(F, MSG2_CONT) & (
                             ( [] x : USER, y : USER @ send.x.y.(Msg2,F) -> Known(F))
                             []
                             ( [] x : USER, y : USER @ recv.x.y.(Msg2,F) -> Known(F))
						   )
  )
  []
  (
    member(F, MSG3_CONT) & (
                             ( [] x : USER, y : USER @ send.x.y.(Msg3,F) -> Known(F))
                             []
                             ( [] x : USER, y : USER @ recv.x.y.(Msg3,F) -> Known(F))
						   )
  )
  []
  ([] r : rules_contain_body(F,Deduction_Rules) @ infer.rule_head(r).r -> Known(F))

KnownAlpha(F) =
  Union({
    { send.x.y.(Msg1,F) | x <- USER, y <- USER, member(F, MSG1_CONT)},
    { send.x.y.(Msg2,F) | x <- USER, y <- USER, member(F, MSG2_CONT)},
    { send.x.y.(Msg3,F) | x <- USER, y <- USER, member(F, MSG3_CONT)},
    { recv.x.y.(Msg1,F) | x <- USER, y <- USER, member(F, MSG1_CONT)},
    { recv.x.y.(Msg2,F) | x <- USER, y <- USER, member(F, MSG2_CONT)},
    { recv.x.y.(Msg3,F) | x <- USER, y <- USER, member(F, MSG3_CONT)},
    { infer.F.r | r <- rules_match_head(F,Deduction_Rules) },
    { infer.rule_head(r).r | r <- rules_contain_body(F,Deduction_Rules) }
  })


IK = {Key.PKA, Key.PKB, Key.PKI, Key.SKI, Nonce.NI, User.A, User.B, User.I}

Intruder(K) =
  || F : Fact @ [KnownAlpha(F)]
  if member(F,K) then
     Known(F)
  else
     Unknown(F)

external chase

IntruderHideInfer = chase(Intruder(IK) \ {| infer |})

Unsecure_System = (User_A ||| User_B) [| {|send, recv|} |] IntruderHideInfer

-------------------------------------------------------
-- 8.5.4 Encoding and verifying the security properties
-------------------------------------------------------

Precedes(e,d) = e -> RUN({e,d})

Aliveness(a,b) = [] x : USER, n : NONCE, m : NONCE @ Precedes(running.b.x.n, commit.a.b.m)
AlphaAliveness(a,b) = { running.b.x.n, commit.a.b.m | x <- USER, n <- NONCE, m <- NONCE }

InjectiveAgreement(a,b,na) = Precedes(running.b.a.na, commit.a.b.na)
AlphaInjectiveAgreement(a,b,na) = { running.b.a.na, commit.a.b.na }

assert Aliveness(A,B) |||
RUN(diff(Events,AlphaAliveness(A,B))) [T= Secure_System
assert Aliveness(B,A) |||
RUN(diff(Events,AlphaAliveness(B,A))) [T= Secure_System

assert Aliveness(A,B) |||
RUN(diff(Events,AlphaAliveness(A,B))) [T= Unsecure_System
assert Aliveness(B,A) |||
RUN(diff(Events,AlphaAliveness(B,A))) [T= Unsecure_System

assert InjectiveAgreement(A,B,NA) |||
RUN(diff(Events,AlphaInjectiveAgreement(A,B,NA))) [T= Secure_System
assert InjectiveAgreement(B,A,NB) |||
RUN(diff(Events,AlphaInjectiveAgreement(B,A,NB))) [T= Secure_System

assert InjectiveAgreement(A,B,NA) |||
RUN(diff(Events,AlphaInjectiveAgreement(A,B,NA))) [T= Unsecure_System
assert InjectiveAgreement(B,A,NB) |||
RUN(diff(Events,AlphaInjectiveAgreement(B,A,NB))) [T= Unsecure_System
```