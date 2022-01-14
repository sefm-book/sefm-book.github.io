# ATM3.csp
```
-- ATM3

datatype DText = ready
channel Display : DText

datatype CardSlotActions = cardI | cardO
channel CardSlot : CardSlotActions

datatype KeyPadActions = pinE | cancel
channel KeyPad: KeyPadActions

datatype CashSlotActions = cashO
channel CashSlot: CashSlotActions

ATM3 = Display.ready -> CardSlot.cardI -> Session; SessionEnd

Session = (KeyPad.pinE -> SKIP) /\ SessionCancel 

SessionCancel = KeyPad.cancel -> CardSlot.cardO -> ATM3

SessionEnd = CardSlot.cardO -> CashSlot.cashO -> ATM3
```