# ATM2.csp
```
-- ATM2

datatype DisplayActions = ready 
channel Display : DisplayActions

datatype CardSlotActions = cardI | cardO
channel CardSlot : CardSlotActions

datatype KeyPadActions = pinE 
channel KeyPad: KeyPadActions

datatype CashSlotActions = cashO
channel CashSlot: CashSlotActions

ATM2 = Display.ready -> CardSlot.cardI 
    -> KeyPad.pinE -> CardSlot.cardO 
    -> CashSlot.cashO -> ATM2
```