# ATM5.csp
```
-- ATM5

datatype DisplayActions = ready | menu | accountBalance
channel Display : DisplayActions

datatype CardSlotActions = cardI | cardO
channel CardSlot : CardSlotActions

datatype KeyPadActions = pinE 
channel KeyPad: KeyPadActions

datatype CashSlotActions = cashO
channel CashSlot: CashSlotActions

datatype ButtonActions = checkBalance | withdrawCash
channel Buttons: ButtonActions

ATM5 = Display!ready -> CardSlot.cardI 
     -> KeyPad.pinE -> Display!menu 
     -> Buttons?x -> if x==checkBalance then Balance
                                        else Withdrawal
Balance = Display!accountBalance 
          -> CardSlot!cardO -> ATM5

Withdrawal = CardSlot!cardO 
             -> CashSlot!cashO -> ATM5
```