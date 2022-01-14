# ATM4.csp
```
-- ATM4

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

ATM4 = Display.ready -> CardSlot.cardI 
     -> KeyPad.pinE -> Display.menu 
     ->  ( (Buttons.checkBalance -> Display.accountBalance 
            -> CardSlot.cardO -> ATM4)
         []       
            (Buttons.withdrawCash -> CardSlot.cardO 
             -> CashSlot.cashO -> ATM4)
         )
```