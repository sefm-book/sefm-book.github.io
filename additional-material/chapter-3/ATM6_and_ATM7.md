# ATM6_and_ATM7.csp
```
-- ATM6 and ATM7

datatype DisplayActions = ready | menu | accountBalance | messagePinWrong
channel Display : DisplayActions

datatype CardSlotActions = cardI | cardO
channel CardSlot : CardSlotActions

datatype KeyPadActions = pinE 
channel KeyPad: KeyPadActions

datatype CashSlotActions = cashO
channel CashSlot: CashSlotActions

datatype ButtonActions = checkBalance | withdrawCash
channel Buttons: ButtonActions

datatype CheckActions = pinOK | pinWrong
channel Check: CheckActions

channel requestPCheck, comparePinWithCard

PinVerification = 
     requestPCheck -> comparePinWithCard
  ->((Check.pinOK -> PinVerification) 
     |~| 
     (Check.pinWrong -> PinVerification))

UserDialog = 
    Display.ready -> CardSlot.cardI 
 -> KeyPad.pinE -> requestPCheck 
 -> ((Check.pinOK -> Services) 
     [] 
     (Check.pinWrong -> Display.messagePinWrong -> UserDialog))

Services = Display.menu -> (CashWithdrawal [] BalanceCheck)

BalanceCheck = 
  Buttons.checkBalance -> Display.accountBalance 
  -> CardSlot.cardO -> UserDialog

CashWithdrawal = 
     Buttons.withdrawCash -> CardSlot.cardO 
  -> CashSlot.cashO -> UserDialog

ATM6 = UserDialog 
       [| {| requestPCheck, Check |} |] 
       PinVerification

ATM7 = ATM6 \ {| requestPCheck, Check, comparePinWithCard |}
```