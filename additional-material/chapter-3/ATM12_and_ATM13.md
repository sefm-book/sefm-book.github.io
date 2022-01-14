# ATM12_and_ATM13.csp
```
-- ATM12 and ATM13

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

datatype Denominations = five | ten | twenty | fifty

setofDenominations = {five,ten,twenty,fifty}

channel Quantity: Denominations

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

CartridgeCounter(d) = Quantity.d -> CartridgeCounter(d)

CartridgeCounterS = |||x:setofDenominations@CartridgeCounter(x)

Init(X) = ([]x:X@Quantity.x -> Init(diff(X,{x}))) [] (X == {}) & ATM7

ATM12 = CartridgeCounterS [| {|Quantity|} |] Init(setofDenominations)

ATM13 = ATM12\  {|Quantity|}
```