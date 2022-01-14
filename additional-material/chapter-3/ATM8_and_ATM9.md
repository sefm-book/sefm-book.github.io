# ATM8_and_ATM9.csp
```
-- ATM 8 and ATM 9

datatype DisplayActions = ready | menu | accountBalance | messagePinWrong | cardSwallowed
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

UserDialog = Display.ready -> CardSlot.cardI
          -> PinCheck(3) 

PinCheck(n) = KeyPad.pinE -> requestPCheck 
          -> ((Check.pinOK -> Services) 
              [] 
              (Check.pinWrong 
               -> if (n==1) 
                  then Display.messagePinWrong
                       -> Display.cardSwallowed 
                       -> UserDialog 
                  else Display.messagePinWrong
                       -> PinCheck(n-1)
              )
             )    

Services = Display.menu -> (CashWithdrawal [] BalanceCheck)

BalanceCheck = 
  Buttons.checkBalance -> Display.accountBalance 
  -> CardSlot.cardO -> UserDialog

CashWithdrawal = 
     Buttons.withdrawCash -> CardSlot.cardO 
  -> CashSlot.cashO -> UserDialog

ATM8 = UserDialog 
       [| {| requestPCheck, Check  |} |] 
       PinVerification

ATM9 = ATM8 \ {| requestPCheck, Check, comparePinWithCard |}
```