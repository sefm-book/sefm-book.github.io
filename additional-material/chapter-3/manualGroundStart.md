# commSystem.csp
```
-- ManualGroundStart

-- *******  BUTTONS ***********
channel press, release

-- ButtonOFF and ButtonON  - this are the general process for the needed buttons

ButtonOFF = press -> ButtonON 
ButtonON = release -> ButtonOFF 

-- Instantiate the general ButtonON ButtonOFF for the individual buttons:

channel mc_press, mc_release
MasterCrank = ButtonOFF [[press <- mc_press, release <- mc_release]]

channel ms_press, ms_release
MasterStart = ButtonOFF [[press <- ms_press, release <- ms_release]]

channel engineStartON
EngineStart = engineStartON -> EngineStart

channel fc_press, fc_release
FuelControl = ButtonOFF [[press <- fc_press, release <- fc_release]]

channel ci_press, ci_release
ContIgnition = ButtonOFF [[press <- ci_press, release <- ci_release]]

-- All Buttons

Buttons = MasterCrank ||| MasterStart ||| EngineStart ||| FuelControl ||| ContIgnition

-- ********* Checking for the aircraft and engine condition ************************

channel aircraftCondition:Bool
channel engineCondition:Bool
channel inhibitStart, startOK

CheckConditions =   aircraftCondition ? ac -> engineCondition ? ec -> Checking(ac,ec)
                 [] engineCondition ? ec -> aircraftCondition ? ac -> Checking(ac,ec)

Checking(ac,ec) = if (ac and ec) then startOK -> SKIP else InhibitStart

InhibitStart = inhibitStart -> SKIP

-- ****** Initiating Interaction with the EEC ***********

-- engineStartOn has effect only after both
--    MasterCrank 
--    ContIgnition
-- are ON
 
StartInteractionEEC =   mc_press -> NowCIpress
                     [] ci_press -> NowMCpress
                     [] engineStartON -> StartInteractionEEC

-- InitStartOK is the state where
-- both MasterCrank and ContIgnition are ON

NowCIpress =    ci_press -> InitStartOK
             [] engineStartON -> NowCIpress

NowMCpress =    mc_press -> InitStartOK
             [] engineStartON -> NowMCpress

-- now engineStartON has an effect

InitStartOK = engineStartON -> AtLeastOneEngineStartOn

-- the engineStartOn Button can be pressed any time
-- though it does not have any further effect
-- the state "Start initiated" has been reached

AtLeastOneEngineStartOn =    startOK -> SKIP 
                          [] engineStartON -> AtLeastOneEngineStartOn

--*****************************************
--  Main Process of the Manual Ground Start
--*****************************************

channel abortStart
channel commandIGNoff

-- Note: the effect of mc_release wrongly leads to abort
-- even ***after*** Starter Disengagement Speed has been reached


-- mc_release -> abortStart -> SKIP
             
Interrupts =     fc_release -> abortStart -> STOP
             []  ci_release -> commandIGNoff -> STOP

ManualGroundStart =
  
    (CheckConditions [| {|startOK|} |] StartInteractionEEC) \ { startOK }; 
    ((Region ||| EngineStart)  /\ Interrupts)
  
    [| { mc_press, mc_release,
        ms_press, ms_release,
        engineStartON,
        fc_press, fc_release,
        ci_press, ci_release}
    |] 
    Buttons

--*********** Starting the internal procedure of the MGS ****************

datatype SAVMode = open | close
channel sav:SAVMode

StartInit =  sav.open -> fc_press -> Fuel
          [] fc_press -> sav.open -> Fuel

channel commandFuelON, commandIgnON

-- commandFuelON and commandIgnON interleave:

Fuel =  commandFuelON -> commandIgnON  -> SKIP
    []  commandIgnON  -> commandFuelON -> SKIP

Region = (StartInit /\  (mc_release -> abortStart -> STOP)) ; 
         (MasterSpeed ||| (ButtonON  [[press <- mc_press, release <- mc_release]] )) 

-- ********  Checking for the speed and the idle *****************

SPEED1 = 15 -- this is the % of the max speed
SPEED2 = 65 -- this is the % of the max speed

channel readNH:{0..100}
channel startComplete  

MasterSpeed = readNH ? x -> if (x>SPEED1) then SpeedReached else MasterSpeed

SpeedReached = sav.close -> MasterIdle

MasterIdle = readNH ? x -> if (x>SPEED2) then StartCompleted else MasterIdle

StartCompleted = startComplete -> SKIP
```