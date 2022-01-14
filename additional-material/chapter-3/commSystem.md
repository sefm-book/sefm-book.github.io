# commSystem.csp
```
-- COMM_SYSTEM and MCOMM_SYSTEM

channel read, write: {0,1}

-- A two place buffer:

B           = read?x -> B_One (x)
B_One(x)    = read?y -> B_Two(x,y)
              []
              write!x ->B
B_Two(x,y) = write!x -> B_One(y)

-- The faulty communication system:

channel toMedium, fromMedium : {0,1}

SNDR = read?x -> toMedium!x -> SNDR
RCVR = fromMedium?x -> write!x -> RCVR

MEDIUM_Zero = toMedium?m -> 
             (fromMedium!m -> MEDIUM_Zero 
              |~| 
              fromMedium!(1-m) -> MEDIUM_Two)
MEDIUM_One = toMedium?m -> fromMedium!m -> MEDIUM_Zero
MEDIUM_Two = toMedium?m -> fromMedium!m -> MEDIUM_One

MEDIUM = MEDIUM_Zero

COMM_SYSTEM = (SNDR [| {|toMedium |} |] MEDIUM) [| {|fromMedium |} |] RCVR

-- This assertion does not hold:
assert B [T= COMM_SYSTEM \ {|toMedium, fromMedium|}

-- The corrected communication system:

MSNDR = read?x -> toMedium!x ->toMedium!x ->toMedium!x -> MSNDR

MRCVR = fromMedium?x -> fromMedium?y -> fromMedium?z-> 
           if x==y 
           then write!x -> MRCVR
           else write!z -> MRCVR

MCOMM_SYSTEM = (MSNDR[| {|toMedium |} |] MEDIUM) [| {|fromMedium |} |] MRCVR

-- Both these assertions are true:
assert B [F= MCOMM_SYSTEM \ {|toMedium, fromMedium|}
assert MCOMM_SYSTEM \ {|toMedium, fromMedium|} [F= B
```