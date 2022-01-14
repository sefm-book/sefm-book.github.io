# candy.csp
```
-- Children and StableAfter

fill(n) = if (n%2==0) then n else n+1

channel c: {0..2}.{0..2}

-- The child processes: 
--       p - position, 
--       i - number of candies

Child(p,i) = 
   (   c.(p+1)%3 ! (i/2) 
    -> c.p       ? x     -> Child(p, fill(i/2+x)))
[] (   c.p       ? x    
    -> c.(p+1)%3 ! (i/2) -> Child(p, fill(i/2+x)))

-- 3 Children, holding 2*p candies each:

Children = || p:{0..2} @ 
             [ {| c.p, c.(p+1)%3 |} ] Child(p,2*p)

-- Stability

StableAfter (n) = if n>0 then  c.0 ? x -> StableAfter (n-1)
                            [] c.1 ? x -> StableAfter (n-1)  
                            [] c.2 ? x -> StableAfter (n-1)
                  else Stable

Stable = c.0!2->Stable [] c.1!2->Stable [] c.2!2->Stable


assert Children :[deadlock free]
assert StableAfter(3)  [T= Children
assert StableAfter(6)  [T= Children
assert StableAfter(9)  [T= Children
assert StableAfter(12)  [T= Children
```