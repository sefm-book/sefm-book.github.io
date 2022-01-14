# structuredSpecs.casl
```
library ExamplesForStructuringOperations
%display __<=__ %LATEX __\leq__

%%%%%%%%%%%%%%%%%%%%
%% 4.4.1 Extensions
%%%%%%%%%%%%%%%%%%%%

spec PartialOrder =
  sort Elem
  pred __ <= __ : Elem * Elem
  forall x,y,z: Elem
  .   x <= x
  .   x <= y /\ y <=z => x <= z
  op inf, sup :  Elem * Elem -> ? Elem
  forall x,y,z: Elem
  . inf (x,y) = z 
    <=>
    z <= x  /\ z <= y /\
    (forall t:Elem .  t <= x  /\ t <= y =>  t <= z)
  . sup (x,y) = z 
    <=>
    x <= z  /\ y <= z /\
    (forall t:Elem .  x <= t  /\ y <= t =>  z <= t)
end

spec TotalOrder =
  PartialOrder
then
  forall x,y : Elem
  . x <= y \/ y <= x
  ops min, max :  Elem * Elem -> Elem
  forall x,y: Elem
  . min (x,y) = x when x <= y else y
  . max (x,y) = x when y <= x else y
then %implies
  forall x,y: Elem 
  . min(x,y) = inf(x,y) %(min=inf)%
  . max(x,y) = sup(x,y) %(max=sup)%
end

%%%%%%%%%%%%%%%
%% 4.2.2 Union
%%%%%%%%%%%%%%%

spec Relation =
  sort Elem
  pred __~__: Elem * Elem
end

spec IrreflexiveRelation = Relation
then
  forall x: Elem
  . not x ~ x
end

spec TransitiveRelation = Relation
then
  forall x,y,z: Elem
  . x ~ y /\ y ~ z => x ~ z
end

spec AsymmetricRelation = Relation
then
  forall x, y: Elem
  . not x ~ y if y ~ x
end

spec StrictOrder =
  IrreflexiveRelation and  TransitiveRelation
then %implies
  AsymmetricRelation
end

%%%%%%%%%%%%%%%%%
%% 4.4.3 Renaming
%%%%%%%%%%%%%%%%%


spec Monoid =
  sort S
  ops  1: S;
       __*__: S * S -> S;
  . forall x: S . 1 * x = x                          %(monoid left unit)%
  . forall x: S . x * 1 = x                          %(monoid right unit)%
  . forall x,y,z: S . x * ( y * z ) = (x * y) * z    %(monoid associativity)%
end

spec List = 
  sort Elem
  free type List ::= [] | __::__ (Elem; List) 
then %def
  op __++__    :List * List -> List 
  forall L,M :List;e :Elem
  . [] ++ L = L                                 %(++ empty list)%     
  . (e::L)++M =e::(L++M)                        %(++ non-empty list)%    
end 

spec MyMonoid =
  Monoid with S |-> List, 1 |-> [], __*__ |-> __++__
end


spec ListsAreMonoids = 
  List
then %implies
   Monoid with S |-> List, 1 |-> [], __*__ |-> __++__
end

%% creating a copy of Monoid called Monoid2
%% creating a copy of List called List2
%% in order to start a fresh development

spec Monoid2 =
  sort S
  ops  1: S;
       __*__: S * S -> S;
  . forall x: S . 1 * x = x                          %(monoid left unit)%
  . forall x: S . x * 1 = x                          %(monoid right unit)%
  . forall x,y,z: S . x * ( y * z ) = (x * y) * z    %(monoid associativity)%
end

spec List2 = 
  sort Elem
  free type List ::= [] | __::__ (Elem; List) 
then %def
  op __++__    :List * List -> List 
  forall L,M :List;e :Elem
  . [] ++ L = L                                 %(++ empty list)%     
  . (e::L)++M =e::(L++M)                        %(++ non-empty list)%    
end 

spec List2WithInductionPrinciples =
  List2
then 
 . (      [] ++ [] = [] 
    /\
        (forall M: List; e: Elem .
                      M ++ [] =   M 
            =>   (e::M) ++ [] =  (e::M)
        )
   )
   => forall M: List. M ++ [] = M               %(induction axiom for r-Unit)%
  
then %implies
  forall L,M, N :List; e:Elem 

  . [] ++ (M ++ N) = ([] ++ M) ++ N            %(induction base for assoc)%
  .    (forall K: List, e: Elem .
          ( forall M, N: List .       
                    K  ++ (M ++ N) = (    K  ++ M) ++ N
            =>  (e::K) ++ (M ++ N) = ((e::K) ++ M) ++ N
          )   
       ) %(induction step)%
then
 . (  forall M, N :List. [] ++ (M ++ N) = ([] ++ M) ++ N ) 
   /\
     (forall K: List, e: Elem .
          ( forall M, N: List .       
                    K  ++ (M ++ N) = (    K  ++ M) ++ N  
            =>  (e::K) ++ (M ++ N) = ((e::K) ++ M) ++ N
          )   
       )
   => forall L,M,N: List. L ++ (M ++ N) = (L ++ M) ++ N %(induction axiom for assoc)%

then %implies
  Monoid2 with S |-> List, 1 |-> [], __*__ |-> __++__
end

%%%%%%%%%%%%%%%%%
%% 4.4.4 Libraries
%%%%%%%%%%%%%%%%%

from Basic/Numbers get Nat

spec ListWithLength = 
  List
then
  Nat
then
  op length : List -> Nat
  forall L :List;e :Elem
  . length ([]) = 0                 %(length empty list)%
  . length (e::L) = length(L) + 1   %(length non-empty lists)%
end

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 4.4.5 Parametrization and Instantiation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

spec SortedList [TotalOrder] =
  List
then %def
     pred  sorted : List
     forall e, f : Elem; l : List
     . sorted([])
     . sorted(e :: [])
     . sorted(e :: (f :: l)) <=> (e <= f /\  sorted(f :: l))
end

spec SortedNatList =
  SortedList [Nat fit sort Elem |-> Nat, ops inf |-> min, sup |-> max]
end

spec SortedListWithLengthNoNat [TotalOrder] = 
  ListWithLength and SortedList[TotalOrder]
end

spec SortedListWithLength [TotalOrder] given Nat = 
  ListWithLength and SortedList[TotalOrder]
end

spec SortedNatListWithLength =
  SortedListWithLength [Nat fit sort Elem |-> Nat, 
                                ops inf |-> min, sup |-> max]
end

%%%%%%%%%%%%%%%
%% 4.4.6 Hiding
%%%%%%%%%%%%%%%

spec Hugo =
  sorts s,t
  op  o: s -> t
end

spec Erna =
  Hugo hide t
end

spec NewNat =
  free type Nat ::= 0 | suc(Nat)
  op 1: Nat = suc(0);
  op __+__, __*__: Nat * Nat -> Nat;
  op square: Nat -> Nat;
  forall n,m: Nat 
  .  0 + n = n
  .  suc(m) + n = suc(m+n)
  .  0 * n = 0
  .  suc(m) * n = n + (m * n)
  .  square(n) = n * n
end

spec MyDataType =
  NewNat hide __+__, __*__
end
```