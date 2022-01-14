# telephoneDatabase.casl
```
library telephoneDatabase

%%%%%%%%%%%%%%%%%
%% 4.2.1 Modelling
%%%%%%%%%%%%%%%%%

spec DatabaseSignature =
 sort Database, Name, Number
 ops initial: Database;
     lookUp: Database * Name ->? Number;
     update: Database * Name * Number -> Database;
     delete: Database * Name -> Database;
 pred isEmpty: Database
end

spec Database =
 sort Database, Name, Number
 ops initial: Database;
     lookUp: Database * Name ->? Number;
     update: Database * Name * Number -> Database;
     delete: Database * Name -> Database;
 pred isEmpty: Database
 forall db:Database; name,name1,name2:Name; number: Number 
  . not def lookUp(initial, name)
    %(non def initial)%
  . name1 = name2 =>
      lookUp(update(db,name1,number), name2) = number
    %(name found)%
  . not (name1 = name2) =>
    lookUp(update(db,name1,number), name2) = 
      lookUp(db, name2) 
    %(name not found)%
  . delete(initial, name) = initial 
    %(delete initial)%
  . name1 = name2 =>
      delete(update(db,name1,number), name2) = 
      delete(db, name2) 
    %(delete found)%
  . not (name1 = name2) =>
      delete(update(db,name1,number), name2) = 
      update(delete(db, name2), name1,number)
    %(name not found)%
   . isEmpty(db) <=> db=initial
    %(def isEmpty)%
end

spec OneSort =
  sort s
end

%%%%%%%%%%%%%%%%%%
%% 4.2.2 Validating
%%%%%%%%%%%%%%%%%%

spec UseCaseSetUp =
  Database
then
  ops Hugo, Erna: Name;
      N4711, N17: Number
   .  not Hugo=Erna
     %(Hugo different from Erna)%
end

spec UseCase =
  UseCaseSetUp
then %implies
   .  not lookUp(initial,Hugo) = N17
          %(lookup on initial not equal to 17)% 
   .  not def lookUp(initial,Hugo)
          %(lookup on initial defined)%  
   .  lookUp(update(initial,Hugo,N4711),Hugo) = N4711
          %(lookup stores values)%  
   .  lookUp(
          update(update(initial,Hugo,N4711), Erna,N17),
          Hugo) = N4711
          %(update does not overwrite)%
   .  not def(lookUp(update(initial,Erna,N17),Hugo))
          %(lookup is not defined without update)%
   .  not isEmpty (update(update(initial,Hugo,N4711), Erna,N17))
          %(updating leads to a non empty database)%
   .  isEmpty(initial)
          %(the initial database is empty)%  
   .  isEmpty (delete(update(initial,Hugo,N4711), Hugo))
          %(deleting all entries leads to an empty database)%
end

spec AbstractProperty =
  Database
then %implies
  forall db: Database, name1, name2, name3: Name, number1, number2: Number
  .     lookUp(update(update(db, name1, number1), name2, number2), name3) 
     =  lookUp(update(update(db, name2, number2), name1, number1), name3)
     if not (name1 = name2)
       %(specialised update commutativity)%

end


spec UndeterminedProperty =
  Database
then %implies
  forall db: Database, name1, name2: Name, number1, number2: Number

  .     update(update(db, name1, number1), name2, number2)
     =  update(update(db, name2, number2), name1, number1)
     if not (name1 = name2)
       %(general update commutativity)%

  .  not (  update(update(db, name1, number1), name2, number2)
     =  update(update(db, name2, number2), name1, number1)
     if not (name1 = name2) )
       %(negation of general update commutativity)%

%%%%%%%%%%%%%%%%%%%
%% 4.2.3 Consistency
%%%%%%%%%%%%%%%%%%%

spec MyModel =   
  %% encoding the carrier sets using "free types":
  free type Database ::= empty | h_stored | e_stored | e_and_h_stored
  free type Name ::=  h | e
  free type Number ::= *

  %% adding generatedness manually 
  %% currently not supported in the Hets translation to Spass:
  %% cf. error message
  %% SuleCFOL2TPTP sort generation axioms are not yet supported
  forall d: Database . d = empty \/ d = h_stored \/ d = e_stored \/ d = e_and_h_stored
  forall n: Name . n = h \/ n = e
  forall n: Number . n = *

  %% declaring "initial" and its interpretation:
  ops initial: Database
  . initial = empty

  %% declaring "Hugo" and "Erna" and their interpretation:
  ops Hugo, Erna: Name
  . Hugo = h
  . Erna = e

  ops N4711, N17: Number
  . N4711 = *
  . N17 = *

  %% declaring "lookUp" and encoding its value table:
  op lookUp: Database * Name ->? Number

  %% first row:
  . not def lookUp (empty,         h)
  .         lookUp (h_stored,      h) = *
  . not def lookUp (e_stored,      h) 
  .         lookUp(e_and_h_stored, h) = *

  %% second row:
  . not def lookUp(empty,          e) 
  . not def lookUp(h_stored,       e) 
  .         lookUp(e_stored,       e) = *
  .         lookUp(e_and_h_stored, e) = *

  %% declaring "update" and encoding its value table:
  op update: Database * Name * Number -> Database;

  %% first row:
  . update (empty,          h, *) = h_stored
  . update (h_stored,       h, *) = h_stored
  . update (e_stored,       h, *) = e_and_h_stored
  . update (e_and_h_stored, h, *) = e_and_h_stored

  %% second row:
  . update (empty,          e, *) = e_stored
  . update (h_stored,       e, *) = e_and_h_stored
  . update (e_stored,       e, *) = e_stored
  . update (e_and_h_stored, e, *) = e_and_h_stored

  %% declaring "delete" and encoding its value table:
  op  delete: Database * Name -> Database;

  %% first row:
  . delete (empty,          h) = empty
  . delete (h_stored,       h) = empty
  . delete (e_stored,       h) = e_stored
  . delete (e_and_h_stored, h) = e_stored

  %% second row:
  . delete (empty,          e) = empty
  . delete (h_stored,       e) = h_stored
  . delete (e_stored,       e) = empty
  . delete (e_and_h_stored, e) = h_stored

  %% declaring "isEmpty" and its extent:
  pred isEmpty : Database
  . forall d: Database . isEmpty(d) <=> d = empty
end

view consistency : UseCaseSetUp to MyModel

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 4.2.4 Testing Java implementations against algebraic specifications
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

spec DatabaseForCongu =
  Database
then %def 
  pred 
    contains: Database * Name;
  axioms
    forall db: Database; name: Name 
    . contains(db, name) <=> def lookUp(db, name) 
then %implies
  forall db:Database; name,name1,name2:Name; number: Number 
    . not(contains(initial, name))
        %(contains never holds for initial)%

    . contains(update(db, name1, number), name2)
 	  if name1 = name2 \/ contains(db, name2)
        %(contains behaves like lookUp)%
end
```