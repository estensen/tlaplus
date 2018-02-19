------------------------------ MODULE DieHard ------------------------------
EXTENDS Integers

VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big   \in 0..5

Init == /\ small = 0
        /\ big   = 0

FillSmall == /\ small' = 3
             /\ big'   = big

FillBig == /\ big'   = 5
           /\ small' = small

EmptySmall == /\ small' = 0
              /\ big'   = big

EmptyBig == /\ big'   = 0
            /\ small' = small

SmallToBig == IF big + small =< 5
               THEN /\ small' = 0 
                    /\ big'   = small + big
               ELSE /\ small' = small - (5 - big)
                    /\ big'   = 5

BigToSmall == IF big + small =< 3
               THEN /\ small' = small + big
                    /\ big'   = 0
               ELSE /\ small' = 3
                    /\ big'   = small - (3 - big)

Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall

=============================================================================