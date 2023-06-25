--------------------------- MODULE TowersOfHanoiGeneral ---------------------------
EXTENDS Integers, Sequences

CONSTANTS N, T

VARIABLE X

Discs == 1..N
Towers == 1..T

Range(f) == {f[x] : x \in DOMAIN f}
Empty(s) == Len(s) = 0
NotEmpty(s) == \neg Empty(s)

TypeOKTower(t) == Range(X[t]) \subseteq Discs
TypeOK == \A t \in Towers : TypeOKTower(t)

NoDuplicatesBetweenTowers(t1, t2) ==
    \/ t1 = t2 
    \/ \neg (
            \E d1 \in Range(X[t1]) :
                \E d2 \in Range(X[t2]) :
                    d1 = d2
       )
NoDuplicates ==
    \A t1, t2 \in Towers :
        NoDuplicatesBetweenTowers(t1, t2)

NoLosingDiscs ==
    \A d \in Discs :
        \E t \in Towers:
            d \in Range(X[t])

AllDiscsOnTower(t) ==
    X = [
            a \in Towers |->
                IF a = t
                    THEN [ d \in Discs |-> d ]
                    ELSE <<>>
        ]
Init == AllDiscsOnTower(1)

CanMove(t1, t2) ==
    /\ NotEmpty(X[t1])
    /\ IF Empty(X[t2])
           THEN TRUE
           ELSE Head(X[t1]) < Head(X[t2])

Next ==
    \E t1, t2 \in Towers :
        /\ CanMove(t1, t2)
        /\ X' = [X EXCEPT ![t1] = Tail(@),
                          ![t2] = <<Head(X[t1])>> \o IF NotEmpty(@) THEN @ ELSE <<>>]

DesiredSolutionNotPossible == \neg AllDiscsOnTower(T)

=============================================================================

