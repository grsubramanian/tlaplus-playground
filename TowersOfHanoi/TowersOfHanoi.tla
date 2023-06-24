--------------------------- MODULE TowersOfHanoi ---------------------------
EXTENDS Integers, Sequences

CONSTANT N

VARIABLE x1, x2, x3

Discs == 1..N

Range(f) == {f[x] : x \in DOMAIN f}
Empty(s) == Len(s) = 0
NotEmpty(s) == \neg Empty(s)

TypeOK ==
    /\ Range(x1) \subseteq Discs
    /\ Range(x2) \subseteq Discs
    /\ Range(x3) \subseteq Discs

NoDuplicates ==
    /\ \neg (\E d1 \in Range(x1) : \E d2 \in Range(x2) : d1 = d2)
    /\ \neg (\E d2 \in Range(x2) : \E d3 \in Range(x3) : d2 = d3)
    /\ \neg (\E d3 \in Range(x3) : \E d1 \in Range(x1) : d3 = d1)

NoLosingDiscs ==
    \A d \in Discs : (d \in Range(x1)) \/ (d \in Range(x2)) \/ (d \in Range(x3))

Init ==
    /\ x1 = [ d \in Discs |-> d ]
    /\ x2 = <<>>
    /\ x3 = <<>>

DesiredSolution ==
    /\ x1 = <<>>
    /\ x2 = <<>>
    /\ x3 = [ d \in Discs |-> d ]

DesiredSolutionNotPossible == \neg DesiredSolution

CanMove(a, b) ==
    /\ NotEmpty(a)
    /\ IF Empty(b) THEN TRUE ELSE Head(a) < Head(b)

Move(a, b) ==
    /\ CanMove(a, b)
    /\ a' = Tail(a)
    /\ b' = <<Head(a)>> \o IF NotEmpty(b) THEN b ELSE <<>>

Next ==
    \/ (Move(x1, x2) /\ UNCHANGED x3)
    \/ (Move(x1, x3) /\ UNCHANGED x2)
    \/ (Move(x2, x1) /\ UNCHANGED x3)
    \/ (Move(x2, x3) /\ UNCHANGED x1)
    \/ (Move(x3, x1) /\ UNCHANGED x2)
    \/ (Move(x3, x2) /\ UNCHANGED x1)

=============================================================================

