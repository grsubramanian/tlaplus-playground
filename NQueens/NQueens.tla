------------------------------- MODULE NQueens -------------------------------
EXTENDS Integers, Sequences

CONSTANT N
ASSUME N \in Nat \ {0}

VARIABLE QueenCells

Init ==
    QueenCells = [
        row \in 1..N |->
            <<row, 1>>
    ]

ValidCells == (1..N) \X (1..N)
IsValidCell(c) == c \in ValidCells

ShiftQueen(q, c) ==
    QueenCells' = [ QueenCells EXCEPT ![q] = << QueenCells[q][1], c >> ]

Next ==
    \E q \in 1..N :
        \E c \in (1 .. QueenCells[q][2] - 1) \union (QueenCells[q][2] + 1 .. N):
            ShiftQueen(q, c)

IsSameCol(c1, c2)   == c1[2] = c2[2]
IsSameDiag1(c1, c2) == c1[1] - c2[1] = c1[2] - c2[2]
IsSameDiag2(c1, c2) == c1[1] - c2[1] = c2[2] - c1[2]

SomeQueenAttackingAnother ==
    \E q1, q2 \in 1..N :
        /\ q1 # q2
        /\ \/ IsSameCol(QueenCells[q1], QueenCells[q2])
           \/ IsSameDiag1(QueenCells[q1], QueenCells[q2])
           \/ IsSameDiag2(QueenCells[q1], QueenCells[q2])

==============================================================================
