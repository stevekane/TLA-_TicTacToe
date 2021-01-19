----------------------------- MODULE TicTacToe -----------------------------
EXTENDS Integers, Sequences
VARIABLES turnState, board
CONSTANTS TotalDimensions, BoardSize, PlayerCount

Index       == 0..(BoardSize - 1)
TurnState   == 0..(PlayerCount - 1)
Dimension   == 0..(TotalDimensions - 1)
First       == 0
Empty       == -1
CellState   == TurnState \union {Empty}
\* CellIndex   == [x : Index, y : Index]
CellIndex   == [Dimension -> Index]
Board       == [CellIndex -> CellState]
EmptyBoard  == [c \in CellIndex |-> Empty]
NonZeroNat  == Nat \ {0}

TypeOK ==
    /\ PlayerCount \in NonZeroNat
    /\ BoardSize \in NonZeroNat
    /\ turnState \in TurnState
    /\ board \in Board

BeginNewGame ==
    /\ turnState' = First
    /\ board' = EmptyBoard

TakeTurn ==
    /\ turnState' = (turnState + 1) % PlayerCount
    /\ \E c \in CellIndex :
        /\ board[c] = Empty
        /\ board' = [board EXCEPT ![c] = turnState]

GameOver == 
    \/ \A c \in CellIndex : board[c] # Empty
    \/ \E t \in TurnState : 
        \/ \E x \in Index : \A y \in Index : board[[x |-> x, y |-> y]] = t
        \/ \E y \in Index : \A x \in Index : board[[x |-> x, y |-> y]] = t
        \/ \A i \in Index : board[[x |-> i, y |-> BoardSize - 1 - i]] = t
        \/ \A i \in Index : board[[x |-> i, y |-> i]] = t

Init == turnState = First /\ board = EmptyBoard 

Next == IF GameOver THEN BeginNewGame ELSE TakeTurn
=============================================================================