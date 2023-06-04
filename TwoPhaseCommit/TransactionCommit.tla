--------------------------- MODULE TransactionCommit ---------------------------
CONSTANT ResourceManagers
VARIABLE resourceManagerState

TransactionCommitTypeOKInvariant ==
    resourceManagerState \in [ResourceManagers -> {"working", "prepared", "committed", "aborted"}]

ConsistencyInvariant ==
    \A r1, r2 \in ResourceManagers : ~ (resourceManagerState[r1] = "committed" /\ resourceManagerState[r2] = "aborted")

TransactionCommitInit ==
    resourceManagerState = [r \in ResourceManagers |-> "working"]

Prepare(r) ==
    /\ resourceManagerState[r] = "working"
    /\ resourceManagerState' = [s \in ResourceManagers |-> IF s = r THEN "prepared" ELSE resourceManagerState[s]]

DecideCommit(r) ==
    /\ resourceManagerState[r] = "prepared"
    /\ \A s \in ResourceManagers : resourceManagerState[s] \in {"prepared", "committed"}
    /\ resourceManagerState' = [s \in ResourceManagers |-> IF s = r THEN "committed" ELSE resourceManagerState[s]]

DecideAbort(r) ==
    /\ resourceManagerState[r] \in {"working", "prepared"}
    /\ \A s \in ResourceManagers : resourceManagerState[s] # "committed"
    /\ resourceManagerState' = [s \in ResourceManagers |-> IF s = r THEN "aborted" ELSE resourceManagerState[s]]

Decide(r) ==
    DecideCommit(r) \/ DecideAbort(r)
                
TransactionCommitNext ==
    \E r \in ResourceManagers : Prepare(r) \/ Decide(r) 

=============================================================================
