--------------------------- MODULE TwoPhaseCommit ---------------------------
CONSTANT ResourceManagers
VARIABLES resourceManagerState, transactionManagerState, readyResourceManagers, messagesEverSent

TwoPhaseCommitMessages == [type: {"prepared"}, rm: ResourceManagers] \union [type: {"commit", "abort"}]

TwoPhaseCommitTypeOKInvariant ==
    /\ resourceManagerState \in [ResourceManagers -> {"working", "prepared", "committed", "aborted"}]
    /\ transactionManagerState \in {"init", "done"}
    /\ readyResourceManagers \subseteq ResourceManagers
    /\ messagesEverSent \subseteq TwoPhaseCommitMessages

TwoPhaseCommitInit ==
    /\ resourceManagerState = [r \in ResourceManagers |-> "working"]
    /\ transactionManagerState = "init"
    /\ readyResourceManagers = {}
    /\ messagesEverSent = {}

RmSendsPrepare(r) ==
    /\ resourceManagerState[r] = "working"
    /\ resourceManagerState' = [resourceManagerState EXCEPT ![r] = "prepared"]
    /\ messagesEverSent' = messagesEverSent \union {[type |-> "prepared", rm |-> r]}
    /\ UNCHANGED <<transactionManagerState, readyResourceManagers>>

TmReceivesPrepare(r) ==
    /\ transactionManagerState = "init"
    /\ [type |-> "prepared", rm |-> r] \in messagesEverSent
    /\ readyResourceManagers' = readyResourceManagers \union {r}
    /\ UNCHANGED <<resourceManagerState, transactionManagerState, messagesEverSent>>

TmSendsCommit ==
    /\ transactionManagerState = "init"
    /\ readyResourceManagers = ResourceManagers
    /\ transactionManagerState' = "done"
    /\ messagesEverSent' = messagesEverSent \union {[type |-> "commit"]}
    /\ UNCHANGED <<resourceManagerState, readyResourceManagers>>

TmSendsAbort ==
    /\ transactionManagerState = "init"
    /\ transactionManagerState' = "done"
    /\ messagesEverSent' = messagesEverSent \union {[type |-> "abort"]}
    /\ UNCHANGED <<resourceManagerState, readyResourceManagers>>

RmReceivesCommit(r) ==
    /\ resourceManagerState[r] = "prepared"
    /\ [type |-> "commit"] \in messagesEverSent
    /\ resourceManagerState' = [resourceManagerState EXCEPT ![r]= "committed"]
    /\ UNCHANGED <<transactionManagerState, readyResourceManagers, messagesEverSent>>

RmReceivesAbort(r) ==
    /\ resourceManagerState[r] = "prepared"
    /\ [type |-> "abort"] \in messagesEverSent
    /\ resourceManagerState' = [resourceManagerState EXCEPT ![r]= "aborted"]
    /\ UNCHANGED <<transactionManagerState, readyResourceManagers, messagesEverSent>>

RmAborts(r) ==
    /\ resourceManagerState[r] = "working"
    /\ resourceManagerState' = [resourceManagerState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<transactionManagerState, readyResourceManagers, messagesEverSent>>

TwoPhaseCommitNext ==
    \/ TmSendsCommit
    \/ TmSendsAbort
    \/ \E r \in ResourceManagers : RmAborts(r) \/ RmSendsPrepare(r) \/ TmReceivesPrepare(r) \/ RmReceivesCommit(r) \/ RmReceivesAbort(r)

=============================================================================
