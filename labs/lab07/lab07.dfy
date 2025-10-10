// Credit: Some boilerplate adapted from Manos' in-class demo (Ch.5, F25)
include "UtilitiesLibrary.dfy"

module HostIdentifiers {
    type HostId = int 

    ghost predicate ValidHostId(numHosts: nat, hostid: HostId) {
        0 <= hostid < numHosts
    }
}

module Network {
    import opened UtilitiesLibrary

    datatype MessageOps<Message> = MessageOps(recv: Option<Message>, send: Option<Message>)

    datatype Constants = Constants(numHosts: nat)
    {
        ghost predicate Configure(numHosts: nat) {
            this.numHosts == numHosts
        }
    }

    // Fill in
    datatype Variables<Message> = Variables(/* */)

    // Fill in
    ghost predicate Init<Message>(c: Constants, v: Variables<Message>)
    {
        true
    }

    // Fill in
    ghost predicate Next<Message>(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        true
    }
}


module Host {
    import opened UtilitiesLibrary
    import opened HostIdentifiers
    import Network

    datatype Message = TransferLockMsg(dest: HostId)

    datatype Constants = Constants(numHosts: nat, myId: HostId) {
        // Our constants are determined by the DistributedSystem.
        // DistributedSystem tells us how many hosts are in the distributed system.
        // DistributedSystem tells us our id so we can recognize inbound messages.
        ghost predicate Configure(numHosts: nat, id: HostId) {
            && this.numHosts == numHosts
            && this.myId == id
        }
    }

    datatype Variables = Variables(
        holdsLock: bool
    )

    // Fill in
    ghost predicate Init(c: Constants, v: Variables) {
        true
    }

    // Fill in
    ghost predicate SendLock(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, recipient: HostId) {
        true
    }

    // Fill in
    ghost predicate ReceiveLock(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>) {
        true
    }

    datatype Step =
        | SendLock(recipient: HostId)
        | ReceiveLock

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>, step: Step) {
        match step {
            case SendLock(recipient) => SendLock(c, v, v', msgOps, recipient)
            case ReceiveLock => ReceiveLock(c, v, v', msgOps)
        }
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: Network.MessageOps<Message>) {
        exists step :: NextStep(c, v, v', msgOps, step)
    }
}

module DistributedSystem {
    import opened HostIdentifiers
    import Host
    import Network

    datatype Constants = Constants(
        hosts: seq<Host.Constants>,
        network: Network.Constants
    ) {
        ghost predicate WellFormed() {
            // Network numHosts and each host's numHosts agree with the size of our own host list
            && network.Configure(|hosts|)
            && (forall id | ValidHostId(id) :: hosts[id].Configure(|hosts|, id))  // every host knows its id (and ids are unique)
        }

        ghost predicate ValidHostId(hostid: HostId) {
            HostIdentifiers.ValidHostId(|hosts|, hostid)
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables<Host.Message>
    ) {
        ghost predicate WellFormed(c: Constants) {
            && c.WellFormed()
            && |hosts| == |c.hosts|
        }
    }

    // Fill in
    ghost predicate Init(c:Constants, v:Variables) {
        && v.WellFormed(c)
        && true // What is true about the hosts and network?
    }

    // JayNF
    datatype Step = Step(id: HostId, msgOps: Network.MessageOps<Host.Message>)

    // Fill in
    ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
        && v.WellFormed(c)
        && v'.WellFormed(c)
        && c.ValidHostId(step.id)
        && true // The network steps, and ONE host steps, given by step.id
    }

    ghost predicate Next(c:Constants, v:Variables, v':Variables) {
        exists step :: NextStep(c, v, v', step)
    }
}

module SafetySpec {
    import opened HostIdentifiers
    import DistributedSystem

    // Fill in
    ghost predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
        && v.WellFormed(c)
        && true
    }
}

module Proof {
    import opened HostIdentifiers
    import Host
    import opened DistributedSystem
    import opened SafetySpec

    // Fill in
    ghost predicate Inv(c: Constants, v:Variables) {
        && Safety(c, v)
        && true
    }

    lemma InitImpliesInv(c: Constants, v: Variables)
        requires Init(c, v)
        ensures Inv(c, v)
    {
    }

    // Might not need proof
    lemma NextMaintainsInv(c: Constants, v: Variables, v': Variables) 
        requires Inv(c, v)
        requires DistributedSystem.Next(c, v, v')
        ensures Inv(c, v')
    {
    }

    // Might not need proof
    lemma InvImpliesSafety(c: Constants, v: Variables)
        requires Inv(c, v)
        ensures Safety(c, v)
    {
    }
}