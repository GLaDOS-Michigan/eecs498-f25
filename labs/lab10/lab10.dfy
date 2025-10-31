include "UtilitiesLibrary.dfy"

module Event {
    datatype Event = 
        | Event // Replace "Event" with world-visible events representing multiset
        | NoOp
}

module Spec {
    import opened Event

    datatype Constants = Constants()
    datatype Variables = Variables(/* Something here */)

    ghost predicate Init(c: Constants, v: Variables)
    {
        true // Replace me!
    }

    ghost predicate Insert(c: Constants, v: Variables, v': Variables, event: Event, item: int)
    {
        true // Replace me!
    }

    ghost predicate Remove(c: Constants, v: Variables, v': Variables, event: Event, item: int)
    {
        true // Replace me!
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event)
    {
        true // Replace me!
    }
}

module Types {
    import opened UtilitiesLibrary

    type HostId = nat
    datatype Message = Message // Replace me with appropriate message!
    datatype MessageOps = MessageOps(recv: Option<Message>, send: Option<Message>)
}


module Host {
    import opened Event
    import opened Types
    import opened UtilitiesLibrary

    datatype Constants = Constants(id: HostId, num_hosts: nat)
    {
        ghost predicate ValidHostId(id: HostId)
        {
            id < num_hosts
        }
    }

    datatype Variables = Variables(/* Something here */)

    ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && |grp_c| == |grp_v|
        && forall idx | 0 <= idx < |grp_v| :: (
            && |grp_c| == grp_c[idx].num_hosts
            && grp_c[idx].ValidHostId(grp_c[idx].id)
        )
    }

    ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
    {
        && GroupWF(grp_c, grp_v)
        && true // Replace me!
    }

    ghost predicate LocalInsert(c: Constants, v: Variables, v': Variables, event: Event, msgOps: MessageOps, item: int)
    {
        true // Replace me!
    }

    ghost predicate LocalRemove(c: Constants, v: Variables, v': Variables, event: Event, msgOps: MessageOps, item: int)
    {
        true // Replace me!
    }

    ghost predicate SendItem(c: Constants, v: Variables, v': Variables, event: Event, msgOps: MessageOps, item: int, dest: HostId)
    {
        true // Replace me!
    }

    ghost predicate ReceiveItem(c: Constants, v: Variables, v': Variables, event: Event, msgOps: MessageOps)
    {
        true // Replace me!
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, event: Event, msgOps: MessageOps)
    {
        true // Replace me!
    }
}

// "Deliver at most once" type of network
module Network {
    import opened UtilitiesLibrary
    import opened Types

    datatype Constants = Constants
    datatype Variables = Variables(inFlightMessages: set<Message>)

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.inFlightMessages == {}
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
    {
        // Only allow receipt of a message if we've seen it has been sent.
        && (msgOps.recv.Some? ==> msgOps.recv.value in v.inFlightMessages)

        // Only allow sending a message if there isn't a duplicate of that
        // message already sent but not yet delivered.
        && (msgOps.send.Some? ==> msgOps.send.value !in v.inFlightMessages)

        // Record the sent message, if there was one.
        && v'.inFlightMessages ==
            v.inFlightMessages
                // remove a message "used up" by receipt
                - (if msgOps.recv.None? then {} else { msgOps.recv.value })
                // add a new message supplied by send
                + (if msgOps.send.None? then {} else { msgOps.send.value })
    }
}

module DistributedSystem {
    import opened Event
    import opened UtilitiesLibrary
    import opened Types
    import Network
    import Host

    datatype Constants = Constants(
        totalKeys: nat,
        hosts: seq<Host.Constants>,
        network: Network.Constants)
    {
        ghost predicate WF() {
            0 < |hosts|
        }

        ghost predicate ValidHostId(id: HostId) {
            id < |hosts|
        }
    }

    datatype Variables = Variables(
        hosts: seq<Host.Variables>,
        network: Network.Variables
        )
    {
        ghost predicate WF(c: Constants) {
            && c.WF()
            && Host.GroupWF(c.hosts, hosts)
            && |hosts| == |c.hosts|
        }
    }

    ghost predicate Init(c: Constants, v: Variables)
    {
        && v.WF(c)
        && Host.GroupInit(c.hosts, v.hosts)
        && Network.Init(c.network, v.network)
    }

    ghost predicate HostAction(c: Constants, v: Variables, v': Variables, evt: Event, hostid: HostId, msgOps: MessageOps)
    {
        && v.WF(c)
        && v'.WF(c)
        && c.ValidHostId(hostid)
        && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], evt, msgOps)
        // all other hosts UNCHANGED
        && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
    }

    datatype Step =
        | HostActionStep(hostid: HostId, msgOps: MessageOps)

    ghost predicate NextStep(c: Constants, v: Variables, v': Variables, evt: Event, step: Step)
    {
        && HostAction(c, v, v', evt, step.hostid, step.msgOps)
        // network agrees recv has been sent and records sent
        && Network.Next(c.network, v.network, v'.network, step.msgOps)
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event)
    {
        exists step :: NextStep(c, v, v', evt, step)
    }
}


module RefinementTheorem {
    import opened Event
    import opened Types
    import Spec
    import Host
    import DistributedSystem

    // Add lemmas and helper functions as needed



    ghost function ConstantsAbstraction(c: DistributedSystem.Constants) : Spec.Constants
        requires c.WF()
    {
        Spec.Constants()
    }

    ghost function VariablesAbstraction(c: DistributedSystem.Constants, v: DistributedSystem.Variables) : Spec.Variables
        requires v.WF(c)
    {
        Spec.Variables()
    }

    lemma RefinementInit(c: DistributedSystem.Constants, v: DistributedSystem.Variables)
        requires DistributedSystem.Init(c, v)
        ensures Spec.Init(ConstantsAbstraction(c), VariablesAbstraction(c, v))
    {
    }
    
    lemma RefinementNext(c: DistributedSystem.Constants, v: DistributedSystem.Variables, v': DistributedSystem.Variables, evt: Event)
        requires DistributedSystem.Next(c, v, v', evt)
        ensures Spec.Next(ConstantsAbstraction(c), VariablesAbstraction(c, v), VariablesAbstraction(c, v'), evt) || (VariablesAbstraction(c, v) == VariablesAbstraction(c, v') && evt == NoOp)
    {
    }
}
