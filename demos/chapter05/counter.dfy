include "UtilitiesLibrary.dfy"

module HostIdentifiers {
  type HostId = int 

  ghost predicate ValidHostId(numHosts: nat, hostid: HostId) {
    0 <= hostid < numHosts
  }

  ghost function AllHosts(numHosts: nat) : set<HostId> {
    set hostid:HostId |
      && 0 <= hostid < numHosts // This line is entirely redundant, but it satisfies Dafny's finite-set heuristic
      && ValidHostId(numHosts, hostid)
  }
}

module Network {
  import opened UtilitiesLibrary

  datatype MessageOps<Message> = MessageOps(recv:Option<Message>, send:Option<Message>)

  datatype Constants = Constants(numHosts: nat)
  {
    ghost predicate Configure(numHosts: nat) {
      this.numHosts == numHosts
    }
  }

  datatype Variables<Message> = Variables(sentMsgs:set<Message>)

  ghost predicate Init<Message>(c: Constants, v: Variables<Message>)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next<Message>(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && v'.sentMsgs ==
      v.sentMsgs + if msgOps.send.None? then {} else { msgOps.send.value }
  }
}


module Host {
  import opened UtilitiesLibrary
  import opened HostIdentifiers
  import Network

  datatype Message = SendCounterMsg(dest:HostId, counter:int)

  datatype Constants = Constants(numHosts: nat, myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    ghost predicate Configure(numHosts: nat, id:HostId) {
      && this.numHosts == numHosts
      && this.myId == id
    }
  }

  datatype Variables = Variables(
    counter: int
  )

  ghost predicate Init(c:Constants, v:Variables) {
    && v.counter == 0
  }

  ghost predicate SendCounter(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, recipient:HostId) {
    && msgOps.recv.None?
    && ValidHostId(c.numHosts, recipient) // Doesn't actually affect safety, but does affect liveness! if we grant to msgOps nonexistent host, no further steps will occur.
    && msgOps.send == Some(SendCounterMsg(recipient, v.counter))
    && v'.counter == v.counter
  }

  ghost predicate ReceiveCounter(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    && msgOps.recv.Some?
    && msgOps.recv.value.dest == c.myId
    && msgOps.send == None
    && v'.counter == msgOps.recv.value.counter
  }

  ghost predicate IncrementCounter(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    && msgOps.send == None
    && msgOps.recv == None
    && v'.counter == v.counter + 1
  }

  datatype Step =
    | SendCounterStep(recipient: HostId)
    | ReceiveCounterStep()
    | IncrementCounterStep()

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
      case SendCounterStep(recipient) => SendCounter(c, v, v', msgOps, recipient)
      case ReceiveCounterStep => ReceiveCounter(c, v, v', msgOps)
      case IncrementCounterStep => IncrementCounter(c, v, v', msgOps)
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}

module DistributedSystem {
  import opened HostIdentifiers
  import Host
  import Network

  datatype Constants = Constants(
    hosts:seq<Host.Constants>,
    network:Network.Constants) {
    ghost predicate WF() {
      // Network numHosts and each host's numHosts agree with the size of our
      // own host list
      && network.Configure(|hosts|)
      && (forall id | ValidHostId(id) :: hosts[id].Configure(|hosts|, id))  // every host knows its id (and ids are unique)
    }

    ghost predicate ValidHostId(hostid: HostId) {
      HostIdentifiers.ValidHostId(|hosts|, hostid)
    }
  }

  datatype Variables = Variables(
    hosts:seq<Host.Variables>,
    network:Network.Variables<Host.Message>) {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  ghost predicate Init(c:Constants, v:Variables) {
    && v.WF(c)
    && (forall id | c.ValidHostId(id) :: Host.Init(c.hosts[id], v.hosts[id]))
    && Network.Init(c.network, v.network)
  }

  // JayNF
  datatype Step = Step(id:HostId, msgOps: Network.MessageOps<Host.Message>)

  ghost predicate NextStep(c:Constants, v:Variables, v':Variables, step: Step) {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(step.id)
    && Host.Next(c.hosts[step.id], v.hosts[step.id], v'.hosts[step.id], step.msgOps)
    && (forall other | c.ValidHostId(other) && other != step.id :: v'.hosts[other] == v.hosts[other])
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c:Constants, v:Variables, v':Variables) {
    exists step :: NextStep(c, v, v', step)
  }
}

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // No two hosts think they hold the lock simultaneously.
  ghost predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
    && v.WF(c)
    && (forall i | c.ValidHostId(i) :: v.hosts[i].counter >= 0
      )
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  ghost predicate Inv(c: Constants, v:Variables) {
    && Safety(c, v)
  }

  lemma NextMaintainsInv(c: Constants, v:Variables, v':Variables) 
    requires Inv(c, v)
    requires DistributedSystem.Next(c, v, v')
    ensures Inv(c, v')
  {

  }

  lemma SafetyProof(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    ensures Inv(c, v) ==> Safety(c, v)
  {
    if Inv(c, v) && Next(c, v, v') {
      NextMaintainsInv(c, v, v');
    }
  }
}