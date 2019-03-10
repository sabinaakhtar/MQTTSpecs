------------------------------ MODULE MQTT ---------------------------

EXTENDS  Sequences,Naturals,TLC,FiniteSets

CONSTANTS any

VARIABLES depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack, _pc

vars == << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack, _pc >>

upperbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : n >= m

lowerbound(S) == CHOOSE n \in S : 
            /\ \A m \in S : m >= n

Broker == 
          LET Broker_start == 1 IN 
           LET Broker_end == 1 IN
               Broker_start .. Broker_end

Publisher == 
             LET Publisher_start == upperbound(Broker) + 1 IN 
              LET Publisher_end == upperbound(Broker) + 1 IN
                  Publisher_start .. Publisher_end

Subscriber == 
              LET Subscriber_start == upperbound(Publisher) + 1 IN 
               LET Subscriber_end == upperbound(Publisher) + 2 IN
                   Subscriber_start .. Subscriber_end

ProcSet == Broker \cup Publisher \cup Subscriber

send(ch,msg) == [network EXCEPT ![ch] = Append(@, msg)]

Init == 
    /\ depth = 0
    /\ cp = any
    /\ network = [p \in ((Broker \cup Publisher) \cup Subscriber) |-> <<>>]
    /\ activeClients = {}
    /\ Topics = {"A", "B", "C"}
    /\ TopicPool = [t \in Topics |-> {}]
    /\ _Broker_data = [self \in Broker |-> [ self |-> self, parentID |-> 0, Name|->"Broker", rules|->0, status|->0, statusRecord|->0, wait_REL|->{}]]

    /\ _Publisher_data = [self \in Publisher |-> [ self |-> self, parentID |-> 0, Name|->"Publisher", CONNSUCC|->FALSE, PUBSUCC|->FALSE, BrokerID|->1]]

    /\ _Subscriber_data = [self \in Subscriber |-> [ self |-> self, parentID |-> 0, Name|->"Subscriber", rules|->0, BrokerID|->1, SUBSUCC|->FALSE, CONNSUCC|->FALSE, PUBRECE|->FALSE]]

    /\ _stack = [self \in ProcSet |-> << >>]
    /\ _pc = [self \in ProcSet |-> CASE self \in Broker -> "listen"
                         []self \in Publisher -> "PubStart"
                         []self \in Subscriber -> "Sub_start"]

Push(s,e) == e \circ s 

Lbl_1(self) == 
               /\ _pc[self] = "Lbl_1"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Lbl_2(self) == 
               /\ _pc[self] = "Lbl_2"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREL", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Lbl_3(self) == 
               /\ _pc[self] = "Lbl_3"
               /\ (cp = any \/ cp = self)
               /\ \/ /\ (({Head(_stack[self]).pkt.sender} \cap activeClients) # {})
                        /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PINGRESP", sender |-> self]) IN
                           /\ network' = _network
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                  \/ /\ ~((({Head(_stack[self]).pkt.sender} \cap activeClients) # {}))
                           /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                           /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
cqos2(self) == 
               /\ _pc[self] = "cqos2"
               /\ (cp = any \/ cp = self)
               /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "waitPUB2"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
waitPUB2(self) == 
                  /\ _pc[self] = "waitPUB2"
                  /\ (cp = any \/ cp = self)
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "PUBREC")
                                    /\ LET _network == send(Head(_stack[self]).to, [type |-> "PUBREL", sender |-> self, topic |-> "A", QoS |-> 2]) IN
                                       LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                       /\ network' = __network
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                              \/ /\ ~((packet.type = "PUBREC"))
                                    /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       /\ network' = _network
                                       /\ _pc' = [_pc EXCEPT ![self] = "waitPUBCOMP2"]
                                       /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
waitPUBCOMP2(self) == 
                      /\ _pc[self] = "waitPUBCOMP2"
                      /\ (cp = any \/ cp = self)
                      /\ \/ /\ (Len(network[self]) > 0)
                               /\ LET pkt == Head(network[self]) IN
                                  \/ /\ (pkt.type = "PUBCOMP")
                                        /\ LET _newhead == Head(_stack[self]) IN
                                           LET __newhead == [_newhead EXCEPT !.PUBSUCC = TRUE ] IN
                                           LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                           LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                           LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (Head(___stack[self]).PUBSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                           \/ /\ ~((Head(___stack[self]).PUBSUCC = TRUE))
                                                    /\ _stack' = ___stack
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                  \/ /\ ~((pkt.type = "PUBCOMP"))
                                        /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (Head(_stack[self]).PUBSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                           \/ /\ ~((Head(_stack[self]).PUBSUCC = TRUE))
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
rqos2(self) == 
               /\ _pc[self] = "rqos2"
               /\ (cp = any \/ cp = self)
               /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREC", sender |-> self]) IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "waitPUBREL"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
waitPUBREL(self) == 
                    /\ _pc[self] = "waitPUBREL"
                    /\ (cp = any \/ cp = self)
                    /\ \/ /\ (Len(network[self]) > 0)
                             /\ LET packet == Head(network[self]) IN
                                \/ /\ (packet.type = "PUBREL")
                                      /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                                         LET _newhead == Head(_stack[self]) IN
                                         LET __newhead == [_newhead EXCEPT !.PUBSUCC = TRUE ] IN
                                         LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                         LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<__newhead>>) ] IN
                                         LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                         \/ /\ (Head(___stack[self]).PUBSUCC = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                  /\ network' = __network
                                                  /\ _stack' = ___stack
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                         \/ /\ ~((Head(___stack[self]).PUBSUCC = TRUE))
                                                  /\ _stack' = ___stack
                                                  /\ network' = __network
                                                  /\ _pc' = [_pc EXCEPT ![self] = "rqos2"]
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                \/ /\ ~((packet.type = "PUBREL"))
                                      /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                         \/ /\ (Head(_stack[self]).PUBSUCC = TRUE)
                                                  /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                  /\ network' = _network
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                         \/ /\ ~((Head(_stack[self]).PUBSUCC = TRUE))
                                                  /\ network' = _network
                                                  /\ _pc' = [_pc EXCEPT ![self] = "rqos2"]
                                                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
l1(self) == 
            /\ _pc[self] = "l1"
            /\ (cp = any \/ cp = self)
            /\ \/ /\ (Head(_stack[self]).pkt.QoS = 0)
                     /\ \/ /\ (TopicPool[Head(_stack[self]).pkt.topic] # {})
                                 /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                 /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                        \/ /\ ~((TopicPool[Head(_stack[self]).pkt.topic] # {}))
                                 /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                 /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 1)
                        /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                        /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
               \/ /\ (Head(_stack[self]).pkt.QoS = 2)
                     /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBREC", sender |-> self]) IN
                        LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \cup {Head(_stack[self]).pkt.sender})] IN
                        /\ network' = _network
                        /\ _Broker_data' = __Broker_data
                        /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                        /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Publisher_data, _Subscriber_data, _stack >>
Lbl_4(self) == 
               /\ _pc[self] = "Lbl_4"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead1 == Head(_stack[self]) IN
                                LET _newHead1 == [newHead1 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead1>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead2 == Head(_stack[self]) IN
                                              LET _newHead2 == [newHead2 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead2>>) ] IN
                                              LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, QoS |-> 0]) IN
                                              LET __newhead == Head(___stack[self]) IN
                                              LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                              LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                              LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                              /\ IF Head(_____stack[self]).idS_sub # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_4"]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                                    ELSE
                                                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                      ELSE
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Lbl_5(self) == 
               /\ _pc[self] = "Lbl_5"
               /\ (cp = any \/ cp = self)
               /\ IF TopicPool[Head(_stack[self]).pkt.topic] # {} /\ Head(_stack[self]).idS_sub = {}
                        THEN /\ LET newHead3 == Head(_stack[self]) IN
                                LET _newHead3 == [newHead3 EXCEPT !.idS_sub = TopicPool[Head(_stack[self]).pkt.topic] ] IN
                                LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead3>>) ] IN
                                /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                /\ _stack' = ___stack
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                        ELSE
                             /\ IF Head(_stack[self]).idS_sub # {}
                                      THEN /\ LET sub == CHOOSE fech \in Head(_stack[self]).idS_sub : TRUE IN
                                              LET newHead4 == Head(_stack[self]) IN
                                              LET _newHead4 == [newHead4 EXCEPT !.sub = sub ] IN
                                              LET __stack == [_stack EXCEPT ![self] = Tail(_stack[self]) ] IN
                                              LET ___stack == [__stack EXCEPT ![self] = Push(__stack[self], <<_newHead4>>) ] IN
                                              LET _network == send(Head(___stack[self]).sub, [type |-> "PUBLISH", sender |-> self, QoS |-> 1]) IN
                                              LET __newhead == Head(___stack[self]) IN
                                              LET ___newhead == [__newhead EXCEPT !.idS_sub = Head(___stack[self]).idS_sub \ {Head(___stack[self]).sub } ] IN
                                              LET ____stack == [___stack EXCEPT ![self] = Tail(___stack[self]) ] IN
                                              LET _____stack == [____stack EXCEPT ![self] = Push(____stack[self], <<___newhead>>) ] IN
                                              /\ IF Head(_____stack[self]).idS_sub # {}
                                                    THEN    /\ _pc' = [_pc EXCEPT ![self] = "Lbl_5"]
                                                            /\ _stack' = _____stack
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                                    ELSE
                                                         /\ LET __network == send(Head(_____stack[self]).pkt.sender, [type |-> "PUBACK", sender |-> self]) IN
                                                            /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                                            /\ _stack' = _____stack
                                                            /\ network' = __network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                                      ELSE
                                           /\ LET _network == send(Head(_stack[self]).pkt.sender, [type |-> "PUBACK", sender |-> self]) IN
                                              /\ _pc' = [_pc EXCEPT ![self] = Head(_stack[self])._pc]
                                              /\ network' = _network
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
listen(self) == 
                /\ _pc[self] = "listen"
                /\ cp = any
                /\ \/ /\ (Len(network[self]) > 0)
                         /\ LET packet == Head(network[self]) IN
                            \/ /\ (packet.type = "CONNECT")
                                  /\ LET _activeClients == (activeClients \cup {packet.sender}) IN
                                     LET _network == send(packet.sender, [type |-> "CONNACK", sender |-> self]) IN
                                     LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                     /\ activeClients' = _activeClients
                                     /\ network' = __network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                            \/ /\ (packet.type = "PUBLISH")
                                  /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, sub|->0, idS_sub|->{}, _pc |->"listen"]>>)] IN
                                     /\ _pc' = [_pc EXCEPT ![self] = "l1"]
                                     /\ network' = _network
                                     /\ _stack' = __stack
                                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                            \/ /\ (packet.type = "PUBACK")
                                  /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                            \/ /\ (packet.type = "PUBREL")
                                  /\ \/ /\ (({packet.sender} \cap _Broker_data[self].wait_REL) # {})
                                           /\ LET __Broker_data == [_Broker_data EXCEPT ![self].wait_REL = (_Broker_data[self].wait_REL \ {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "PUBCOMP", sender |-> self]) IN
                                              LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                              /\ _Broker_data' = __Broker_data
                                              /\ network' = __network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Publisher_data, _Subscriber_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap _Broker_data[self].wait_REL) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                            \/ /\ (packet.type = "SUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \cup {packet.sender})] IN
                                              LET _network == send(packet.sender, [type |-> "SUBACK", sender |-> self]) IN
                                              LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = __network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                            \/ /\ (packet.type = "UNSUBSCRIBE")
                                  /\ \/ /\ (({packet.sender} \cap activeClients) # {})
                                           /\ LET _TopicPool == [TopicPool EXCEPT ![packet.topic] = (TopicPool[packet.topic] \ {packet.sender})] IN
                                              LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ TopicPool' = _TopicPool
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                     \/ /\ ~((({packet.sender} \cap activeClients) # {}))
                                           /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                              /\ network' = _network
                                              /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                              /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                            \/ /\ (packet.type = "PINGREQ")
                                  /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[pkt|->packet, _pc |->"Lbl_6"]>>)] IN
                                     /\ _pc' = [_pc EXCEPT ![self] = "Lbl_3"]
                                     /\ _stack' = __stack
                                     /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
                            \/ /\ (packet.type = "DISCONNECT")
                                  /\ LET _activeClients == (activeClients \ {packet.sender}) IN
                                     LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                     /\ activeClients' = _activeClients
                                     /\ network' = _network
                                     /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                                     /\ UNCHANGED << depth, cp, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                   \/ /\ ~((Len(network[self]) > 0))
                            /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                            /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Lbl_6(self) == 
               /\ _pc[self] = "Lbl_6"
               /\ cp = any
               /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                  /\ network' = _network
                  /\ _pc' = [_pc EXCEPT ![self] = "listen"]
                  /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
_Broker(self) == 
                     listen(self) \/ Lbl_6(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self) \/ l1(self) \/ Lbl_4(self) \/ Lbl_5(self)  
PubStart(self) == 
                  /\ _pc[self] = "PubStart"
                  /\ cp = any
                  /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "CONNECT", sender |-> self]) IN
                     /\ network' = _network
                     /\ _pc' = [_pc EXCEPT ![self] = "waitCONN"]
                     /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
waitCONN(self) == 
                  /\ _pc[self] = "waitCONN"
                  /\ cp = any
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "CONNACK")
                                    /\ LET __Publisher_data == [_Publisher_data EXCEPT ![self].CONNSUCC = TRUE] IN
                                       LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (__Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUBLISH"]
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Subscriber_data, _stack >>
                                       \/ /\ ~((__Publisher_data[self].CONNSUCC = TRUE))
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Subscriber_data, _stack >>
                              \/ /\ ~((packet.type = "CONNACK"))
                                    /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (_Publisher_data[self].CONNSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUBLISH"]
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                       \/ /\ ~((_Publisher_data[self].CONNSUCC = TRUE))
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "PubStart"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
tryPUBLISH(self) == 
                    /\ _pc[self] = "tryPUBLISH"
                    /\ cp = any
                    /\ \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "lbl"]
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                       \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                       \/ /\ TRUE
                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB2"]
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
lbl(self) == 
             /\ _pc[self] = "lbl"
             /\ cp = any
             /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 0]) IN
                /\ network' = _network
                /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
tryPUB1(self) == 
                 /\ _pc[self] = "tryPUB1"
                 /\ cp = any
                 /\ LET _network == send(_Publisher_data[self].BrokerID, [type |-> "PUBLISH", sender |-> self, topic |-> "A", QoS |-> 1]) IN
                    /\ network' = _network
                    /\ _pc' = [_pc EXCEPT ![self] = "waitPUB1"]
                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
waitPUB1(self) == 
                  /\ _pc[self] = "waitPUB1"
                  /\ cp = any
                  /\ \/ /\ (Len(network[self]) > 0)
                           /\ LET packet == Head(network[self]) IN
                              \/ /\ (packet.type = "PUBACK")
                                    /\ LET __Publisher_data == [_Publisher_data EXCEPT ![self].PUBSUCC = TRUE] IN
                                       LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (__Publisher_data[self].PUBSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Subscriber_data, _stack >>
                                       \/ /\ ~((__Publisher_data[self].PUBSUCC = TRUE))
                                                /\ _Publisher_data' = __Publisher_data
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Subscriber_data, _stack >>
                              \/ /\ ~((packet.type = "PUBACK"))
                                    /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                       \/ /\ (_Publisher_data[self].PUBSUCC = TRUE)
                                                /\ _pc' = [_pc EXCEPT ![self] = "Done"]
                                                /\ network' = _network
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                       \/ /\ ~((_Publisher_data[self].PUBSUCC = TRUE))
                                                /\ network' = _network
                                                /\ _pc' = [_pc EXCEPT ![self] = "tryPUB1"]
                                                /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
tryPUB2(self) == 
                 /\ _pc[self] = "tryPUB2"
                 /\ cp = any
                 /\ LET __stack == [_stack EXCEPT ![self] = Push(_stack[self], <<[to|->_Publisher_data[self].BrokerID, PUBSUCC|->FALSE, _pc |->"Done"]>>)] IN
                    /\ _pc' = [_pc EXCEPT ![self] = "cqos2"]
                    /\ _stack' = __stack
                    /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data >>
_Publisher(self) == 
                        PubStart(self) \/ waitCONN(self) \/ tryPUBLISH(self) \/ lbl(self) \/ tryPUB1(self) \/ waitPUB1(self) \/ tryPUB2(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self)  
Sub_start(self) == 
                   /\ _pc[self] = "Sub_start"
                   /\ cp = any
                   /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "CONNECT", sender |-> self]) IN
                      /\ network' = _network
                      /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitCONN"]
                      /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Sub_waitCONN(self) == 
                      /\ _pc[self] = "Sub_waitCONN"
                      /\ cp = any
                      /\ \/ /\ (Len(network[self]) > 0)
                               /\ LET packet == Head(network[self]) IN
                                  \/ /\ (packet.type = "CONNACK")
                                        /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].CONNSUCC = TRUE] IN
                                           LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (__Subscriber_data[self].CONNSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                    /\ _Subscriber_data' = __Subscriber_data
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                           \/ /\ ~((__Subscriber_data[self].CONNSUCC = TRUE))
                                                    /\ _Subscriber_data' = __Subscriber_data
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_start"]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                  \/ /\ ~((packet.type = "CONNACK"))
                                        /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                           \/ /\ (_Subscriber_data[self].CONNSUCC = TRUE)
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                    /\ network' = _network
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                           \/ /\ ~((_Subscriber_data[self].CONNSUCC = TRUE))
                                                    /\ network' = _network
                                                    /\ _pc' = [_pc EXCEPT ![self] = "Sub_start"]
                                                    /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Sub_subscription(self) == 
                          /\ _pc[self] = "Sub_subscription"
                          /\ cp = any
                          /\ LET _network == send(_Subscriber_data[self].BrokerID, [type |-> "SUBSCRIBE", topic |-> "A", sender |-> self]) IN
                             /\ network' = _network
                             /\ _pc' = [_pc EXCEPT ![self] = "Sub_waitsubscription"]
                             /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Sub_waitsubscription(self) == 
                              /\ _pc[self] = "Sub_waitsubscription"
                              /\ cp = any
                              /\ \/ /\ (Len(network[self]) > 0)
                                       /\ LET packet == Head(network[self]) IN
                                          \/ /\ (packet.type = "SUBACK")
                                                /\ LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].SUBSUCC = TRUE] IN
                                                   LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                                   \/ /\ (__Subscriber_data[self].SUBSUCC = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                            /\ _Subscriber_data' = __Subscriber_data
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                                   \/ /\ ~((__Subscriber_data[self].SUBSUCC = TRUE))
                                                            /\ _Subscriber_data' = __Subscriber_data
                                                            /\ network' = _network
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                                          \/ /\ ~((packet.type = "SUBACK"))
                                                /\ LET _network == [network EXCEPT ![self] = Tail(network[self])] IN
                                                   \/ /\ (_Subscriber_data[self].SUBSUCC = TRUE)
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                                            /\ network' = _network
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
                                                   \/ /\ ~((_Subscriber_data[self].SUBSUCC = TRUE))
                                                            /\ network' = _network
                                                            /\ _pc' = [_pc EXCEPT ![self] = "Sub_subscription"]
                                                            /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
Sub_listen(self) == 
                    /\ _pc[self] = "Sub_listen"
                    /\ cp = any
                    /\ \/ /\ (Len(network[self]) > 0)
                             /\ LET packet == Head(network[self]) IN
                                \/ /\ (packet.type = "PUBLISH")
                                      /\ LET _network == send(packet.sender, [type |-> "PUBACK", sender |-> self]) IN
                                         LET __Subscriber_data == [_Subscriber_data EXCEPT ![self].PUBRECE = TRUE] IN
                                         LET __network == [_network EXCEPT ![self] = Tail(_network[self])] IN
                                         /\ network' = __network
                                         /\ _Subscriber_data' = __Subscriber_data
                                         /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                         /\ UNCHANGED << depth, cp, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _stack >>
                       \/ /\ ~((Len(network[self]) > 0))
                                /\ _pc' = [_pc EXCEPT ![self] = "Sub_listen"]
                                /\ UNCHANGED << depth, cp, network, activeClients, Topics, TopicPool, _Broker_data, _Publisher_data, _Subscriber_data, _stack >>
_Subscriber(self) == 
                         Sub_start(self) \/ Sub_waitCONN(self) \/ Sub_subscription(self) \/ Sub_waitsubscription(self) \/ Sub_listen(self) \/ Lbl_1(self) \/ Lbl_2(self) \/ Lbl_3(self) \/ cqos2(self) \/ waitPUB2(self) \/ waitPUBCOMP2(self) \/ rqos2(self) \/ waitPUBREL(self)  

Next == (\E self \in Broker : _Broker(self))
                         \/ (\E self \in Publisher : _Publisher(self))
                         \/ (\E self \in Subscriber : _Subscriber(self))
                         \/ ((\A self \in ProcSet : _pc[self] = "Done")
                             /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Fairness == 
    /\ \A self \in Subscriber : /\ WF_vars(_Subscriber(self)) 

FairSpec == Spec /\ Fairness
=================================================================================
