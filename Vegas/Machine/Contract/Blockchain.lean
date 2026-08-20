/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Contract.Configured

/-!
# Stochastic blockchain contract boundary

This pass separates transaction context from caller-supplied message data and
adds a minimal blockchain view. Its shape is suitable for later connection to
contract execution frameworks: a contract receives a chain view, call context,
current state, and message.

Vegas chance transitions are still exact `FinDist` laws, so this interface is
intentionally stochastic. A deterministic blockchain contract cannot implement
it until a later pass replaces each internal probability law with a concrete
entropy protocol and states the associated adversarial assumptions.

Height, slot, origin, contract address, balances, and transferred amount are
introduced but ignored by the configured Vegas transition. This makes their
semantic inertness explicit before later passes use them for timing, payments,
or entropy.
-/

noncomputable section

namespace Vegas.Machine.Contract.Blockchain

open EventGraph

variable {Player Address Word : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

/-- Read-only chain data supplied to one contract invocation. -/
structure ChainView where
  height : Nat
  slot : Nat
  finalizedHeight : Nat

/-- Invocation metadata supplied by the blockchain rather than serialized in
the message body. Amounts remain mathematical integers at this layer. -/
structure CallContext (Address : Type) where
  origin : Address
  sender : Address
  contractAddress : Address
  contractBalance : Int
  transferredAmount : Int

/-- Player entry-point arguments, excluding the physical caller. -/
structure PlayerMessage (Player Word : Type) where
  player : Player
  node : Nat
  value : Word

/-- Internal entry-point arguments, excluding the physical caller. -/
structure InternalMessage where
  node : Nat

/-- Caller-free configured-contract messages. -/
inductive Message (Player Word : Type) where
  | player (message : PlayerMessage Player Word)
  | internal (message : InternalMessage)

/-- A contract interface whose receive function may have a finite stochastic
successor law. No outbound calls or asset transfers are modeled yet. -/
structure StochasticContract (Address Message State : Type) where
  initial : State
  receive? :
    ChainView → CallContext Address → State → Message →
      Option (GameTheory.Math.Probability.FinDist State)

namespace PlayerMessage

/-- Encode a valid semantic commit without duplicating the authenticated
physical sender in the message body. -/
def encodeCommit (codec : StorageCodec program)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action) :
    PlayerMessage Player codec.Word where
  player := who
  node := action.node
  value := codec.encodeValue step.guard.ty step.value

end PlayerMessage

namespace InternalMessage

/-- Encode a valid graph-directed internal event. -/
def encode (event : InternalEvent program.graph) : InternalMessage where
  node := event.node

end InternalMessage

namespace Message

/-- Attach the authenticated blockchain sender to caller-free message data. -/
def contextualize (context : CallContext Address) :
    Message Player Word → ContractCalldata Player Address Word
  | .player message =>
      .player
        { caller := context.sender
          player := message.player
          node := message.node
          value := message.value }
  | .internal message =>
      .internal
        { caller := context.sender
          node := message.node }

end Message

end Vegas.Machine.Contract.Blockchain

namespace Vegas.Machine.Contract.ConfiguredContract

open EventGraph Blockchain

variable {Player Address : Type}
variable [DecidableEq Player] [DecidableEq Address]
variable {L : IExpr} {program : Program Player L}

variable (contract : ConfiguredContract program Address)

/-- Caller-free message type for this configured contract. -/
abbrev Message := Blockchain.Message Player contract.codec.Word

/-- Contextual validation. Only `context.sender` is operational at this pass. -/
def acceptsMessage (context : CallContext Address) (store : contract.Store)
    (message : contract.Message) : Bool :=
  contract.accepts store (message.contextualize context)

/-- Contextual execution. Chain metadata is deliberately inert at this pass. -/
def receive? (_chain : ChainView) (context : CallContext Address)
    (store : contract.Store) (message : contract.Message) :
    Option (GameTheory.Math.Probability.FinDist contract.Store) :=
  contract.execute? store (message.contextualize context)

/-- Package the configured contract at the stochastic blockchain boundary. -/
def toStochasticContract :
    StochasticContract Address contract.Message contract.Store where
  initial := contract.initialStore
  receive? := contract.receive?

/-- Contextual receive succeeds exactly when contextual validation accepts. -/
theorem receive?_isSome (chain : ChainView) (context : CallContext Address)
    (store : contract.Store) (message : contract.Message) :
    (contract.receive? chain context store message).isSome =
      contract.acceptsMessage context store message := by
  exact contract.execute?_isSome store (message.contextualize context)

/-- A semantic player commit submitted by its registered sender retains the
exact stored machine-step law in every otherwise arbitrary chain context. -/
theorem receive?_encodeState_playerCommit
    (chain : ChainView) (context : CallContext Address)
    {state : program.State} {who : Player}
    (action : CommitAction program.graph who)
    (step : CommitStep program.graph state.1 who action)
    (hsender : context.sender = contract.players.address who) :
    contract.receive? chain context
        (RawStore.encodeState contract.codec state)
        (.player (PlayerMessage.encodeCommit contract.codec action step)) =
      some ((program.step state (.commit who action step)).map
        (RawStore.encodeState contract.codec)) := by
  unfold receive? Message.contextualize PlayerMessage.encodeCommit
  rw [hsender]
  exact contract.execute?_encodeState_playerCommit action step

/-- An authorized internal event retains its exact stored machine-step law in
every otherwise arbitrary chain context. -/
theorem receive?_encodeState_internal
    (chain : ChainView) (context : CallContext Address)
    {state : program.State}
    (event : InternalEvent program.graph)
    (step : InternalStep program.graph state.1 event)
    (hauthorized :
      contract.triggers.allows context.sender event.node = true) :
    contract.receive? chain context
        (RawStore.encodeState contract.codec state)
        (.internal (InternalMessage.encode event)) =
      some ((program.step state (.internal event step)).map
        (RawStore.encodeState contract.codec)) := by
  exact contract.execute?_encodeState_internal
    context.sender event step hauthorized

/-- Every context/message pair accepted over encoded reachable storage
executes as a valid semantic command. Chain metadata and non-sender context
fields cannot create extra transitions at this pass. -/
theorem receive?_encodeState_of_accepts
    (chain : ChainView) (context : CallContext Address)
    (state : program.State) (message : contract.Message)
    (haccept :
      contract.acceptsMessage context
        (RawStore.encodeState contract.codec state) message = true) :
    ∃ command : program.Command state,
      contract.receive? chain context
          (RawStore.encodeState contract.codec state) message =
        some ((program.step state command).map
          (RawStore.encodeState contract.codec)) := by
  exact contract.execute?_encodeState_of_accepts
    state (message.contextualize context) haccept

end Vegas.Machine.Contract.ConfiguredContract
