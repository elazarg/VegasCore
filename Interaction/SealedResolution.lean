/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedApplication

/-! # Continuing sealed programs after a missed deadline

Each node receives a relative deadline when its public prerequisites first
complete. Expiring a commitment records logical completion without registering
or accepting a handle. Its ready reveal publishes the designated null value.
Expiring an accepted reveal publishes that same null value without overwriting
the private service. Later application nodes remain executable.

The kernel reuses the sealed validator, discharging only prerequisites already
completed by timeout. Its shared message application retains arbitrary traffic,
public inclusion receipts, principal-local registration, and full-pool
environment observations. The clock command advances one unit and resolves
expired ready nodes in source order. A round driver and a deadline-relative
service hypothesis must constrain when it is called; arbitrary clock-triggering
environment policies need not allow honest players to finish.

The runtime parameter `nullValue` is instantiated with `Option.none` by a
nullable backend. No utility, source guard, or persistent role-bail rule is
built into this runtime. Acyclic dependencies and a valid commitment producer
for each reveal are separate program admission conditions.
-/

namespace Interaction

universe uPrincipal uValue

namespace SealedProgram

variable {Principal : Type uPrincipal} {Value : Type uValue}

def Payload.node? : Payload Principal Value → Option Nat
  | .commitment node _ | .opening node _ _ | .cleartext node _ => some node
  | .malformed => none

end SealedProgram

structure SealedResolution (Principal : Type uPrincipal) (Value : Type uValue) where
  program : SealedProgram Principal
  nullValue : Value
  window : Nat

namespace SealedResolution

variable {Principal : Type uPrincipal} {Value : Type uValue}

structure PublicState (Principal : Type uPrincipal) (Value : Type uValue) where
  events : List (SealedProgram.Event Principal Value) := []
  timeouts : List Nat := []
  readyAt : List (Nat × Nat) := []
  clock : Nat := 0

structure ApplicationState (Principal : Type uPrincipal) (Value : Type uValue)
    (Service : Type (max uPrincipal uValue) := IdealCommitments Principal Nat Value) where
  service : Service
  visible : PublicState Principal Value

def PublicState.completed (state : PublicState Principal Value) (node : Nat) : Bool :=
  SealedProgram.done state.events node || state.timeouts.contains node

def PublicState.firstReady? (state : PublicState Principal Value) (node : Nat) : Option Nat :=
  state.readyAt.findSome? fun entry => if entry.1 = node then some entry.2 else none

/-- The first timestamp is retained even when the same node is scanned again. -/
def PublicState.stamp (state : PublicState Principal Value) (node : Nat) :
    PublicState Principal Value :=
  if (state.firstReady? node).isSome then state
  else { state with readyAt := state.readyAt ++ [(node, state.clock)] }

def PublicState.published? (state : PublicState Principal Value) (node : Nat) : Option Value :=
  state.events.findSome? fun event => match event with
    | .opened other value => if other = node then some value else none
    | .accepted _ _ => none

/-- Public resolution of a ready node. It never operates on the private table. -/
def expire (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat) (kind : SealedRuleKind Principal) :
    PublicState Principal Value :=
  match kind with
  | .commit _ => { state with timeouts := state.timeouts ++ [node] }
  | .reveal _ _ =>
      { state with events := state.events ++ [.opened node runtime.nullValue]
                   timeouts := state.timeouts ++ [node] }
  | .disabled => state

/-- One source-ordered scan step. Propagation of a defaulted commitment's
reveal needs no further clock tick and is not a second timeout. -/
def visit (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat) : PublicState Principal Value :=
  match runtime.program.rules[node]? with
  | none => state
  | some rule =>
      if state.completed node || !rule.requires.all state.completed then state
      else
        let stamped := state.stamp node
        let expireNow := resolveExpired &&
          decide ((stamped.firstReady? node).getD stamped.clock + runtime.window ≤ stamped.clock)
        match rule.kind with
        | .disabled => state
        | .reveal _ source =>
            if state.timeouts.contains source then
              { stamped with events := stamped.events ++ [.opened node runtime.nullValue] }
            else if expireNow then
              runtime.expire stamped node rule.kind
            else stamped
        | .commit _ =>
            if expireNow then
              runtime.expire stamped node rule.kind
            else stamped

/-- A backward-dependency program needs one increasing scan to propagate all
new defaults and timestamp nodes made ready by earlier completions. -/
def refresh (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) : PublicState Principal Value :=
  (List.range runtime.program.rules.length).foldl (runtime.visit resolveExpired) state

def initial (runtime : SealedResolution Principal Value) : ApplicationState Principal Value :=
  ⟨IdealCommitments.empty, runtime.refresh false {}⟩

/-- A clock boundary resolves expired nodes; inclusion alone never advances it. -/
def tick {Service : Type (max uPrincipal uValue)} (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value Service) :
    ApplicationState Principal Value Service :=
  let visible := runtime.refresh true { state.visible with clock := state.visible.clock + 1 }
  { state with visible }

/-- Reuse the original authentication, binding, and readiness validator.
A timed-out node cannot accept a later message. -/
def validateMessage? [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    Option (SealedProgram.Event Principal Value) :=
  if message.payload.node?.any state.visible.timeouts.contains then none
  else (runtime.program.discharge state.visible.timeouts).validateMessage?
    state.service state.visible.events message

def handle [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    Option (ApplicationState Principal Value) := do
  let event ← runtime.validateMessage? state message
  let visible := runtime.refresh false
    { state.visible with events := state.visible.events ++ [event] }
  some { state with visible }

/-- Host one commitment service under the same public clock, timeout rules,
message transport, and policy interface. Only preparation and authenticated
message application depend on the service. No service state enters a view. -/
noncomputable abbrev host
    {Service : Type (max uPrincipal uValue)}
    (runtime : SealedResolution Principal Value)
    (prepare : Service → Principal → Nat → Value → Service)
    (applyMessage : ApplicationState Principal Value Service →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value Service)) : MessageApplication Principal where
  Application := ApplicationState Principal Value Service
  Payload := SealedProgram.Payload Principal Value
  PrivateCommand := ULift.{uPrincipal} (Nat × Value)
  EnvironmentCommand := ULift.{max uPrincipal uValue} Unit
  PlayerView := PublicState Principal Value
  EnvironmentView := PublicState Principal Value
  privateStep state owner command :=
    { state with service := prepare state.service owner command.down.1 command.down.2 }
  environmentStep state _ := GameTheory.Math.Probability.FinDist.pure (runtime.tick state)
  handle := applyMessage
  observePlayer state _ := state.visible
  observeEnvironment state := state.visible

/-- The registered-site commitment service hosted by the shared runner.
Its acceptance requires an already registered canonical source-site handle. -/
noncomputable def messageApplication [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) : MessageApplication Principal :=
  runtime.host (Service := IdealCommitments Principal Nat Value)
    (fun state owner slot value => (state.sealValue owner slot value).state)
    runtime.handle

end SealedResolution
end Interaction
