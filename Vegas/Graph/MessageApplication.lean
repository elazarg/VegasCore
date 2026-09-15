/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.PublicEvaluation
import Interaction.CommitmentCandidates
import Interaction.MessageApplication

/-! # A public-message host for typed immutable graphs

This module executes `Vegas.Graph` directly.  The candidate catalogue and the
full `VEnv` are ideal private bookkeeping.  Public evaluation is deliberately
fed only `PublicValues`; in particular resolution validation cannot inspect a
sealed graph field.
-/

noncomputable section
namespace Vegas

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} {Δ : VCtx Player L}

/-- Hosting parameters for one fixed terminal graph context. -/
structure GraphRuntime (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] (Δ : VCtx Player L) where
  deadline : Nat → Nat

namespace GraphRuntime

/-- A dynamically typed wire value.  Wrong tags are ordinary malformed input. -/
structure Raw (L : IExpr) where
  ty : L.Ty
  value : L.Val ty

namespace Raw

def as? (raw : Raw L) (ty : L.Ty) : Option (L.Val ty) :=
  if h : raw.ty = ty then some (cast (congrArg L.Val h) raw.value) else none

@[simp] theorem as?_mk (ty : L.Ty) (value : L.Val ty) :
    (Raw.mk ty value).as? ty = some value := by simp [as?]

end Raw

instance : DecidableEq (Raw L) := fun left right =>
  if hty : left.ty = right.ty then
    match left, right, hty with
    | ⟨ty, leftValue⟩, ⟨_, rightValue⟩, rfl =>
        if hvalue : leftValue = rightValue then
          isTrue (by cases hvalue; rfl)
        else isFalse (by intro heq; cases heq; exact hvalue rfl)
  else isFalse (by intro heq; exact hty (congrArg Raw.ty heq))

inductive Slot where
  | initial (name : VarId)
  | prepared (serial : Nat)
  deriving DecidableEq

abbrev Handle (Player : Type) := CommitmentHandle Player Slot

/-- Accepted handles are indexed by immutable graph binding names. -/
abbrev Bindings (Player : Type) := List (VarId × Handle Player)

def lookupBinding (bindings : Bindings Player) (name : VarId) : Option (Handle Player) :=
  bindings.findSome? fun entry => if entry.1 = name then some entry.2 else none

/-- Public projection of the current existential graph prefix. -/
structure PublicView (Player : Type) (L : IExpr) where
  Γ : VCtx Player L
  values : PublicValues Γ
  pc : Nat
  clock : Nat
  enteredAt : Nat
  bindings : Bindings Player

/-- A player's application view.  The environment receives only `PublicView`.
The full observation is returned only to the authenticated player projection. -/
structure PlayerView (Player : Type) [DecidableEq Player] (L : IExpr) where
  who : Player
  publicState : PublicView Player L
  privateObservation : Observation L who publicState.Γ
  prepared : Nat → CommitmentCandidate (Raw L)

variable [R : IExpr.ResultTypes L]

/-- A running graph has an existential current context and a fixed terminal
context.  `ideal` is never passed to a public evaluator. -/
inductive State (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] (Δ : VCtx Player L) where
  | running {Γ : VCtx Player L}
      (next : Graph Player L Γ Δ)
      (ideal : VEnv L Γ)
      (publicValues : PublicValues Γ)
      (bindings : Bindings Player)
      (candidates : CommitmentCandidates Player Slot (Raw L))
      (pc clock enteredAt : Nat) : State Player L Δ

namespace State

private def initialEntries : (Γ : VCtx Player L) → VEnv L Γ →
    List (VarId × Player × Raw L)
  | [], _ => []
  | (_name, ⟨_ty, .pub⟩) :: Γ, input => initialEntries Γ (VEnv.tail input)
  | (name, ⟨ty, .sealed owner⟩) :: Γ, input =>
      (name, owner, ⟨ty, input.get .here⟩) :: initialEntries Γ (VEnv.tail input)

private def initialCandidates (entries : List (VarId × Player × Raw L)) :
    CommitmentCandidates Player Slot (Raw L) where
  table owner slot := match slot with
    | .prepared _ => .fresh
    | .initial name =>
        match entries.findSome? fun entry =>
          if entry.1 = name && entry.2.1 = owner then some entry.2.2 else none with
        | some raw => .openable raw
        | none => .fresh

private def initialBindings (entries : List (VarId × Player × Raw L)) : Bindings Player :=
  entries.map fun entry => (entry.1, (entry.2.1, .initial entry.1))

/-- Generate verification material for every sealed initial field. -/
def initial {Γ Δ : VCtx Player L} (graph : Graph Player L Γ Δ)
    (input : VEnv L Γ) : State Player L Δ :=
  let entries := initialEntries Γ input
  .running graph input (PublicValues.ofVEnv input) (initialBindings entries)
    (initialCandidates entries) 0 0 0

def publicView : State Player L Δ → PublicView Player L
  | .running _ _ values bindings _ pc clock enteredAt =>
      ⟨_, values, pc, clock, enteredAt, bindings⟩

def playerView (state : State Player L Δ) (who : Player) : PlayerView Player L :=
  match state with
  | .running _ ideal values bindings candidates pc clock enteredAt =>
      ⟨who, ⟨_, values, pc, clock, enteredAt, bindings⟩, observe who ideal,
        fun serial => candidates.lookup (who, .prepared serial)⟩

def candidates : State Player L Δ → CommitmentCandidates Player Slot (Raw L)
  | .running _ _ _ _ candidates _ _ _ => candidates

def outcome? : State Player L Δ → Option (VEnv L Δ)
  | .running (.ret _) ideal _ _ _ _ _ _ => some ideal
  | .running (.sample ..) _ _ _ _ _ _ _ => none
  | .running (.bind ..) _ _ _ _ _ _ _ => none
  | .running (.resolve ..) _ _ _ _ _ _ _ => none

end State

inductive Payload (Player : Type) (L : IExpr) where
  | commitment (site : Nat) (handle : Handle Player)
  | opening (site : Nat) (handle : Handle Player) (raw : Raw L)
  | withhold (site : Nat)
  | malformed (raw : Raw L)

inductive PrivateCommand (L : IExpr) where
  | prepare (slot : Nat) (raw : Raw L)
  /-- A policy-local marker.  The application state is unchanged; the shared
  runner nevertheless records it in authenticated own command history. -/
  | rememberDisclosure (disclose : Bool)

inductive EnvironmentCommand where
  | tick

def privateStep (_runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (who : Player) : PrivateCommand L → State Player L Δ
  | .prepare slot raw =>
      match state with
      | .running next ideal values bindings candidates pc clock enteredAt =>
          .running next ideal values bindings (candidates.prepare who (.prepared slot) raw)
            pc clock enteredAt
  | .rememberDisclosure _ => state

def advanceBind {Γ : VCtx Player L} {name : VarId} {owner : Player}
    {payload : L.Ty} {Δ : VCtx Player L}
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock : Nat) (handle : Handle Player) : State Player L Δ :=
  let stored : L.Val (R.result payload) :=
    match candidates.lookup handle with
    | .openable raw => (raw.as? (R.result payload)).getD
        ((R.valueEquiv payload).symm .failure)
    | .fresh | .unopenable => (R.valueEquiv payload).symm .failure
  .running next (VEnv.cons stored ideal) (PublicValues.consSealed values)
    ((name, handle) :: bindings) (candidates.accept handle) (pc + 1) clock clock

def advanceBindFailure {Γ : VCtx Player L} {name : VarId} {owner : Player}
    {payload : L.Ty} {Δ : VCtx Player L}
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock : Nat) : State Player L Δ :=
  let failed := (R.valueEquiv payload).symm (.failure)
  .running next (VEnv.cons failed ideal) (PublicValues.consSealed values)
    bindings candidates (pc + 1) clock clock

def advanceResolve {Γ : VCtx Player L} {outputName : VarId}
    {payload : L.Ty} {Δ : VCtx Player L}
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock : Nat)
    (result : PublicationResult (L.Val payload)) : State Player L Δ :=
  let encoded := (R.valueEquiv payload).symm result
  .running next (VEnv.cons encoded ideal) (PublicValues.consPublic encoded values)
    bindings candidates (pc + 1) clock clock

/-- Application inclusion.  Binding acceptance has one public transition
regardless of whether its candidate is openable.  Resolution uses only the
verified wire proposal and `PublicValues`; the private environment is merely
extended after that public result has been computed. -/
def handle (_runtime : GraphRuntime Player L Δ) (state : State Player L Δ)
    (message : Message Player (Payload Player L)) : Option (State Player L Δ) :=
  match state with
  | .running graph ideal values bindings candidates pc clock _enteredAt =>
    match graph, message.payload with
    | .bind _name owner _fresh next, .commitment site handle =>
        if site = pc && message.sender = owner && handle.1 = owner then
          some (advanceBind next ideal values bindings candidates pc clock handle)
        else none
    | .resolve _ owner bindingName _fresh _source checks next,
        .opening site handle raw =>
        if site = pc && message.sender = owner && handle.1 = owner &&
            lookupBinding bindings bindingName = some handle && candidates.verify handle raw then
          match raw.as? (R.result _) with
          | none => none
          | some encoded =>
              let proposal := R.valueEquiv _ encoded
              let accepted := acceptedProposal checks values proposal
              some (advanceResolve next ideal values bindings candidates pc clock accepted)
        else none
    | .resolve _ owner _ _ _ _ next, .withhold site =>
        if site = pc && message.sender = owner then
          some (advanceResolve next ideal values bindings candidates pc clock .failure)
        else none
    | _, _ => none

noncomputable def tick (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) : FinDist (State Player L Δ) :=
  match state with
  | .running graph ideal values bindings candidates pc clock enteredAt =>
      let clock' := clock + 1
      match graph with
      | .sample _ _ law next =>
          (law.evalPublic values).map fun value =>
            .running next (VEnv.cons value ideal) (PublicValues.consPublic value values)
              bindings candidates (pc + 1) clock' clock'
      | .bind name owner fresh next =>
          if runtime.deadline pc ≤ clock' - enteredAt then
            FinDist.pure (advanceBindFailure next ideal values bindings candidates pc clock')
          else FinDist.pure (.running (.bind name owner fresh next) ideal values bindings candidates
            pc clock' enteredAt)
      | .resolve outputName owner bindingName fresh source checks next =>
          if runtime.deadline pc ≤ clock' - enteredAt then
            FinDist.pure (advanceResolve next ideal values bindings candidates pc clock' .failure)
          else FinDist.pure (.running
            (.resolve outputName owner bindingName fresh source checks next)
            ideal values bindings candidates
            pc clock' enteredAt)
      | .ret payoffs => FinDist.pure (.running (.ret payoffs) ideal values bindings candidates
          pc clock' enteredAt)

noncomputable def environmentStep (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) : EnvironmentCommand → FinDist (State Player L Δ)
  | .tick => runtime.tick state

noncomputable def application (runtime : GraphRuntime Player L Δ) :
    Interaction.MessageApplication Player where
  Application := State Player L Δ
  Payload := Payload Player L
  PrivateCommand := PrivateCommand L
  EnvironmentCommand := EnvironmentCommand
  PlayerView := PlayerView Player L
  EnvironmentView := PublicView Player L
  privateStep := runtime.privateStep
  environmentStep := runtime.environmentStep
  handle := runtime.handle
  observePlayer := State.playerView
  observeEnvironment := State.publicView

@[simp] theorem privateStep_public (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L) :
    (runtime.privateStep state who command).publicView = state.publicView := by
  cases state
  cases command <;> rfl

@[simp] theorem handle_malformed (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (sender : Player) (raw : Raw L) :
    runtime.handle state ⟨(sender, 0), .malformed raw⟩ = none := by
  cases state with
  | running graph => cases graph <;> rfl

/-- Environment observation is definitionally public-only. -/
theorem observeEnvironment_eq (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) :
    runtime.application.observeEnvironment state = state.publicView := rfl

end GraphRuntime
end Vegas
