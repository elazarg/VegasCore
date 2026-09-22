/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventService
import Interaction.MessageApplicationLocality

/-! # Player actions and private recall

One action records private data and optionally transmits a packet. Computation
is part of the policy function. A submission supplies its hidden opening data
at the same decision as its public envelope; the envelope alone enters the
network. Neither scratch commands nor preparation positions belong to this game.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Private opening data is interpreted only for an authored commitment to a
prepared-slot handle. It cannot change a meaning fixed by an earlier submission. -/
structure Submission (graph : Vegas.EventGraph Player L) where
  packet : Payload graph
  opening : Option (Raw L)

inductive Transmission (graph : Vegas.EventGraph Player L) where
  | submit (submission : Submission graph)
  | replay (id : MessageId Player)

/-- Private data can retain randomized choices for future decisions. It is
ordinary memory, with no instructions, resource allocation, or application effect. -/
structure PlayerAction (graph : Vegas.EventGraph Player L) where
  memory : List (Nat ⊕ Raw L)
  transmission : Option (Transmission graph)

def PlayerAction.wait : PlayerAction graph := ⟨[], none⟩

/-- The native view contains no application scratch-action cache. -/
structure NativeView (graph : Vegas.EventGraph Player L) where
  messages : MessagePool.View Player (Payload graph)
  who : Player
  publicView : PublicView graph
  observation : graph.PlayerObservation who
  candidates : CandidateSlot graph → CommitmentCandidate (Raw L)
  receipts : List (MessageId Player × Bool)

def NativeView.ofApplication (runtime : EventGraphRuntime graph)
    (view : runtime.application.View) : NativeView graph where
  messages := view.messages
  who := view.application.who
  publicView := view.application.publicView
  observation := view.application.observation
  candidates := view.application.candidates
  receipts := view.receipts

def nativeView (runtime : EventGraphRuntime graph) (state : runtime.application.State)
    (who : Player) : NativeView graph :=
  NativeView.ofApplication runtime (MessageApplication.State.observe runtime.application state who)

structure NativeEntry (graph : Vegas.EventGraph Player L) where
  beforeView : NativeView graph
  action : PlayerAction graph

abbrev NativePolicy (graph : Vegas.EventGraph Player L) :=
  List (NativeEntry graph) → NativeView graph → FinDist (PlayerAction graph)

structure NativeExecution (runtime : EventGraphRuntime graph) where
  native : runtime.application.State
  principalHistory : Player → List (NativeEntry graph)
  environmentHistory : List runtime.application.EnvironmentEntry

def NativeExecution.initial (runtime : EventGraphRuntime graph)
    (state : runtime.application.State) : NativeExecution runtime :=
  ⟨state, fun _ => [], []⟩

/-- Supply only the state and environment recall used by the existing wire
and service kernels. Their invocation never reads a player-command history. -/
def NativeExecution.environmentExecution (runtime : EventGraphRuntime graph)
    (execution : NativeExecution runtime) : runtime.application.PolicyExecution :=
  { native := execution.native
    principalHistory := fun _ => []
    environmentHistory := execution.environmentHistory
    nativeTrace := [] }

/-- Register opening data only for a fresh handle owned by the sender. Initial
handles and foreign handles cannot acquire meanings through this operation. -/
def Submission.register (submission : Submission graph) (state : State graph)
    (who : Player) : State graph :=
  match submission.packet, submission.opening with
  | .commitment _ (owner, .prepared serial), some raw =>
      if owner = who then
        { state with candidates := state.candidates.prepare who (.prepared serial) raw }
      else state
  | _, _ => state

def transmit (runtime : EventGraphRuntime graph) (who : Player)
    (state : runtime.application.State) : Option (Transmission graph) → runtime.application.State
  | none => state
  | some (.replay id) => { state with pool := (state.pool.replay who id).state }
  | some (.submit submission) =>
      { state with
        application := submitStep (submission.register state.application who) who submission.packet
        pool := (state.pool.submit who submission.packet).2 }

/-- One decision contributes exactly one recall entry, whether it sends or waits. -/
def takeAction (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph) : NativeExecution runtime :=
  { execution with
    native := runtime.transmit who execution.native action.transmission
    principalHistory := fun other =>
      if other = who then execution.principalHistory who ++
        [⟨runtime.nativeView execution.native who, action⟩]
      else execution.principalHistory other }

def actionStep (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph) :
    FinDist (NativeExecution runtime) := FinDist.pure (runtime.takeAction who execution action)

def invokeNative (runtime : EventGraphRuntime graph) (who : Player)
    (policy : NativePolicy graph) (execution : NativeExecution runtime) :
    FinDist (NativeExecution runtime) :=
  (policy (execution.principalHistory who) (runtime.nativeView execution.native who)).bind
    (runtime.actionStep who execution)

theorem takeAction_history_self (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph) :
    (runtime.takeAction who execution action).principalHistory who =
      execution.principalHistory who ++ [⟨runtime.nativeView execution.native who, action⟩] := by
  simp only [takeAction, ↓reduceIte]

theorem takeAction_memory_irrel (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (first second : List (Nat ⊕ Raw L))
    (transmission : Option (Transmission graph)) :
    (runtime.takeAction who execution ⟨first, transmission⟩).native =
      (runtime.takeAction who execution ⟨second, transmission⟩).native := rfl

/-- Lowering describes the implementation of registration, not strategic
intermediate positions or a program supplied by the player. -/
def Submission.registrationCommand (submission : Submission graph) (who : Player) :
    Option (PrivateCommand graph) :=
  match submission.packet, submission.opening with
  | .commitment _ (owner, .prepared serial), some raw =>
      if owner = who then some (.prepare serial raw) else none
  | _, _ => none

theorem Submission.register_eq (submission : Submission graph) (who : Player)
    (state : State graph) :
    submission.register state who =
      match submission.registrationCommand who with
      | none => state
      | some command => privateStep state who command := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot <;> cases opening <;>
        simp only [Submission.register, Submission.registrationCommand]
      split <;> rfl
  | opening event candidate raw | withhold event | malformed raw => rfl

theorem Submission.register_facts (submission : Submission graph) (who : Player)
    (state : State graph) :
    (submission.register state who).config = state.config ∧
      (submission.register state who).remembered = state.remembered ∧
      (submission.register state who).publicView = state.publicView := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot <;> cases opening <;>
        by_cases same : owner = who <;> simp [Submission.register, State.publicView, same]
  | opening event candidate raw | withhold event | malformed raw => exact ⟨rfl, rfl, rfl⟩

theorem transmit_application (runtime : EventGraphRuntime graph) (who : Player)
    (state : runtime.application.State) (transmission : Option (Transmission graph)) :
    let next := runtime.transmit who state transmission
    next.application.config = state.application.config ∧
      next.application.remembered = state.application.remembered ∧
      next.application.publicView = state.application.publicView := by
  cases transmission with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨rfl, rfl, rfl⟩
      | submit submission =>
          simpa only [transmit, submitStep_config, submitStep_remembered,
            submitStep_publicView] using submission.register_facts who state.application

/-- The wire receives only the packet. Hidden opening data does not enter
the pool, receipts, or public application projection at submission. -/
theorem transmit_submission_public (runtime : EventGraphRuntime graph) (who : Player)
    (state : runtime.application.State) (submission : Submission graph) :
    MessageApplication.State.environmentView runtime.application
        (runtime.transmit who state (some (.submit submission))) =
      ⟨(state.pool.submit who submission.packet).2,
        state.application.publicView, state.receipts⟩ := by
  change MessageInterface.EnvironmentObservation.mk
    (interface := runtime.application.toMessageInterface) _
    (submitStep (submission.register state.application who) who submission.packet).publicView _ = _
  rw [submitStep_publicView, (submission.register_facts who state.application).2.2]
  rfl

/-- A commitment is fixed as soon as it is submitted, including when its
opening data is absent, mistyped, or inconsistent with an already fixed handle. -/
theorem takeAction_commitment_fixed (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (memory : List (Nat ⊕ Raw L))
    (event : graph.EventId) (slot : CandidateSlot graph) (opening : Option (Raw L)) :
    let next := runtime.takeAction who execution
      ⟨memory, some (.submit ⟨.commitment event (who, slot), opening⟩)⟩
    next.native.application.candidates.lookup (who, slot) ≠ .fresh := by
  exact submitStep_commitment_fixed _ who event slot

theorem Submission.register_other (submission : Submission graph) (state : State graph)
    (actor observer : Player) (different : observer ≠ actor) :
    (submission.register state actor).playerView observer = state.playerView observer := by
  rw [submission.register_eq]
  cases registration : submission.registrationCommand actor with
  | none => rfl
  | some command => exact privateStep_playerView_other state actor observer different command

/-- A player's decision changes only that player's local information until
the network delivers or includes a packet. Private memory remains in own recall. -/
theorem takeAction_other_input (runtime : EventGraphRuntime graph) (actor observer : Player)
    (different : observer ≠ actor) (execution : NativeExecution runtime)
    (action : PlayerAction graph) :
    let next := runtime.takeAction actor execution action
    (next.principalHistory observer, runtime.nativeView next.native observer) =
      (execution.principalHistory observer, runtime.nativeView execution.native observer) := by
  have history : (runtime.takeAction actor execution action).principalHistory observer =
      execution.principalHistory observer := by simp only [takeAction, ite_eq_right different]
  apply Prod.ext history
  apply congrArg (NativeView.ofApplication runtime)
  change MessageApplication.State.observe runtime.application
    (runtime.transmit actor execution.native action.transmission) observer = _
  cases selected : action.transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [transmit, MessageApplication.State.observe,
            MessagePool.replay_other_observe _ _ _ _ different]
      | submit submission =>
          simp only [transmit, MessageApplication.State.observe, application,
            submitStep_playerView_other _ _ _ different,
            submission.register_other _ actor observer different, MessagePool.submit,
            MessagePool.observe, ite_eq_right different]

/-- A direct submission reuses the established native safety semantics. The
intermediate implementation states are absent from the strategic history. -/
theorem transmit_native (runtime : EventGraphRuntime graph) (who : Player)
    (state : runtime.application.State) (transmission : Option (Transmission graph)) :
    ∃ actions, runtime.application.run actions state =
      FinDist.pure (runtime.transmit who state transmission) := by
  cases transmission with
  | none => exact ⟨[], rfl⟩
  | some transmission =>
      cases transmission with
      | replay id => exact ⟨[.replay who id], by simp only [MessageApplication.run,
          MessageApplication.step, FinDist.pure_bind]; rfl⟩
      | submit submission =>
          cases registration : submission.registrationCommand who with
          | none =>
              refine ⟨[.submit who submission.packet], ?_⟩
              simp only [MessageApplication.run, MessageApplication.step, FinDist.pure_bind,
                transmit, submission.register_eq, registration]
              rfl
          | some command =>
              refine ⟨[.privateCommand who command, .submit who submission.packet], ?_⟩
              simp only [MessageApplication.run, MessageApplication.step, FinDist.pure_bind,
                transmit, submission.register_eq, registration]
              rfl

theorem actionStep_native (runtime : EventGraphRuntime graph) (who : Player)
    (execution next : NativeExecution runtime) (action : PlayerAction graph)
    (reached : next ∈ (runtime.actionStep who execution action).support) :
    ∃ actions, next.native ∈ (runtime.application.run actions execution.native).support := by
  have same := FinDist.mem_support_pure.mp reached
  subst next
  obtain ⟨actions, law⟩ := runtime.transmit_native who execution.native action.transmission
  exact ⟨actions, by rw [law]; exact FinDist.mem_support_pure.mpr rfl⟩

end Vegas.EventGraphRuntime
