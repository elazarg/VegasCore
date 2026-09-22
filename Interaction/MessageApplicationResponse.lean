/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationLocality
import Interaction.MessageApplicationPolicyLaws

/-! # Private work within a player response

A response contains a finite private program and one network command. The
runtime executes the whole response at one invocation, without intervening
delivery, inclusion, clock ticks, or policy calls. Internal commands remain
in the owner's recall and the proof-facing native trace. Their count is not
a service budget. Submission still enters the pending pool, awaiting the wire.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

inductive NetworkCommand where
  | submit (payload : app.Payload)
  | replay (id : MessageId Principal)
  | wait

def NetworkCommand.toPlayerCommand : app.NetworkCommand → app.PlayerCommand
  | .submit payload => .submit payload
  | .replay id => .replay id
  | .wait => .wait

structure PlayerResponse where
  privateWork : List app.PrivateCommand
  network : app.NetworkCommand

/-- A response is selected from the actual received view and own recall. -/
abbrev ResponsePolicy := List app.PlayerEntry → app.View → FinDist app.PlayerResponse

def afterPrivateWork (who : Principal) :
    List app.PrivateCommand → app.PolicyExecution → app.PolicyExecution
  | [], execution => execution
  | command :: rest, execution =>
      afterPrivateWork who rest (app.afterPrivate execution who command)

/-- No scheduler or player policy is consulted inside a selected response. -/
def responseStep (who : Principal) (execution : app.PolicyExecution)
    (response : app.PlayerResponse) : FinDist app.PolicyExecution :=
  app.playerStep who (app.afterPrivateWork who response.privateWork execution)
    (response.network.toPlayerCommand app)

def invokeResponse (who : Principal) (policy : app.ResponsePolicy)
    (execution : app.PolicyExecution) : FinDist app.PolicyExecution :=
  (policy (execution.principalHistory who) (State.observe app execution.native who)).bind
    (app.responseStep who execution)

theorem responseStep_submit (who : Principal) (execution : app.PolicyExecution)
    (work : List app.PrivateCommand) (payload : app.Payload) :
    app.responseStep who execution ⟨work, .submit payload⟩ =
      FinDist.pure (app.afterSubmit (app.afterPrivateWork who work execution) who payload) :=
  app.playerStep_submit_eq _ _ _

/-- Private work preserves the transport state exactly. -/
theorem afterPrivateWork_transport (who : Principal) (work : List app.PrivateCommand)
    (execution : app.PolicyExecution) :
    (app.afterPrivateWork who work execution).native.pool = execution.native.pool ∧
    (app.afterPrivateWork who work execution).native.receipts = execution.native.receipts := by
  induction work generalizing execution with
  | nil => exact ⟨rfl, rfl⟩
  | cons command rest ih => exact ih (app.afterPrivate execution who command)

/-- Work stays private under the application's ordinary locality premise. -/
theorem afterPrivateWork_other_input (actor observer : Principal) (different : observer ≠ actor)
    (hprivate : ∀ state command,
      app.observePlayer (app.privateStep state actor command) observer =
        app.observePlayer state observer)
    (work : List app.PrivateCommand) (execution : app.PolicyExecution) :
    let next := app.afterPrivateWork actor work execution
    (next.principalHistory observer, State.observe app next.native observer) =
      (execution.principalHistory observer, State.observe app execution.native observer) := by
  dsimp only
  induction work generalizing execution with
  | nil => rfl
  | cons command rest ih =>
      rw [afterPrivateWork, ih]
      simp only [afterPrivate, ite_eq_right different, State.observe, hprivate]

/-- One response exposes no extra application information to other players.
Its pending packet can be delivered or included by later wire steps. -/
theorem responseStep_other_input (actor observer : Principal) (different : observer ≠ actor)
    (hprivate : ∀ state command,
      app.observePlayer (app.privateStep state actor command) observer =
        app.observePlayer state observer)
    (submit : ∀ state payload,
      app.observePlayer (app.submitStep state actor payload) observer =
        app.observePlayer state observer)
    (execution next : app.PolicyExecution) (response : app.PlayerResponse)
    (supported : next ∈ (app.responseStep actor execution response).support) :
    (next.principalHistory observer, State.observe app next.native observer) =
      (execution.principalHistory observer, State.observe app execution.native observer) := by
  exact (app.playerStep_other_input actor observer different hprivate submit
    _ next _ supported).trans
      (app.afterPrivateWork_other_input actor observer different hprivate
        response.privateWork execution)

theorem afterPrivateWork_native (who : Principal) (work : List app.PrivateCommand)
    (execution : app.PolicyExecution) :
    app.run (work.map (.privateCommand who)) execution.native =
      FinDist.pure (app.afterPrivateWork who work execution).native := by
  induction work generalizing execution with
  | nil => rfl
  | cons command rest ih =>
      simp only [List.map_cons, run_cons, step, FinDist.pure_bind]
      exact ih (app.afterPrivate execution who command)

/-- Every response still expands into the existing native actions. This
permits native safety invariants to be reused without scheduling those actions. -/
theorem responseStep_native_support (who : Principal) (execution next : app.PolicyExecution)
    (response : app.PlayerResponse)
    (supported : next ∈ (app.responseStep who execution response).support) :
    ∃ actions, next.native ∈ (app.run actions execution.native).support := by
  obtain ⟨suffix, _, member⟩ := app.playerStep_native_support who
    (app.afterPrivateWork who response.privateWork execution)
    (response.network.toPlayerCommand app) next supported
  refine ⟨response.privateWork.map (.privateCommand who) ++ suffix, ?_⟩
  rw [run_append, afterPrivateWork_native, FinDist.pure_bind]
  exact member

end Interaction.MessageApplication
