/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningCoupling

/-! # Auxiliary transcript coupling through public deadline settlement

Clock ticks and expiry append their actual pre-command public views to service
recall. Their message transcript is determined by the initial public view and
the previous message transcript, even though private application states differ.
These readouts describe the existing interpreter; they add no runtime state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def applicationReadout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (view : PublicView graph) (command : EnvironmentCommand graph)
    (transcript : (runtime.reactiveApplication leaks).MessageReadout ×
      List (runtime.reactiveApplication leaks).PlayerEntry) :=
  let before := transcript.1
  let environment := before.2.2.1 ++
    [⟨⟨before.1.publicView, view, before.2.1⟩, .application command⟩]
  ((before.1, before.2.1, environment, before.2.2.2), transcript.2)

private def expiryReadout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) : PublicView graph → Nat →
      ((runtime.reactiveApplication leaks).MessageReadout ×
        List (runtime.reactiveApplication leaks).PlayerEntry) →
      ((runtime.reactiveApplication leaks).MessageReadout ×
        List (runtime.reactiveApplication leaks).PlayerEntry)
  | view, 0, transcript => applicationReadout runtime leaks view (.expire event) transcript
  | view, ticks + 1, transcript =>
      expiryReadout runtime leaks event { view with clock := view.clock + 1 } ticks
        (applicationReadout runtime leaks view .advanceClock transcript)

private theorem expiry_readout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (focal : Player)
    (ticks : Nat) (initial : (runtime.reactiveApplication leaks).Execution) :
    (runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]) initial).map
        (fun next => ((runtime.reactiveApplication leaks).messageView next, next.recall focal)) =
      PMF.pure (expiryReadout runtime leaks event initial.application.publicView ticks
        ((runtime.reactiveApplication leaks).messageView initial, initial.recall focal)) := by
  induction ticks generalizing initial with
  | zero =>
      simp only [List.replicate_zero, List.nil_append, runInteractionPlan, interactionStep,
        interactionInstruction, PMF.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume, PMF.bind_pure,
        ReactiveApplication.Execution.environmentStep, reactiveApplication,
        environmentStep, PMF.pure_map]
      rfl
  | succ ticks ih =>
      let app := runtime.reactiveApplication leaks
      let ticked : app.Execution := { initial with
        application := { initial.application with clock := initial.application.clock + 1 }
        environmentRecall := initial.environmentRecall ++
          [⟨initial.observeEnvironment app, .application .advanceClock⟩] }
      have step : runtime.interactionStep leaks players network .tick initial =
          PMF.pure ticked := by
        simp only [interactionStep, interactionInstruction, PMF.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
          ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
          reactiveApplication, environmentStep, PMF.pure_map]
        rfl
      rw [List.replicate_succ, List.cons_append, runInteractionPlan, step, PMF.pure_bind, ih]
      rfl

/-- Clock/expiry suffixes preserve equality of the full message readout and
focal recall whenever their starting public application views agree. -/
theorem expiry_transcript_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (leftPlayers rightPlayers : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (focal : Player)
    (ticks : Nat) (left right : (runtime.reactiveApplication leaks).Execution)
    (messages : (runtime.reactiveApplication leaks).messageView left =
      (runtime.reactiveApplication leaks).messageView right)
    (recall : left.recall focal = right.recall focal)
    (publicView : left.application.publicView = right.application.publicView) :
    (runtime.runInteractionPlan leaks leftPlayers network
      (List.replicate ticks .tick ++ [.expire event]) left).map
        (fun next => ((runtime.reactiveApplication leaks).messageView next, next.recall focal)) =
    (runtime.runInteractionPlan leaks rightPlayers network
      (List.replicate ticks .tick ++ [.expire event]) right).map
        (fun next => ((runtime.reactiveApplication leaks).messageView next,
          next.recall focal)) := by
  rw [expiry_readout, expiry_readout, messages, recall, publicView]

private theorem expiry_law_readout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (focal : Player)
    (ticks : Nat) (starts : PMF (runtime.reactiveApplication leaks).Execution)
    (view : PublicView graph)
    (publicView : ∀ state ∈ starts.support, state.application.publicView = view) :
    (starts.bind fun state => runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]) state).map
        (fun next => ((runtime.reactiveApplication leaks).messageView next, next.recall focal)) =
      (starts.map fun state => ((runtime.reactiveApplication leaks).messageView state,
        state.recall focal)).map (expiryReadout runtime leaks event view ticks) := by
  rw [PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro state supported
  rw [expiry_readout, publicView state supported]
  rfl

/-- The complete scheduled phase, including all ticks and expiry, preserves
the joint message transcript and focal recall. The post-inclusion public-view
premise compares actual application results; it cannot hide a different public
guard outcome. No premise identifies unrevealed commitment meanings. -/
theorem openingWindow_expiry_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (network : runtime.NetworkPolicy leaks) (focal : Player) (ticks : Nat)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (messages : (runtime.reactiveApplication leaks).messageView left =
      (runtime.reactiveApplication leaks).messageView right)
    (recall : left.recall focal = right.recall focal)
    (publicView : left.application.publicView = right.application.publicView)
    (privateView : (runtime.reactiveApplication leaks).observePlayer left.application focal =
      (runtime.reactiveApplication leaks).observePlayer right.application focal)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw)
    (accepted : selected.isSome →
      ((runtime.reactiveApplication leaks).handle left.application
        (runtime.windowEnvelope leaks owner event candidate raw left)).isSome = true ∧
      ((runtime.reactiveApplication leaks).handle right.application
        (runtime.windowEnvelope leaks owner event candidate raw right)).isSome = true)
    (publicAfter :
      (if selected.isSome then
        ((runtime.reactiveApplication leaks).handle left.application
          (runtime.windowEnvelope leaks owner event candidate raw left)).getD left.application
        else left.application).publicView =
      (if selected.isSome then
        ((runtime.reactiveApplication leaks).handle right.application
          (runtime.windowEnvelope leaks owner event candidate raw right)).getD right.application
        else right.application).publicView) :
    let app := runtime.reactiveApplication leaks
    let players := fun start : app.Execution =>
      runtime.openingWindowPlayers leaks owner event candidate raw
        (start.recall owner).length selected
    let plan := (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      (List.replicate ticks .tick ++ [.expire event])
    (runtime.runInteractionPlan leaks (players left) network plan left).map
        (fun next => (app.messageView next, next.recall focal)) =
      (runtime.runInteractionPlan leaks (players right) network plan right).map
        (fun next => (app.messageView next, next.recall focal)) := by
  dsimp only
  rw [runInteractionPlan_append (execution := left),
    runInteractionPlan_append (execution := right)]
  have postView (initial : (runtime.reactiveApplication leaks).Execution)
      (serials : initial.network.SerialsBeforeNext)
      (published : initial.network.Satisfies fun message =>
        message.id ∈ initial.network.ledger.map Message.id)
      (valid : selected.isSome → initial.application.candidates.lookup candidate = .openable raw)
      (final : (runtime.reactiveApplication leaks).Execution)
      (reached : final ∈ (runtime.runInteractionPlan leaks
        (runtime.openingWindowPlayers leaks owner event candidate raw (initial.recall owner).length
          selected) network (roster.map ServiceInstruction.player ++ [.includeLatest event owner])
            initial).support) :
      final.application.publicView = (if selected.isSome then
        ((runtime.reactiveApplication leaks).handle initial.application
          (runtime.windowEnvelope leaks owner event candidate raw initial)).getD initial.application
        else initial.application).publicView :=
    congrArg State.publicView (runtime.openingWindow_settlement leaks owner event candidate raw
      roster selected initial serials published owned valid network final reached).1
  rw [expiry_law_readout runtime leaks _ network event focal ticks _ _
      (postView left leftSerials leftPublished (fun h => (meaning h).1)),
    expiry_law_readout runtime leaks _ network event focal ticks _ _
      (postView right rightSerials rightPublished (fun h => (meaning h).2)), publicAfter]
  apply congrArg (PMF.map _)
  exact runtime.openingWindow_inclusion_coupling leaks owner event candidate raw roster selected
    network focal left right leftRecall rightRecall leftSerials rightSerials leftPublished
    rightPublished messages recall publicView privateView owned meaning accepted

end Vegas.EventGraphRuntime
