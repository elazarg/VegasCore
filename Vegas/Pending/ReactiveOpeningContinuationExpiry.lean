/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningContinuation

/-! # Complete settlement from an intermediate opening window

The timing posterior couples the actual remaining execution to its source
disclosure result. The coupling retains the final ledger, receipts and serials,
so subsequent source phases can use their existing public checkpoint. Neither
the latent timing mode nor this proof coupling is an added runtime state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual continuation through the remaining visits, protected inclusion and
deadline expiry, jointly with its recall-conditioned timing mode. Every mode
has the exact source effect and public records, including off-path openings. -/
theorem openingWindowMixture_continuation_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (ready : initial.application.config.cut.Ready event)
    (serials : initial.network.SerialsBeforeNext)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (accepted : (runtime.reactiveApplication leaks).handle initial.application
      (runtime.windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial) =
        some (initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value))))
    (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ initial.application.clock + ticks - entered)
    (remaining : List Player) (complete : visits + remaining.count owner = slots)
    (network : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let family := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure (runtime.windowOpening leaks event candidate ⟨payload, value⟩))
        app.replayPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ selected ∈ posterior.support,
      runtime.OpeningWindowFrame leaks owner event candidate ⟨payload, value⟩
        offset selected visits initial current) →
    ∃ coupling : PMF (Option (Fin slots) × app.Execution),
      coupling.map Prod.fst = posterior ∧
      coupling.map Prod.snd = runtime.runInteractionPlan leaks
        (runtime.openingWindowMixturePlayers leaks owner event candidate ⟨payload, value⟩
          offset choices) network
        (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])) current ∧
      ∀ pair ∈ coupling.support,
        pair.2.application = (if pair.1.isSome then
          { initial.application.complete event ready
              (cast (congrArg EventField.Action outputEq.symm) true)
              (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value))
              with clock := initial.application.clock + ticks }
          else ({ initial.application with clock := initial.application.clock + ticks } :
              State graph)
            |>.complete event ready (cast (congrArg EventField.Action outputEq.symm) false)
              (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)) ∧
        pair.2.network.Satisfies (fun message =>
          message.id ∈ pair.2.network.ledger.map Message.id) ∧
        pair.2.network.ledger = (if pair.1.isSome then List.append initial.network.ledger
          [runtime.windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial]
          else initial.network.ledger) ∧
        pair.2.receipts = (if pair.1.isSome then initial.receipts ++
          [((owner, initial.network.nextSerial owner), true)] else initial.receipts) ∧
        pair.2.network.nextSerial = fun who => initial.network.nextSerial who +
          if who = owner ∧ pair.1.isSome then 1 else 0 := by
  intro app family posterior frames
  let plan := remaining.map ServiceInstruction.player ++
    (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
  let finish := fun selected : Option (Fin slots) => runtime.runInteractionPlan leaks
    (runtime.openingWindowPlayers leaks owner event candidate ⟨payload, value⟩ offset selected)
      network plan current
  let coupling := posterior.bind fun selected =>
    (finish selected).map fun final => (selected, final)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_bind, PMF.map_comp, Function.comp_def,
      PMF.map_const, PMF.bind_pure]
  · simp only [coupling, PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (posterior.bind fun selected => (finish selected).map id) = _
    simp only [PMF.map_id]
    exact (runtime.openingWindowMixture_continuation leaks owner event candidate ⟨payload, value⟩
      offset choices network plan current).symm
  · intro pair supported
    obtain ⟨selected, possible, mapped⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ mapped
    change final ∈ (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate ⟨payload, value⟩ offset selected)
        network plan current).support at reached
    rw [show plan = remaining.map ServiceInstruction.player ++
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]) from rfl,
      runtime.runInteractionPlan_append] at reached
    obtain ⟨before, prior, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    have frame := (frames selected possible).run runtime leaks owner event candidate
      ⟨payload, value⟩ offset selected visits initial current network remaining before prior
        owned (fun _ => valid)
    rw [complete] at frame
    exact frame.expiry runtime leaks owner event payload binding checks outputEq codeEq node
      candidate value initial before offset selected ready serials accepted entered ticks activated
        due _ network final reached

end Vegas.EventGraphRuntime
