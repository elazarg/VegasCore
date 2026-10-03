/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedReference
import Vegas.Game.SourceServiceBindingSelectedAttemptLaw
import Vegas.Game.SourceServiceBindingSelectedClosedCompletion
import Vegas.Game.SourceServiceBindingProtectedAttempt
import Vegas.Game.SourceServiceBindingTimingMixture

/-! # The literal binding timing family through actual completion

The actual silent-reference prefix reaches the chosen input or earlier
completion. At a protected input the original commitment lottery joins the
same value-independent stopped public and foreign traffic. At a closed input
the literal family waits and the actual continuation publicly misses. Earlier
completion is likewise an actual public miss. The original before-response
input and the same prefix parameter remain in the joint law.

These are operational laws of the literal policy. Its closed-gate waiting is
not asserted to be a rational native continuation.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem selected_input_retained
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId) (selected : Nat)
    (input : (application setup leaks).Info) (present : input ≠ none) :
    (application setup leaks).PolicyInvariant players (fun current =>
      sourceServiceSelectedInput? setup leaks owner event selected (current.recall owner) =
        input) := by
  let app := application setup leaks
  constructor
  · intro current actor response recalled _chosen
    exact sourceServiceSelectedInput?_prefix owner event selected _ _
      (app.respond_recall_prefix current actor owner response) input recalled present
  · intro current next command recalled moved
    rw [app.environmentStep_recall current next command moved]
    exact recalled

/-- The actual completed family law separates a protected source draw from
closed-gate waiting and completion before the chosen input. Every branch uses
the same actual reference prefix; no input visit or inclusion chance is
supplied. The readout retains the original input and complete joint traffic. -/
theorem BindingSource.selected_family_completion_law
    {Parameter : Type} (parameter : Parameter)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (site : BindingSource setup profile event execution.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (slot : Fin (turns + 1))
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let app := application setup leaks
    let familyPlayers := Function.update players site.owner
      (sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot)
    let silentPlayers := Function.update players site.owner app.silentPolicy
    let completed := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let earlier := fun final : app.Execution => completed final ∨
      sourceServiceSelectedInput? setup leaks site.owner event slot.val (final.recall site.owner) ≠
        none
    let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
      ⟨.inr event, site.outputEq⟩
    let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
    ((app.runUntilHorizon scheduler familyPlayers completed horizon execution).map fun final =>
      (sourceServiceSelectedInput? setup leaks site.owner event slot.val (final.recall site.owner),
        parameter, output.get? final.application.config.store, traffic final)) =
    (app.runUntilHorizon scheduler silentPlayers earlier horizon execution).bind fun next =>
      if sourceServiceSelectedInput? setup leaks site.owner event slot.val
          (next.recall site.owner) = none then
        PMF.pure (none, parameter, some .failure, traffic next)
      else
        let before := { next with
          «recall» := Function.update next.recall site.owner (next.recall site.owner).dropLast }
        let input := some (before.recall site.owner, before.observe app site.owner)
        if before.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
          ((app.runUntilHorizon scheduler players completed horizon
            (before.respond app site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure
                (before.application.publicView.bindingCount site.owner)))).map traffic).bind
            fun chosen => (commitKernel site.residual (site.source.view site.owner)).map
              fun value => (input, parameter, some value, chosen)
        else
          (app.runUntilHorizon scheduler silentPlayers completed horizon
            (before.respond app site.owner ⟨none⟩)).map fun final =>
              (input, parameter, some .failure, traffic final) := by
  classical
  dsimp only
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile site.owner event turns slot
  let familyPlayers := Function.update players site.owner family
  let silentPlayers := Function.update players site.owner app.silentPolicy
  let completed := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let earlier := fun final : app.Execution => completed final ∨
    sourceServiceSelectedInput? setup leaks site.owner event slot.val (final.recall site.owner) ≠
      none
  let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
    ⟨.inr event, site.outputEq⟩
  let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
  have absent := sourceServiceSelectedInput?_of_untouched site.owner event slot.val execution
    (boundary.untouched event rfl)
  have stopLaw := sourceService_binding_selected_response_law scheduler players bound profile
    site.owner event turns slot (horizon - execution.environmentRecall.length) execution absent
  have ordered := app.runUntilHorizon_eq_runUntilHorizon_bind scheduler familyPlayers earlier
    completed (fun _ done => Or.inl done) horizon execution
  rw [ordered, PMF.map_bind]
  change (app.runUntil scheduler familyPlayers earlier
    (horizon - execution.environmentRecall.length) execution).bind _ = _
  rw [stopLaw, PMF.bind_bind]
  apply bind_congr_on_support
    (app.runUntilHorizon scheduler silentPlayers earlier horizon execution)
  intro next reached
  by_cases missing : sourceServiceSelectedInput? setup leaks site.owner event slot.val
      (next.recall site.owner) = none
  · simp only [missing, ↓reduceIte, PMF.pure_bind]
    have actual : next ∈ (app.runUntilHorizon scheduler familyPlayers earlier horizon
        execution).support := by
      change next ∈ (app.runUntil scheduler familyPlayers earlier
        (horizon - execution.environmentRecall.length) execution).support
      rw [stopLaw, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨next, reached, ?_⟩
      simp only [missing, ↓reduceIte, PMF.mem_support_pure_iff]
    have outcome := sourceService_binding_selected_stop contract players turns timing profile
      site.owner follows event site.payload site.outputEq slot execution boundary bounded next
        actual
    have missed : completed next ∧ output.get? next.application.config.store = some .failure := by
      rcases outcome with hit | missed
      · obtain ⟨_used, _before, _middle, _response, _within, _prior, _same, _raw, _chosen,
          _moved, _current, _absent, _unrecorded, _supported, _result, input⟩ := hit
        rw [missing] at input
        cases input
      · exact ⟨missed.1, missed.2.2.2.2.2⟩
    rw [ReactiveApplication.runUntilHorizon,
      app.runUntil_of_stop scheduler familyPlayers completed _ next missed.1, PMF.pure_map]
    simp only [missing]
    change PMF.pure (none, parameter, output.get? next.application.config.store, traffic next) = _
    rw [missed.2]
  · simp only [missing, ↓reduceIte, PMF.bind_map, Function.comp_def]
    let before : app.Execution := { next with
      «recall» := Function.update next.recall site.owner (next.recall site.owner).dropLast }
    obtain ⟨middle, recovered, ⟨raw⟩, same, _after, turn, selected, beforeAbsent, _atTurn, _slots,
      unrecorded, fresh, _noPacket, _input, responseLaw⟩ :=
      site.selected_reference_resources players turns timing
        profile event execution follows slot boundary bounded next reached missing
    change before = middle at recovered
    cases recovered
    let input : app.Info := some (before.recall site.owner, before.observe app site.owner)
    let currentSite : BindingSource setup profile event before.application.config :=
      ⟨site.Γ, site.names, site.name, site.owner, site.payload, site.fresh, site.guard, site.next,
        site.residual, site.refs, site.source, site.embedding, site.refsBefore, site.aligned,
        (by rw [same]; exact site.agree), (by rw [same]; exact site.history), site.head⟩
    have recalled (response : app.Action) :
        sourceServiceSelectedInput? setup leaks site.owner event slot.val
          ((before.respond app site.owner response).recall site.owner) = input := by
      rw [sourceServiceSelectedInput?_respond site.owner event slot.val before beforeAbsent
        response, ite_eq_left selected]
    have retained (response : app.Action) (final : app.Execution)
        (supported : final ∈ (app.runUntilHorizon scheduler familyPlayers completed horizon
          (before.respond app site.owner response)).support) :
        sourceServiceSelectedInput? setup leaks site.owner event slot.val
          (final.recall site.owner) = input := by
      obtain ⟨used, _within, actual, _length⟩ := app.runUntil_runRounds scheduler familyPlayers
        completed _ (before.respond app site.owner response) final supported
      exact (selected_input_retained familyPlayers site.owner event slot.val input
        (Option.some_ne_none _)).runRounds scheduler used _ final (recalled response) actual
    have familyLaw : family (before.recall site.owner) (before.observe app site.owner) =
        sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
          (before.recall site.owner) (before.observe app site.owner) := by
      exact app.turnScheduledPolicy_selected _ slot _ _ _ _ selected
    by_cases fits : before.application.publicView.InclusionFitsDeadline (runtime setup) bound event
    · rw [ite_eq_left fits]
      have actual := currentSite.selected_attempt_law contract players timing profile before event
        raw fresh turn unrecorded fits follows slot selected parameter
      have tagged := congrArg (fun law => law.map fun chosen =>
        (input, chosen.1, chosen.2.2.1, chosen.2.2.2)) actual
      calc
        _ = (family (before.recall site.owner) (before.observe app site.owner)).bind
            (fun response => (app.runUntilHorizon scheduler familyPlayers completed horizon
              (before.respond app site.owner response)).map fun final =>
                (input, parameter, output.get? final.application.config.store, traffic final)) := by
          rw [familyLaw]
          apply bind_congr_on_support _
          intro response _supported
          apply map_congr_on_support _
          intro final finalSupported
          rw [retained response final finalSupported]
        _ = (((app.runUntilHorizon scheduler players completed horizon
            (before.respond app site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure
                (before.application.publicView.bindingCount site.owner)))).map traffic).bind
              fun chosen => (commitKernel site.residual (site.source.view site.owner)).map
                fun value => (input, parameter,
                  some (if ((site.owner, before.network.nextSerial site.owner), true) ∈
                    chosen.2.1 then value else .failure), chosen)) := by
          simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using tagged
        _ = (((app.runUntilHorizon scheduler players completed horizon
            (before.respond app site.owner
              ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure
                (before.application.publicView.bindingCount site.owner)))).map traffic).bind
              fun chosen => (commitKernel site.residual (site.source.view site.owner)).map
                fun value => (input, parameter, some value, chosen)) := by
          apply bind_congr_on_support _
          intro chosen chosenSupported
          obtain ⟨final, finalSupported, rfl⟩ := PMF.support_map .. ▸ chosenSupported
          have accepted := currentSite.protected_attempt_completion contract players timing
            profile before event raw fresh turn unrecorded fits follows .failure final
              finalSupported
          have receipt : ((site.owner, before.network.nextSerial site.owner), true) ∈
              (traffic final).2.1 := accepted.2.1
          apply map_congr_on_support _
          intro value _supported
          rw [ite_eq_left receipt]
        _ = _ := by
          simp only [PMF.bind_map, Function.comp_def]
          rfl
    · rw [ite_eq_right fits]
      have silence : sourceServiceCanonicalOpportunity setup leaks bound profile site.owner event
          (before.recall site.owner) (before.observe app site.owner) = PMF.pure ⟨none⟩ := by
        rw [responseLaw, ite_eq_right fits]
      rw [silence, PMF.pure_bind,
        sourceService_binding_selected_continuation_silent scheduler players bound profile
          site.owner event turns slot before selected]
      apply map_congr_on_support _
      intro final finalSupported
      have familySupported : final ∈ (app.runUntilHorizon scheduler familyPlayers completed
          horizon (before.respond app site.owner ⟨none⟩)).support := by
        rw [sourceService_binding_selected_continuation_silent scheduler players bound profile
          site.owner event turns slot before selected]
        exact finalSupported
      have missed := sourceService_binding_selected_closed_completion contract players timing
        profile site.owner follows before raw event site.payload site.outputEq site.owned slot
          selected unrecorded fits final familySupported
      rw [retained ⟨none⟩ final familySupported, missed.2.2.1]

/-- The owner's actual timing policy at its untouched source boundary is the
original timing prior joined to the completed selected-family law. The joint
carrier retains the chosen timing slot and actual original input, while its
marginal is the actual typed output and public/foreign traffic law. -/
theorem BindingSource.timing_completion_law
    {Parameter : Type} (parameter : Parameter)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (site : BindingSource setup profile event execution.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let app := application setup leaks
    let completed := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let output : EventGraph.FieldRef (graph setup).layout (.binding site.owner site.payload) :=
      ⟨.inr event, site.outputEq⟩
    let traffic := (runtime setup).bindingPublicTraffic leaks site.owner
    let joint := (timing event site.owner site.owned).bind fun slot =>
      let silentPlayers := Function.update players site.owner app.silentPolicy
      (app.runUntilHorizon scheduler silentPlayers
        (fun final => completed final ∨ sourceServiceSelectedInput? setup leaks site.owner event
          slot.val (final.recall site.owner) ≠ none) horizon execution).bind fun next =>
        if sourceServiceSelectedInput? setup leaks site.owner event slot.val
            (next.recall site.owner) = none then
          PMF.pure (slot, none, parameter, some .failure, traffic next)
        else
          let before := { next with
            «recall» := Function.update next.recall site.owner (next.recall site.owner).dropLast }
          let input := some (before.recall site.owner, before.observe app site.owner)
          if before.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
            ((app.runUntilHorizon scheduler players completed horizon
              (before.respond app site.owner
                ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure
                  (before.application.publicView.bindingCount site.owner)))).map traffic).bind
              fun chosen => (commitKernel site.residual (site.source.view site.owner)).map
                fun value => (slot, input, parameter, some value, chosen)
          else
            (app.runUntilHorizon scheduler silentPlayers completed horizon
              (before.respond app site.owner ⟨none⟩)).map fun final =>
                (slot, input, parameter, some .failure, traffic final)
    ((app.runUntilHorizon scheduler players completed horizon execution).map fun final =>
      (parameter, output.get? final.application.config.store, traffic final)) =
      joint.map (fun chosen => (chosen.2.2.1, chosen.2.2.2.1, chosen.2.2.2.2)) := by
  classical
  dsimp only
  rw [sourceService_binding_timing_mixture parameter scheduler players bound turns timing profile
    site.owner follows event site.payload site.owned site.outputEq execution boundary horizon,
    PMF.map_bind]
  apply bind_congr_on_support (timing event site.owner site.owned)
  intro slot _chosen
  have actual := site.selected_family_completion_law parameter contract players turns timing
    profile event execution follows slot boundary bounded
  have marginal := congrArg (fun law => law.map fun chosen =>
    (chosen.2.1, chosen.2.2.1, chosen.2.2.2)) actual
  simp only [PMF.map_comp, Function.comp_def] at marginal
  rw [marginal]
  simp only [PMF.map_bind]
  apply bind_congr_on_support _
  intro next _reached
  by_cases missing : sourceServiceSelectedInput? setup leaks site.owner event slot.val
      (next.recall site.owner) = none
  · simp only [ite_eq_left missing, PMF.pure_map]
  · simp only [ite_eq_right missing]
    by_cases fits : next.application.publicView.InclusionFitsDeadline (runtime setup) bound event
    · simp only [ite_eq_left fits, PMF.map_bind, PMF.map_comp, Function.comp_def]
    · simp only [ite_eq_right fits, PMF.map_comp, Function.comp_def]

end Vegas
