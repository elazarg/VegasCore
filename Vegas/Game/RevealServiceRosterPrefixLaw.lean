/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterLaw
import Vegas.Game.RevealServiceRosterPrefixSupport
import Vegas.Game.RevealServiceCorrespondence
import Vegas.Game.SourcePrefixKernel

/-! # Exact source laws through repeated activation phases

The single compiled physical policy implements every source prefix law through
the existing service interpreter. Each reveal's conditional timing and passive
traffic remain in the native execution, and all withholding choices remain.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem run_roster_source_prefix_option_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations []
        embedding refsBefore offset →
      ∀ (count : Nat), count ≤ eventCount program →
      ∀ execution, PublicCheckpoint setup leaks initial source refs offset execution →
      (∀ who, (execution.recall who).length =
        (((List.finRange (graph setup).order.eventCount).take offset).flatMap rosters).count who) →
      execution.network.Satisfies (fun message =>
        message.id ∈ execution.network.ledger.map Message.id) →
      execution.network.SerialsBeforeNext →
      ((runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing wholeProfile) network
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          rosterBlock setup rosters (embedding.event index)) execution).map
        (fun final => decodePrefix? program refs source.revelations embedding.ref count
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
          (FinDist.pure (ProtocolState.entry program source))).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile source refs embedding refsBefore offset _aligned count countBound
        execution checkpoint counts clean serials
      have zero : count = 0 := by simpa [eventCount] using countBound
      subst count
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
        FinDist.map_pure, Function.iterate_zero_apply]
      apply congrArg FinDist.pure
      rw [checkpoint.history]
      exact decodePrefix?_zero_of_agrees _ refs embedding.ref source checkpoint.emptyRegistry _
        checkpoint.agrees
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile source refs embedding refsBefore offset aligned count countBound
        execution checkpoint counts clean serials
      cases count with
      | zero =>
          simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
            FinDist.map_pure, Function.iterate_zero_apply]
          apply congrArg FinDist.pure
          rw [checkpoint.history]
          exact decodePrefix?_zero_of_agrees _ refs embedding.ref source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count =>
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have eventRank : event.val = offset := by
            simpa [event, index] using aligned.graphSuffix.rankEq index
          have actor : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs source.revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          obtain ⟨opportunity, activeCheckpoint, granted, grantRecall, grantNetwork, grantLaw⟩ :=
            checkpoint.grant (rosterPolicy setup leaks rosters timing wholeProfile) network event
          have ownerOffset : (opportunity.recall owner).length =
              rosterOffset setup rosters owner event := by
            rw [grantRecall, counts owner]
            simp only [rosterOffset, eventRank]
          obtain ⟨value, bound⟩ := activeCheckpoint.openable selected
          obtain ⟨candidate, associated, owned, valid, opening⟩ :=
            roster_opening_at_checkpoint setup leaks selected source.state refs opportunity
              activeCheckpoint.agrees activeCheckpoint.binding event outputEq codeEq node
                value bound
          have choiceLaw := sourceChoiceLaw_reveal setup leaks fresh selected unresolved next
            wholeProfile profile refs source embedding refsBefore offset aligned opportunity
              activeCheckpoint.agrees activeCheckpoint.history granted
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let resultRef : EventGraph.FieldRef (graphLayout setup.program) (.publication payload) :=
            ⟨.inr event, outputEq⟩
          let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                apply embedding.strictMono
                exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
            | there ref => exact refsBefore ref (Fin.succ remaining)
          have tailAligned := aligned.revealTail (whole := setup.program)
            (wholeProfile := wholeProfile) fresh selected unresolved next profile refs
            source.revelations [] embedding refsBefore offset
          let phase : List (ServiceInstruction (graph setup)) :=
            (rosters event).map ServiceInstruction.player ++
              ([.includeLatest event owner] ++
                List.replicate (event.val + 1) .tick ++ [.expire event])
          let remaining := ((List.finRange (eventCount next)).take count).flatMap fun tail =>
            rosterBlock setup rosters (tailEmbedding.event tail)
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
                (count + 1)).flatMap fun i => rosterBlock setup rosters (embedding.event i)) =
              [.grant event] ++ (phase ++ remaining) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            change rosterBlock setup rosters event ++ remaining = _
            rw [rosterBlock_of_owner setup rosters event owner actor]
            simp only [phase, List.append_assoc, List.cons_append, List.nil_append]
          have phaseForm : phase = ((rosters event).map ServiceInstruction.player ++
              [.includeLatest event owner]) ++ List.replicate (event.val + 1) .tick ++
                [.expire event] := by simp only [phase, List.append_assoc]
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            have embedded := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using embedded
          have finishSlot (slot : Option (Fin ((rosters event).count owner))) :
              (((runtime setup).runInteractionPlan leaks
                ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
                  (rosterOffset setup rosters owner event) slot) network phase opportunity).bind
                fun after => (runtime setup).runInteractionPlan leaks
                  (rosterPolicy setup leaks rosters timing wholeProfile)
                    network remaining after).map
                  (fun final => decodePrefix?
                    (.reveal published owner name fresh selected unresolved next) refs
                    source.revelations embedding.ref (count + 1) final.application.config.store
                    (decodeHistory setup.program (final.application.config.history.map
                      (setup.eventGraph.fromModeCompletion .sequential)))) =
              (((fun law => law.bind (ProtocolState.behavioralStateStep next
                (afterReveal profile)))^[count]
                  (FinDist.pure (ProtocolState.entry next
                    (revealSuccessor published selected source slot.isSome)))).map
                      (Sum.inr (α := Config Player L Γ))).map some := by
            rw [FinDist.map_bind]
            have constant (after : (application setup leaks).Execution)
                (reached : after ∈ ((runtime setup).runInteractionPlan leaks
                  ((runtime setup).openingWindowPlayers leaks owner event candidate ⟨payload, value⟩
                    (rosterOffset setup rosters owner event) slot) network phase
                      opportunity).support) :
                ((runtime setup).runInteractionPlan leaks
                  (rosterPolicy setup leaks rosters timing wholeProfile)
                    network remaining after).map
                    (fun final => decodePrefix?
                      (.reveal published owner name fresh selected unresolved next) refs
                      source.revelations embedding.ref (count + 1) final.application.config.store
                      (decodeHistory setup.program (final.application.config.history.map
                        (setup.eventGraph.fromModeCompletion .sequential)))) =
                  (((fun law => law.bind (ProtocolState.behavioralStateStep next
                    (afterReveal profile)))^[count]
                      (FinDist.pure (ProtocolState.entry next
                        (revealSuccessor published selected source slot.isSome)))).map
                          (Sum.inr (α := Config Player L Γ))).map some := by
              obtain ⟨afterCheckpoint, afterClean, _afterGrant⟩ :=
                activeCheckpoint.reveal_scheduled rosters network
                published selected event eventRank actor outputEq codeEq node
                  (fun ref => refsBefore ref index) decoded value bound candidate owned associated
                    valid ownerOffset (grantNetwork ▸ clean) (grantNetwork ▸ serials) slot after
                      (phaseForm ▸ reached)
              have afterCounts (who : Player) : (after.recall who).length =
                  (((List.finRange (graph setup).order.eventCount).take (offset + 1)).flatMap
                    rosters).count who := by
                have advanced := fixed_plan_response_counts setup leaks network _ phase
                  (by simp [phase]) opportunity after reached who
                have actors : phase.filterMap instructionActor = rosters event := by
                  simp [phase, instructionActor]
                rw [actors, grantRecall, counts who] at advanced
                have phases := congrArg
                  (fun instructions : List (ServiceInstruction (graph setup)) =>
                    (instructions.filterMap instructionActor).count who)
                      (rosterPlanPrefix_succ setup rosters event)
                rw [List.filterMap_append, List.count_append, rosterPlanPrefix_actors,
                  rosterPlanPrefix_actors, rosterBlock_actors, eventRank] at phases
                exact advanced.trans phases.symm
              have afterSerials := (runtime setup).runInteractionPlan_serials leaks _ network
                phase opportunity after (grantNetwork ▸ serials) reached
              have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs
                  (revealSuccessor published selected source slot.isSome).revelations
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
                  tailEmbedding, OutputEmbedding.ref] using tailAligned
              have nextBound : count ≤ eventCount next := by simpa [eventCount] using countBound
              have tailLaw := ih reveals (afterReveal profile)
                (revealSuccessor published selected source slot.isSome)
                tailRefs tailEmbedding tailBefore (offset + 1) nextAligned count nextBound after
                afterCheckpoint afterCounts afterClean afterSerials
              simp only [decodePrefix?_reveal]
              have lifted := congrArg (fun law : FinDist (Option (ProtocolState next)) =>
                law.map (Option.map (Sum.inr (α := Config Player L Γ)))) tailLaw
              simp only [FinDist.map_comp, Function.comp_def, Option.map_some] at lifted
              convert lifted using 1
              · rfl
              · simp only [FinDist.map_comp, Function.comp_def]
            exact (FinDist.bind_congr constant).trans (FinDist.bind_const _ _)
          rw [planEq, runInteractionPlan_append, grantLaw, FinDist.pure_bind,
            runInteractionPlan_append, rosterPolicy_phase_law setup leaks rosters timing
              wholeProfile opportunity event owner granted actor candidate ⟨payload, value⟩
                opening (Nat.le_of_eq ownerOffset) network (event.val + 1), choiceLaw,
                  FinDist.bind_bind, FinDist.map_bind,
                    ProtocolState.behavioralStatePrefix_reveal, FinDist.map_bind]
          apply FinDist.bind_congr
          intro disclose _
          cases disclose with
          | false =>
              simpa only [Bool.false_eq_true, ↓reduceIte, Option.isSome_none, phase]
                using finishSlot none
          | true =>
              simp only [↓reduceIte, FinDist.bind_bind, FinDist.map_bind]
              have branch := FinDist.bind_congr (μ := timing event owner actor)
                fun slot _ => finishSlot (some slot)
              simp only [Option.isSome_some, FinDist.bind_const, phase, FinDist.map_bind] at branch
              exact branch

/-- The actual roster compiler preserves every initialized source prefix law,
including correlated private inputs and source histories. No equilibrium or
full-support assumption enters this equation. -/
theorem roster_compiled_prefix_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (count : Nat) (within : count ≤ eventCount setup.program) :
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing (setup.decodeBehavioralProfile admission profile))
        network (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
          (fun final => sourcePrefix? setup count final.application.config) =
      ((setup.informationModel admission).runBehavioral profile (count + 1)).map
        GameTheory.Protocol.ExecutionProtocol.History.state := by
  let source := setup.decodeBehavioralProfile admission profile
  have permitted (who : Player) : (source who).Admitted setup.program admission :=
    ((setup.behavioralPolicyEquiv admission who).symm (profile who)).2
  have encoded : (fun who => setup.toProtocolBehavioralPolicy admission who
      (source who) (permitted who)) = profile :=
    funext fun who => (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  rw [← encoded, setup.encoded_prefix_state, encoded, initialLaw,
    FinDist.bind_map, FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial supported
  exact run_roster_source_prefix_option_law setup leaks rosters timing network source initial
    setup.program reveals source (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
      (CompiledPolicySuffix.whole setup.program source) count within
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
      (checkpoint_initial setup leaks reveals initial
        (openable initial supported)).toPublicCheckpoint
      (fun _ => rfl) MessageNetwork.Satisfies.empty MessageNetwork.SerialsBeforeNext.empty

end Vegas
