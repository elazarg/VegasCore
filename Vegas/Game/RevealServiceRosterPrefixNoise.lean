/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterGrantNoise
import Vegas.Game.RevealServiceRosterPrefixLaw
import GameTheoryExtensions.Math.Probability.Support

/-! # Conditional traffic laws across actual source prefixes

The induction uses the existing source program and native service interpreter.
Its joint finite law carries typed source configurations and complete native
executions only as proof data; no player receives an additional state component.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime


variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]


/-- A finite joint input law may already contain correlated traffic. Every
source prefix preserves its conditional independence given the focal source
view. The execution and all past native observations remain unmodified. -/
theorem run_roster_source_prefix_noise
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O),
      program.RevealOnly → ∀ (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      {Seed : Type} (prior : PMF Seed) (initial : Seed → State L setup.context)
      (source : Seed → Config Player L Γ)
      (execution : Seed → (application setup leaks).Execution),
      (∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
        (source seed).revelations [] embedding refsBefore offset) →
      (∀ seed, PublicCheckpoint setup leaks (initial seed) (source seed) refs offset
        (execution seed)) →
      (∀ seed who, ((execution seed).recall who).length =
        (((List.finRange (graph setup).order.eventCount).take offset).flatMap rosters).count who) →
      (∀ seed, (execution seed).network.Satisfies fun message =>
        message.id ∈ (execution seed).network.ledger.map Message.id) →
      (∀ seed, (execution seed).network.SerialsBeforeNext) →
      (∀ seed, (execution seed).InputRecall (application setup leaks)) →
      ∀ (grant : Option (graph setup).EventId),
      (∀ seed, (execution seed).application.serviceGrant = grant) →
      ∀ (noise : DecisionView focal Γ → PMF ((application setup leaks).MessageReadout ×
        List (application setup leaks).PlayerEntry)),
      prior.map (fun seed => (source seed,
        ((application setup leaks).messageView (execution seed), (execution seed).recall focal))) =
        (prior.map source).bind (fun config => (noise (config.view focal)).map fun extra =>
          (config, extra)) →
      ∀ count, count ≤ eventCount program →
      ∃ nextNoise : Option (ProtocolView focal program) →
          PMF ((application setup leaks).MessageReadout ×
            List (application setup leaks).PlayerEntry),
        let law := prior.bind fun seed =>
          ((runtime setup).runInteractionPlan leaks
            (rosterPolicy setup leaks rosters timing wholeProfile) network
            (((List.finRange (eventCount program)).take count).flatMap fun index =>
              rosterBlock setup rosters (embedding.event index)) (execution seed)).map
                fun final => (decodePrefix? program refs (source seed).revelations embedding.ref
                  count final.application.config.store (decodeHistory setup.program
                    (final.application.config.history.map
                      (setup.eventGraph.fromModeCompletion .sequential))),
                  ((application setup leaks).messageView final, final.recall focal))
        law = (law.map Prod.fst).bind fun state =>
          (nextNoise (state.map (ProtocolState.observe focal program))).map fun extra =>
            (state, extra) := by
  classical
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro _reveals profile refs embedding refsBefore offset Seed prior initial source execution
        _aligned checkpoint _counts _clean _serials _recalls grant _granted noise factor
        count within
      have zero : count = 0 := by simpa [eventCount] using within
      subst count
      obtain ⟨nextNoise, law⟩ := ProtocolView.entry_noise_factor (.ret payoffs) focal prior source
        (fun seed => ((application setup leaks).messageView (execution seed),
          (execution seed).recall focal)) noise factor
      refine ⟨nextNoise, ?_⟩
      dsimp only
      have decoded (seed : Seed) : decodePrefix? (.ret payoffs) refs (source seed).revelations
          embedding.ref 0 (execution seed).application.config.store
            (decodeHistory setup.program ((execution seed).application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential))) =
          some (ProtocolState.entry (.ret payoffs) (source seed)) := by
        rw [(checkpoint seed).history]
        exact decodePrefix?_zero_of_agrees _ refs embedding.ref (source seed)
          (checkpoint seed).emptyRegistry _ (checkpoint seed).agrees
      simpa only [List.take_zero, List.flatMap_nil, runInteractionPlan,
        PMF.pure_map, PMF.pure_bind, decoded, ← PMF.bind_pure_comp, Function.comp_def] using law
  | sample name fresh distribution next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ O published owner name payload fresh selected unresolved next ih =>
      intro reveals profile refs embedding refsBefore offset Seed prior initial source execution
        aligned checkpoint counts clean serials recalls grant granted noise factor count within
      cases count with
      | zero =>
          obtain ⟨nextNoise, law⟩ := ProtocolView.entry_noise_factor
            (.reveal published owner name fresh selected unresolved next) focal prior source
              (fun seed => ((application setup leaks).messageView (execution seed),
                (execution seed).recall focal)) noise factor
          refine ⟨nextNoise, ?_⟩
          dsimp only
          have decoded (seed : Seed) : decodePrefix?
              (.reveal published owner name fresh selected unresolved next) refs
              (source seed).revelations embedding.ref 0 (execution seed).application.config.store
                (decodeHistory setup.program ((execution seed).application.config.history.map
                  (setup.eventGraph.fromModeCompletion .sequential))) =
              some (ProtocolState.entry _ (source seed)) := by
            rw [(checkpoint seed).history]
            exact decodePrefix?_zero_of_agrees _ refs embedding.ref (source seed)
              (checkpoint seed).emptyRegistry _ (checkpoint seed).agrees
          simpa only [List.take_zero, List.flatMap_nil, runInteractionPlan,
            PMF.pure_map, PMF.pure_bind, decoded, ← PMF.bind_pure_comp, Function.comp_def]
            using law
      | succ count =>
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have eventRank : event.val = offset := by
            simpa [event, index] using
              (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
          have actor : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using
              (aligned prior.support_nonempty.choose).actorEq index
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs
              (source prior.support_nonempty.choose).revelations embedding refsBefore offset
                (aligned prior.support_nonempty.choose).graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          let players := rosterPolicy setup leaks rosters timing wholeProfile
          let opportunity := fun seed => ((checkpoint seed).grant players network event).choose
          have opportunityFacts (seed : Seed) :=
            ((checkpoint seed).grant players network event).choose_spec
          have grantLaw (seed : Seed) :
              (runtime setup).runInteractionPlan leaks players network [.grant event]
                (execution seed) = PMF.pure (opportunity seed) :=
            (opportunityFacts seed).2.2.2.2
          have opportunityNetwork (seed : Seed) :
              (opportunity seed).network = (execution seed).network :=
            (opportunityFacts seed).2.2.2.1
          let value := fun seed => (checkpoint seed).openable selected |>.choose
          have openable (seed : Seed) : (source seed).state.get selected = .success (value seed) :=
            ((checkpoint seed).openable selected).choose_spec
          let candidate := fun seed => (roster_opening_at_checkpoint setup leaks selected
            (source seed).state refs (opportunity seed) (opportunityFacts seed).1.agrees
              (opportunityFacts seed).1.binding event outputEq codeEq node
                (value seed) (openable seed)).choose
          have candidateFacts (seed : Seed) := (roster_opening_at_checkpoint setup leaks selected
            (source seed).state refs (opportunity seed) (opportunityFacts seed).1.agrees
              (opportunityFacts seed).1.binding event outputEq codeEq node
                (value seed) (openable seed)).choose_spec
          have ownerOffset (seed : Seed) : ((opportunity seed).recall owner).length =
              rosterOffset setup rosters owner event := by
            rw [(opportunityFacts seed).2.2.1, counts seed owner]
            simp only [rosterOffset, eventRank]
          obtain ⟨grantNoise, grantFactor⟩ := roster_grant_observation_kernel setup leaks refs
            offset prior initial source execution (fun seed _ => checkpoint seed) event focal
              players network grant (fun seed _ => granted seed) noise factor
          simp only [grantLaw, PMF.pure_bind, ← PMF.bind_pure_comp, Function.comp_def]
            at grantFactor
          have opportunityRecall (seed : Seed) :
              (opportunity seed).InputRecall (application setup leaks) :=
            (runtime setup).runInteractionPlan_inputRecall leaks players network [.grant event]
              (execution seed)
              (opportunity seed) (recalls seed) (by
                rw [(opportunityFacts seed).2.2.2.2]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
          obtain ⟨nextNoise, nextFactor⟩ := roster_successor_observation_kernel setup leaks
            published selected refs offset event eventRank actor outputEq codeEq node prior initial
            source opportunity (fun seed _ => (opportunityFacts seed).1) value
              (fun seed _ => openable seed) candidate (fun seed _ => (candidateFacts seed).2.1)
              (fun seed _ => (candidateFacts seed).1) (fun seed _ => (candidateFacts seed).2.2.1)
              (fun seed _ => opportunityRecall seed)
              (fun seed _ => (opportunityFacts seed).2.2.2.1 ▸ serials seed)
              (fun seed _ => (opportunityFacts seed).2.2.2.1 ▸ clean seed)
              (fun seed _ => (opportunityFacts seed).2.1) (rosters event)
              (timing event owner actor) network focal grantNoise grantFactor
              (fun config => revealKernel profile (config.view owner))
          let phase : List (ServiceInstruction (graph setup)) :=
            ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner])
            ++ List.replicate (event.val + 1) .tick ++ [.expire event]
          let branch := fun seed (slot : Option (Fin ((rosters event).count owner))) =>
            (runtime setup).runInteractionPlan leaks
              ((runtime setup).openingWindowPlayers leaks owner event (candidate seed)
                ⟨payload, value seed⟩ (rosterOffset setup rosters owner event) slot)
              network phase (opportunity seed)
          let conditional := fun seed (disclose : Bool) =>
            if disclose then (timing event owner actor).bind fun slot => branch seed (some slot)
            else branch seed none
          let advanced := prior.bind fun seed =>
            (revealKernel profile ((source seed).view owner)).bind fun disclose =>
              (conditional seed disclose).map fun after => (seed, disclose, after)
          let NextSeed := {point : Seed × Bool × (application setup leaks).Execution //
            point ∈ advanced.support}
          let nextPrior : PMF NextSeed := pmfToSubtype advanced (fun _ member => member)
          let nextInitial := fun point : NextSeed => initial point.val.1
          let nextSource := fun point : NextSeed =>
            revealSuccessor published selected (source point.val.1) point.val.2.1
          let nextExecution := fun point : NextSeed => point.val.2.2
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let resultRef : EventGraph.FieldRef (graphLayout setup.program) (.publication payload) :=
            ⟨.inr event, outputEq⟩
          let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref (Fin.succ remaining)
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            simpa [event, index, outputEq, decodeEventAction] using
              (aligned prior.support_nonempty.choose).actionEq index
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          have nextSupported (point : NextSeed) :
              ∃ slot : Option (Fin ((rosters event).count owner)),
                slot.isSome = point.val.2.1 ∧
                  point.val.2.2 ∈ (branch point.val.1 slot).support := by
            rcases point with ⟨point, member⟩
            change ∃ slot, slot.isSome = point.2.1 ∧ point.2.2 ∈ (branch point.1 slot).support
            change point ∈ (prior.bind fun seed =>
              (revealKernel profile ((source seed).view owner)).bind fun disclose =>
                (conditional seed disclose).map fun after => (seed, disclose, after)).support
              at member
            rw [PMF.support_bind] at member
            obtain ⟨seed, _, moved⟩ := Set.mem_iUnion₂.mp member
            obtain ⟨disclose, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
            obtain ⟨after, moved, equal⟩ := PMF.support_map .. ▸ moved
            have equal' : (seed, disclose, after) = point := equal
            cases disclose with
            | false => exact ⟨none, congrArg (fun value => value.2.1) equal', by
                simpa only [← equal', conditional, Bool.false_eq_true, ↓reduceIte] using moved⟩
            | true =>
                simp only [conditional, ↓reduceIte] at moved
                obtain ⟨slot, _, moved⟩ :=
                  Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
                exact ⟨some slot, congrArg (fun value => value.2.1) equal', by
                  simpa only [← equal'] using moved⟩
          have nextFacts (point : NextSeed) : PublicCheckpoint setup leaks
              (nextInitial point) (nextSource point) tailRefs (offset + 1) (nextExecution point) ∧
              (nextExecution point).network.Satisfies (fun message =>
                message.id ∈ (nextExecution point).network.ledger.map Message.id) ∧
              (nextExecution point).application.serviceGrant = some event := by
            obtain ⟨slot, disclosure, reached⟩ := nextSupported point
            have result := (opportunityFacts point.val.1).1.reveal_scheduled rosters network
              published selected event eventRank actor outputEq codeEq node
              (fun ref => refsBefore ref index) decoded (value point.val.1) (openable point.val.1)
              (candidate point.val.1) (candidateFacts point.val.1).2.1
              (candidateFacts point.val.1).1 (candidateFacts point.val.1).2.2.1
              (ownerOffset point.val.1) (by rw [opportunityNetwork]; exact clean point.val.1)
              (by rw [opportunityNetwork]; exact serials point.val.1) slot point.val.2.2 reached
            exact ⟨by simpa only [disclosure] using result.1, result.2.1,
              result.2.2.trans (opportunityFacts point.val.1).2.1⟩
          have nextCounts (point : NextSeed) (who : Player) :
              ((nextExecution point).recall who).length =
                (((List.finRange (graph setup).order.eventCount).take (offset + 1)).flatMap
                  rosters).count who := by
            obtain ⟨slot, _disclosure, reached⟩ := nextSupported point
            have counted := fixed_plan_response_counts setup leaks network _ phase
              (by simp [phase]) (opportunity point.val.1) point.val.2.2 reached who
            have actors : phase.filterMap instructionActor = rosters event := by
              simp [phase, instructionActor]
            rw [actors, (opportunityFacts point.val.1).2.2.1, counts point.val.1 who] at counted
            have phases := congrArg
              (fun instructions : List (ServiceInstruction (graph setup)) =>
                (instructions.filterMap instructionActor).count who)
                  (rosterPlanPrefix_succ setup rosters event)
            rw [List.filterMap_append, List.count_append, rosterPlanPrefix_actors,
              rosterPlanPrefix_actors, rosterBlock_actors, eventRank] at phases
            exact counted.trans phases.symm
          have nextSerials (point : NextSeed) :
              (nextExecution point).network.SerialsBeforeNext := by
            obtain ⟨slot, _disclosure, reached⟩ := nextSupported point
            exact (runtime setup).runInteractionPlan_serials leaks _ network phase
              (opportunity point.val.1) point.val.2.2 (by
                rw [opportunityNetwork]; exact serials point.val.1) reached
          have nextRecalls (point : NextSeed) :
              (nextExecution point).InputRecall (application setup leaks) := by
            obtain ⟨slot, _disclosure, reached⟩ := nextSupported point
            exact (runtime setup).runInteractionPlan_inputRecall leaks _ network phase
              (opportunity point.val.1)
              point.val.2.2 (opportunityRecall point.val.1) reached
          have nextAligned (point : NextSeed) : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs (nextSource point).revelations [] tailEmbedding
                tailBefore (offset + 1) := by
            simpa only [nextSource, tailRefs, resultRef, tailEmbedding, Registry.weaken,
              List.map_nil, revealSuccessor, OutputEmbedding.ref] using
              (aligned point.val.1).revealTail (whole := setup.program)
                (wholeProfile := wholeProfile) fresh selected unresolved next profile refs
                  (source point.val.1).revelations [] embedding refsBefore offset
          have conditionalRead (seed : Seed) (disclose : Bool) :
              (conditional seed disclose).map (fun final =>
                ((application setup leaks).messageView final, final.recall focal)) =
              rosterDisclosureTranscript setup leaks owner event (candidate seed)
                ⟨payload, value seed⟩ (rosters event) (timing event owner actor) network focal
                  (opportunity seed) disclose := by
            cases disclose <;> simp only [conditional, rosterDisclosureTranscript,
              Bool.false_eq_true, ↓reduceIte, PMF.map_bind, branch, ownerOffset, phase,
              List.append_assoc]
          have advancedFactor : nextPrior.map (fun point => (nextSource point,
              ((application setup leaks).messageView (nextExecution point),
                (nextExecution point).recall focal))) =
              (nextPrior.map nextSource).bind fun config =>
                (nextNoise (config.view focal)).map fun extra => (config, extra) := by
            simp only [nextPrior, nextSource, nextExecution]
            rw [map_pmfToSubtype advanced (fun _ member => member)
              (fun point => (revealSuccessor published selected (source point.1) point.2.1,
                ((application setup leaks).messageView point.2.2, point.2.2.recall focal))),
              map_pmfToSubtype advanced (fun _ member => member)
                (fun point => revealSuccessor published selected (source point.1) point.2.1)]
            have sourceLaw : advanced.map (fun point =>
                revealSuccessor published selected (source point.1) point.2.1) =
                (prior.map source).bind (fun config =>
                  (revealKernel profile (config.view owner)).map
                    (revealSuccessor published selected config)) := by
              simp only [advanced, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
                PMF.pure_bind, PMF.bind_const]
            rw [sourceLaw]
            rw [← nextFactor]
            simp only [advanced, PMF.map_bind, PMF.map_comp, Function.comp_def]
            apply bind_congr_on_support _
            intro seed _
            apply bind_congr_on_support _
            intro disclose _
            have mapped := congrArg (fun law => law.map fun extra =>
              (revealSuccessor published selected (source seed) disclose, extra))
                (conditionalRead seed disclose)
            simpa only [PMF.map_comp, Function.comp_def] using mapped
          obtain ⟨tailNoise, tailLaw⟩ := ih reveals (afterReveal profile) tailRefs tailEmbedding
            tailBefore (offset + 1) nextPrior nextInitial nextSource nextExecution nextAligned
            (fun point => (nextFacts point).1) nextCounts (fun point => (nextFacts point).2.1)
            nextSerials nextRecalls (some event) (fun point => (nextFacts point).2.2)
            nextNoise advancedFactor count (by simpa [eventCount] using within)
          let remaining := ((List.finRange (eventCount next)).take count).flatMap fun tail =>
            rosterBlock setup rosters (tailEmbedding.event tail)
          let tailJoint := nextPrior.bind fun point =>
            ((runtime setup).runInteractionPlan leaks players network remaining
              (nextExecution point)).map fun final =>
                (decodePrefix? next tailRefs (nextSource point).revelations tailEmbedding.ref count
                  final.application.config.store (decodeHistory setup.program
                    (final.application.config.history.map
                      (setup.eventGraph.fromModeCompletion .sequential))),
                  ((application setup leaks).messageView final, final.recall focal))
          have tailFactor : tailJoint = (tailJoint.map Prod.fst).bind fun state =>
              (tailNoise (state.map (ProtocolState.observe focal next))).map fun extra =>
                (state, extra) := tailLaw
          let embed : Option (ProtocolState next) →
              Option (Config Player L Γ ⊕ ProtocolState next) :=
            Option.map Sum.inr
          let recover := fun view : Option (ProtocolView focal
              (.reveal published owner name fresh selected unresolved next)) =>
            view.bind (Sum.elim (fun _ => none) some)
          have recovered (state : Option (ProtocolState next)) :
              recover ((embed state).map (ProtocolState.observe focal
                (.reveal published owner name fresh selected unresolved next))) =
                state.map (ProtocolState.observe focal next) := by
            cases state <;> rfl
          have lifted := PMF.map_observation_factor tailJoint
            (Option.map (ProtocolState.observe focal next))
            tailNoise tailFactor embed (Option.map (ProtocolState.observe focal
              (.reveal published owner name fresh selected unresolved next))) recover recovered
          refine ⟨fun view => tailNoise (recover view), ?_⟩
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
                (count + 1)).flatMap fun i => rosterBlock setup rosters (embedding.event i)) =
              [.grant event] ++ (phase ++ remaining) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            change rosterBlock setup rosters event ++ remaining = _
            rw [rosterBlock_of_owner setup rosters event owner actor]
            simp only [phase, List.append_assoc, List.cons_append, List.nil_append]
          have jointEq : (prior.bind fun seed =>
              ((runtime setup).runInteractionPlan leaks players network
                ([.grant event] ++ (phase ++ remaining)) (execution seed)).map fun final =>
                  (decodePrefix? (.reveal published owner name fresh selected unresolved next)
                    refs (source seed).revelations embedding.ref (count + 1)
                    final.application.config.store (decodeHistory setup.program
                      (final.application.config.history.map
                        (setup.eventGraph.fromModeCompletion .sequential))),
                    ((application setup leaks).messageView final, final.recall focal))) =
              tailJoint.map (fun pair => (embed pair.1, pair.2)) := by
            simp only [tailJoint, PMF.map_bind, PMF.map_comp, Function.comp_def,
              nextExecution, nextSource]
            let continuePoint := fun point : Seed × Bool × (application setup leaks).Execution =>
              ((runtime setup).runInteractionPlan leaks players network remaining point.2.2).map
                fun final => (embed (decodePrefix? next tailRefs
                  (revealSuccessor published selected (source point.1) point.2.1).revelations
                  tailEmbedding.ref count final.application.config.store
                  (decodeHistory setup.program (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential)))),
                  ((application setup leaks).messageView final, final.recall focal))
            change _ = nextPrior.bind (fun point => continuePoint point.val)
            rw [show (nextPrior.bind fun point => continuePoint point.val) =
                (nextPrior.map Subtype.val).bind continuePoint from
              (PMF.bind_map nextPrior Subtype.val continuePoint).symm]
            change _ = ((pmfToSubtype advanced _).map Subtype.val).bind continuePoint
            rw [map_val_pmfToSubtype]
            simp only [advanced, PMF.bind_bind, PMF.bind_map, continuePoint]
            apply bind_congr_on_support _
            intro seed _
            have phaseLaw := rosterPolicy_phase_law setup leaks rosters timing wholeProfile
              (opportunity seed) event owner (opportunityFacts seed).2.1 actor (candidate seed)
              ⟨payload, value seed⟩ (candidateFacts seed).2.2.2 (Nat.le_of_eq (ownerOffset seed))
              network (event.val + 1)
            have choiceLaw := sourceChoiceLaw_reveal setup leaks fresh selected unresolved next
              wholeProfile profile refs (source seed) embedding refsBefore offset (aligned seed)
              (opportunity seed) (opportunityFacts seed).1.agrees
                (opportunityFacts seed).1.history (opportunityFacts seed).2.1
            rw [runInteractionPlan_append, grantLaw, PMF.pure_bind, runInteractionPlan_append]
            change (((runtime setup).runInteractionPlan leaks players network phase
              (opportunity seed)).bind _).map _ = _
            have branchLaw : (runtime setup).runInteractionPlan leaks players network phase
                (opportunity seed) =
                (revealKernel profile ((source seed).view owner)).bind (conditional seed) := by
              simpa only [List.append_assoc, phase, conditional, branch, choiceLaw] using phaseLaw
            rw [branchLaw, PMF.bind_bind, PMF.map_bind]
            apply bind_congr_on_support _
            intro disclose _
            rw [PMF.map_bind]
            apply bind_congr_on_support _
            intro after _
            apply map_congr_on_support _
            intro final _
            simp only [decodePrefix?_reveal, embed, tailRefs, resultRef, tailEmbedding,
              revealSuccessor, OutputEmbedding.ref]
            rfl
          dsimp only
          rw [planEq, jointEq]
          exact lifted

/-- At every initialized completed phase, the entire network transcript and
the focal player's complete native recall reveal no additional source state
beyond that player's current source view. The auxiliary law is constructed
from the concrete runtime, rather than supplied as a preservation premise. -/
theorem roster_compiled_prefix_noise
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program) (focal : Player)
    (count : Nat) (within : count ≤ eventCount setup.program) :
    ∃ noise : Option (ProtocolView focal setup.program) →
        PMF ((application setup leaks).MessageReadout ×
          List (application setup leaks).PlayerEntry),
      let executions := (initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
          network (rosterPlanPrefix setup rosters count)
          (ReactiveApplication.Execution.initial (application setup leaks) state)
      executions.map (fun final => (sourcePrefix? setup count final.application.config,
          ((application setup leaks).messageView final, final.recall focal))) =
        (executions.map fun final => sourcePrefix? setup count final.application.config).bind
          fun state => (noise (state.map (ProtocolState.observe focal setup.program))).map
            fun extra => (state, extra) := by
  let Seed := {initial // initial ∈ setup.initialLaw.support}
  let prior : PMF Seed := pmfToSubtype setup.initialLaw (fun _ member => member)
  let source := fun seed : Seed => setup.initialConfig seed.val
  let execution := fun seed : Seed => ReactiveApplication.Execution.initial
    (application setup leaks) (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs seed.val))
  let emptyExtra :=
    ((application setup leaks).messageView (execution prior.support_nonempty.choose),
      (execution prior.support_nonempty.choose).recall focal)
  have initialFactor : prior.map (fun seed => (source seed,
      ((application setup leaks).messageView (execution seed), (execution seed).recall focal))) =
      (prior.map source).bind fun config => (PMF.pure emptyExtra).map fun extra =>
        (config, extra) := by
    simp only [PMF.pure_map, PMF.bind_map]
    rfl
  obtain ⟨noise, factor⟩ := run_roster_source_prefix_noise setup leaks rosters timing network
    profile focal setup.program reveals profile
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0 prior Subtype.val source
    execution (fun _ => CompiledPolicySuffix.whole setup.program profile)
    (fun seed => (checkpoint_initial setup leaks reveals seed.val
      (openable seed.val seed.property)).toPublicCheckpoint) (fun _ _ => rfl)
    (fun _ => MessageNetwork.Satisfies.empty) (fun _ => MessageNetwork.SerialsBeforeNext.empty)
    (fun _ => (application setup leaks).initial_inputRecall _) none (fun _ => rfl)
    (fun _ => PMF.pure emptyExtra) initialFactor count within
  refine ⟨noise, ?_⟩
  let combined := fun initial : State L setup.context =>
    ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (rosterPlanPrefix setup rosters count)
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))).map
      fun final => (sourcePrefix? setup count final.application.config,
        ((application setup leaks).messageView final, final.recall focal))
  have joint : prior.bind (fun seed => combined seed.val) = setup.initialLaw.bind combined := by
    refine (PMF.bind_map prior Subtype.val combined).symm.trans ?_
    exact congrArg (fun law => law.bind combined) (map_val_pmfToSubtype _ _)
  change (prior.bind fun seed => combined seed.val) =
    ((prior.bind fun seed => combined seed.val).map Prod.fst).bind fun state =>
      (noise (state.map (ProtocolState.observe focal setup.program))).map fun extra =>
        (state, extra) at factor
  rw [joint] at factor
  dsimp only
  simpa only [initialLaw, PMF.bind_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, combined] using factor

end Vegas
