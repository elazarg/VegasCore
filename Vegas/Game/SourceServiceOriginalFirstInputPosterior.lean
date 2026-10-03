/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOriginalFirstInput
import Vegas.Game.ServiceInformation
import GameTheory.Math.Probability.ConditionalObservation

/-! # Conditional original source laws at actual first owner inputs

The real first owner input recovers the compressed original source view from
its authentic typed observation. Conditioning the common original carrier on
that input therefore conditions the true original prefix law on the compressed
view. Original private intentions and physical native recall remain distinct.
Only supported inputs under the exact normalized first-turn policy are used.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def entryObservation (who : Player) :
    {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → DecisionView who Γ → ProtocolView who program
  | _, _, .ret _, view => view
  | _, _, .sample _ _ _ _, view => Sum.inl view
  | _, _, .commit _ _ _ _ _, view => Sum.inl view
  | _, _, .reveal _ _ _ _ _ _ _, view => Sum.inl view

omit [Fintype Player] in
private theorem entryObservation_observe {Γ : SourceCtx Player L} {names : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ names) (source : Config Player L Γ) :
    entryObservation who program (source.view who) =
      ProtocolState.observe who program (ProtocolState.entry program source) := by
  cases program <;> rfl

private theorem first_input_recovers
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let players := sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) normalized
    ∃ recover : (application setup leaks).Info → Option (ProtocolView owner setup.program),
      ∀ initial ∈ setup.initialLaw.support,
        ∀ execution ∈ ((application setup leaks).runUntilHorizon scheduler players
          (sourceServiceRankCompleted event.val) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support,
          ∀ original ∈ (sourceServiceOriginalPrefixCarrier profile initial event.val
            execution).support,
            ∀ final ∈ ((application setup leaks).runUntilHorizon scheduler players
              (fun final => sourceServiceTurnInput? setup leaks owner event
                (final.recall owner) ≠ none) horizon execution).support,
              recover (sourceServiceTurnInput? setup leaks owner event (final.recall owner)) =
                some (ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
                  (ProtocolState.observe owner setup.program original)) := by
  classical
  intro normalized players
  let app := application setup leaks
  have effective (who : Player) : (normalized who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
    (profile who).normalizeDisclosureFrom_effective setup.program []
      (Revelations.initial setup.context) (fun view => PMF.pure view.2)
  have rankWithin : event.val ≤ (graph setup).order.eventCount := Nat.le_of_lt event.isLt
  obtain ⟨Γ, names, tail, tailProfile, refs, registry, revelations, embedding, refsBefore,
    lift, liftView, _recoverView, _counted, _aligned, _tailEffective, _injective, viewed,
    _recovered, _commutes, _transport, endpoints⟩ :=
      sourceServiceFirstTurn_shared_checkpoint (turns := turns) contract timely normalized
        effective event.val rankWithin
  let recover := fun input : app.Info => input.bind fun played =>
    (decisionView? setup leaks refs owner played.2).map
      (fun view => liftView owner (entryObservation owner tail view))
  refine ⟨recover, ?_⟩
  intro initial initialSupport execution reached original restored final finalSupport
  obtain ⟨bounded, boundary, source, _registryEq, _revelationsEq, _decodedState,
    checkpoint, decoded⟩ := endpoints initial initialSupport execution reached
  obtain ⟨middle, response, _actual, configEq, _first, _fits, _chosen, _after, inputEq⟩ :=
    sourceServiceFirstActivation_input contract timely players owner turns normalized rfl
      event owned execution boundary bounded final finalSupport
  have read := decisionView?_observe setup leaks refs owner source middle
    (by rw [configEq]; exact checkpoint.agrees) (by rw [configEq]; exact checkpoint.history)
  have retract := sourceServiceFirstTurn_original_prefix_retracts (turns := turns) contract
    timely profile initial initialSupport event.val rankWithin execution reached original restored
  rw [decoded, Option.some.injEq] at retract
  have originalView := ProtocolState.observe_normalizeDisclosureProfileRecall setup.program
    owner original
  rw [retract, viewed] at originalView
  change recover (sourceServiceTurnInput? setup leaks owner event (final.recall owner)) = _
  rw [inputEq]
  simp only [recover, Option.bind_some, read, Option.map_some, entryObservation_observe]
  exact congrArg some originalView

/-- One actual physical first-input fiber has the conditional true original
source-prefix law, retaining the same initial parameter. Recovery is derived
from the initialized compiler checkpoint and real pre-response observation;
the posterior conditions on compressed source recall, not original intentions. -/
theorem sourceServiceFirstTurn_original_first_input_posterior {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (parameter : State L setup.context → Parameter)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    let originalLaw := setup.initialLaw.bind fun initial =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[event.val]
        (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
          fun original => (parameter initial, original)
    let observe := fun carried : Parameter × ProtocolState setup.program =>
      ProtocolView.normalizeDisclosureRecall setup.program (fun view => view.2)
        (ProtocolState.observe owner setup.program carried.2)
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) profile
    let players := sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) normalized
    let joint := setup.initialLaw.bind fun initial =>
      ((application setup leaks).runUntilHorizon scheduler players
        (sourceServiceRankCompleted event.val) horizon
        (.initial (application setup leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind fun execution =>
            (sourceServiceOriginalPrefixCarrier profile initial event.val execution).bind
              fun original =>
                ((application setup leaks).runUntilHorizon scheduler players
                  (fun final => sourceServiceTurnInput? setup leaks owner event
                    (final.recall owner) ≠ none) horizon execution).map fun final =>
                      ((parameter initial, original),
                        sourceServiceTurnInput? setup leaks owner event (final.recall owner))
    ∃ recover : (application setup leaks).Info → Option (ProtocolView owner setup.program),
      (∀ selected ∈ joint.support, recover selected.2 = some (observe selected.1)) ∧
      ∀ input ∈ (joint.map Prod.snd).support,
        ∃ view, recover input = some view ∧
          (fiberPosterior joint Prod.snd input).map Prod.fst =
            fiberPosterior originalLaw observe view := by
  classical
  intro originalLaw observe normalized players joint
  obtain ⟨recover, recovery⟩ := first_input_recovers (turns := turns) contract timely profile
    owner event owned
  have recovers selected (supported : selected ∈ joint.support) :
      recover selected.2 = some (observe selected.1) := by
    obtain ⟨initial, initialSupport, supported⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨execution, reached, supported⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨original, restored, supported⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨final, finalSupport, rfl⟩ := PMF.support_map .. ▸ supported
    exact recovery initial initialSupport execution reached original restored final finalSupport
  obtain ⟨channel, law, _total⟩ := sourceServiceFirstTurn_original_first_input_law
    (turns := turns) contract timely profile parameter owner event owned
  change joint = originalLaw.bind (fun carried =>
    (channel (observe carried)).map fun input => (carried, input)) at law
  refine ⟨recover, recovers, ?_⟩
  intro input inputSupport
  obtain ⟨selected, supported, equal⟩ := PMF.support_map .. ▸ inputSupport
  have jointSupport := supported
  rw [law, PMF.support_bind] at supported
  obtain ⟨carried, carriedSupport, chosen⟩ := Set.mem_iUnion₂.mp supported
  obtain ⟨signal, signalSupport, rfl⟩ := PMF.support_map .. ▸ chosen
  have first := recovers (carried, signal) jointSupport
  rw [equal] at first
  refine ⟨observe carried, first, ?_⟩
  rw [law]
  apply conditional_observation_kernel_recovered originalLaw observe channel (observe carried)
    input
  · exact ⟨carried, carriedSupport, rfl, equal ▸ signalSupport⟩
  · intro other otherSupport possible
    have otherJoint : (other, input) ∈ joint.support := by
      rw [law, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨other, otherSupport, ?_⟩
      rw [PMF.support_map]
      exact ⟨input, possible, rfl⟩
    exact Option.some.inj ((recovers (other, input) otherJoint).symm.trans first)

end Vegas
