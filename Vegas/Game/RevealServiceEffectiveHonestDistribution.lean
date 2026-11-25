module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealServiceHonestDistribution
public import Vegas.Game.RevealServiceEffectiveTimely
public import Vegas.Pending.CanonicalOutcomeAccepted

@[expose] public section

/-! # The honest outcome law of effective-opening clients

Clients of a reference that opens a publication exactly when the opening would
be accepted keep the outcome law of an always-open twin reference at every
scheduler boundary, under every public scheduler. A round in which every ready
event is a publication preserves the always-open reference's outcome law,
because accepted honest openings stay within their deadline and a rejected
opening's expiry publishes the same failure. A solitary segment preserves the
effective reference's outcome law, which is the always-open twin's.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

section Induction

variable {horizon turns : Nat} {scheduler :
    (serviceApplication setup deps duration leaks).Scheduler}
  {delay bound : (serviceGraph setup deps).EventId → Nat}

/-- **The honest outcome law from every boundary.** Under the asynchronous
service contract, on a graph where only independent reveals are concurrent and
every other event leads, honest clients of an opening, ready-independent
reference run, from every initialized execution whose responses saw only
completed events or publications ready, to the reference's outcome law. -/
theorem effective_runToHorizon_outcomeDistribution
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (only : (serviceGraph setup deps).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup deps).outputLayout event).IsPublication →
      (serviceGraph setup deps).Leading event)
    (effective : (serviceGraph setup deps).BehavioralProfile)
    (effectiveIndependent : ReadyIndependent effective)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        effective owner event actor ((serviceGraph setup deps).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup deps).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (twins : ∀ config, outcomeDistribution effective read config = outcomeDistribution reference
      read config) :
    let players := turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) effective
    ∀ execution : (serviceApplication setup deps duration leaks).Execution,
      execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
        (serviceInitialDistribution setup deps) scheduler players
          execution.environmentRecall.length).support →
      execution.environmentRecall.length ≤ horizon →
      SeenWithin (fun event => ((serviceGraph setup deps).outputLayout event).IsPublication)
        execution →
      ((serviceApplication setup deps duration leaks).runToHorizon scheduler players horizon
          execution).map (fun final => read final.application.config) =
        outcomeDistribution reference read execution.application.config := by
  intro players
  refine runToHorizon_outcomeDistribution_of_segments contract only players reference read ?_ ?_
  · intro execution next supported bounded allPublications reached
    exact reactive_round_outcomeDistribution_of_accepted independent opens read keyed invariant
      (serviceTimeouts setup deps duration) leaks scheduler players execution next
      allPublications (fun event owner ready owned _ accepted =>
        effectivePublication_withinDeadline contract timely players owner effective decides rfl
          execution.environmentRecall.length bounded execution supported event
          (effectiveIndependent.actorSerial event) owned ready (allPublications event ready)
          accepted) reached
  · intro execution event ready notPublication supported bounded untouched
    have segment := soleSegment_outcomeDistribution (serviceTimeouts setup deps duration) leaks
      scheduler delay bound contract timely effective effectiveIndependent read keyed
      players event (fun _ _ => rfl) (only.solitary notPublication) (leading event notPublication)
      notPublication execution ready supported untouched bounded
    simp only [twins] at segment
    exact segment

/-- **The honest outcome law of the run.** Under the hypotheses of
`honest_runToHorizon_outcomeDistribution`, the outcome of the honest clients' run to the
horizon has the reference's outcome law from the initial configurations. -/
theorem effective_roundsFrom_outcomeDistribution
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (only : (serviceGraph setup deps).RevealsOnlyConcurrent)
    (leading : ∀ event, ¬ ((serviceGraph setup deps).outputLayout event).IsPublication →
      (serviceGraph setup deps).Leading event)
    (effective : (serviceGraph setup deps).BehavioralProfile)
    (effectiveIndependent : ReadyIndependent effective)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        effective owner event actor ((serviceGraph setup deps).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent reference) (opens : OpensPublications reference)
    {Outcome : Type*} (read : (serviceGraph setup deps).Config → Outcome)
    (keyed : ∀ left right : (serviceGraph setup deps).Config, runKey left = runKey right →
      read left = read right)
    (invariant : ∀ config, read config.erase = read config)
    (twins : ∀ config, outcomeDistribution effective read config = outcomeDistribution reference
      read config) :
    ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialDistribution setup deps)
        scheduler (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
          (firstTurnTiming setup turns deps) effective) horizon).map
        (fun final => read final.application.config) =
      (serviceInitialDistribution setup deps).bind
        (fun state => outcomeDistribution reference read state.config) := by
  let app := serviceApplication setup deps duration leaks
  let players := turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
    (firstTurnTiming setup turns deps) effective
  unfold ReactiveApplication.roundsFrom
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro state member
  let execution := ReactiveApplication.Execution.initial app state
  have supported : execution ∈ (app.roundsFrom (serviceInitialDistribution setup deps) scheduler
    players
      execution.environmentRecall.length).support := by
    change execution ∈ (app.roundsFrom (serviceInitialDistribution setup deps) scheduler players
      0).support
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨_, member, by simp [ReactiveApplication.runRounds, execution]⟩
  have seen : SeenWithin (fun event => ((serviceGraph setup deps).outputLayout event).IsPublication)
      execution := by
    intro who entry present
    cases present
  exact effective_runToHorizon_outcomeDistribution (turns := turns) contract timely only leading
    effective effectiveIndependent decides reference independent opens read keyed invariant twins
    execution supported (Nat.zero_le _) seen

end Induction

end Vegas
