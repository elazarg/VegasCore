/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceUnsentBayes
import Interaction.ReactiveProfileMixture

/-! # Original private player draws beside the local phased service seed -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (priority : RestSeed → List (phaseApplication runtime leaks).EnvironmentEntry →
    (phaseApplication runtime leaks).EnvironmentView → Nat)
  (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
    PhaseSeedDecision)
  (laws : PhaseSeedAddress graph → PMF LocalSeed) (restLaw : PMF RestSeed)
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  {Memory : Player → Type} (original : (who : Player) → PMF (Memory who))
  (members : (who : Player) → Memory who → (phaseApplication runtime leaks).Policy)

local notation "app" => phaseApplication runtime leaks
local notation "driver" => controller runtime leaks priority decideLocal
local notation "mixture" => ReactiveApplication.AddressedScheduler.coordinateImplementation
  (controller runtime leaks priority decideLocal) laws restLaw
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information menu initial horizon
  (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "SeedAt" => ReactiveApplication.AddressedScheduler.CoordinateSeed
  (Address := PhaseSeedAddress graph) (LocalSeed := LocalSeed) (RestSeed := RestSeed)
local notation "prior" => independentProduct
  (ReactiveApplication.AddressedScheduler.coordinateLaws laws restLaw)
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => prior
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
      (ReactiveApplication.Execution.environmentRecall
        (ReactiveApplication.Control.execution current))
local notation "privateDraws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct original
  | some current => independentProduct (fun who =>
      ReactiveApplication.Implementation.posterior
        (ReactiveApplication.policyMixture (phaseApplication runtime leaks)
          (original who) (members who))
        (ReactiveApplication.Execution.recall (ReactiveApplication.Control.execution current) who))

/-- The existing phased runner draws every original scheduler seed and every
original player member once. Its exact joint law retains those same draws;
conditional player memories use actual own recall, not fresh original priors. -/
theorem runRounds_private_seed_joint (input : graph.Inputs) (count : Nat) :
    ((prior).bind fun values => (independentProduct original).bind fun memories =>
      ((app).runRounds ((driver).family
        (ReactiveApplication.AddressedScheduler.unpack values))
          (fun who => members who (memories who)) count
            (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).map
              fun final => (final, (values, memories))) =
      ((app).runRounds (mixture).scheduler
        (fun who => ((app).policyMixture (original who) (members who)).policy) count
          (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).bind
            fun final => ((mixture).posterior final.environmentRecall).bind fun values =>
              (independentProduct (fun who =>
                ((app).policyMixture (original who) (members who)).posterior
                  (final.recall who))).map fun memories => (final, (values, memories)) :=
  (app).runRounds_policyMixtures_scheduler_joint prior
    (fun values => (driver).family (ReactiveApplication.AddressedScheduler.unpack values))
      original members count (PhaseRuntimeState.initial plan input)

/-- The same local-seed filter works at every actual owner belief jointly
with all original player members and the remaining original scheduler seeds.
Player members retain their actual recall-updated posteriors, including their
unplayed future decisions. No independence premise on those posteriors is used. -/
theorem belief_unsent_private_seed_product
    (timed : DeadlineExpiry runtime decideLocal)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (owner : Player) (site : (model).InformationSite owner)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (siteInfo : site.1 = some (past, view)) (coordinate : PhaseSeedAddress graph)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs past,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∃ (event : Set LocalSeed)
      (localPositive : ∃ seed ∈ event, seed ∈ (laws coordinate).support),
      ∀ belief : PMF ((model).InformationHistory owner site.1),
      ∃ residual : PMF (((model).InformationHistory owner site.1) ×
        (((index : {index : Option (PhaseSeedAddress graph) // index ≠ some coordinate}) →
          SeedAt index) × ((who : Player) → Memory who))),
      (belief.bind fun history => (draws history.1.state).bind fun values =>
        (privateDraws history.1.state).map fun memories => (values (some coordinate),
          (history, ((fun index : {index : Option (PhaseSeedAddress graph) //
            index ≠ some coordinate} => values index), memories)))) =
        ((laws coordinate).filter event localPositive).bind fun seed =>
          residual.map (Prod.mk seed) := by
  classical
  obtain ⟨event, localPositive, factored⟩ := belief_unsent_seed_product runtime leaks priority
    decideLocal laws restLaw bounds plan inputs horizon timed ordered maximal owner site past view
      siteInfo coordinate request unsent
  refine ⟨event, localPositive, ?_⟩
  intro belief
  obtain ⟨remaining, product⟩ := factored belief
  let residual := remaining.bind fun pair =>
    (privateDraws pair.1.1.state).map fun memories => (pair.1, (pair.2, memories))
  refine ⟨residual, ?_⟩
  have attached := congrArg (PMF.bind · (fun pair =>
    (privateDraws pair.2.1.1.state).map fun memories =>
      (pair.1, (pair.2.1, (pair.2.2, memories))))) product
  convert attached using 1 <;>
    simp only [residual, PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      Function.comp_def]
  apply bind_congr_on_support
  intro history _supported
  apply bind_congr_on_support
  intro values _possible
  cases current : history.1.state <;> rfl

end Vegas.EventGraphRuntime.PhaseServiceScheduler
