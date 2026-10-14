/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSeedOccupation
import Interaction.ReactiveSiteHorizon

/-! # Original immutable seeds under actual finite-site Bayes beliefs -/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- Positive finite-site information mass gives a genuine supported observation
of the actual bounded command-occupation law. -/
theorem occupation_observation_support [NeZero horizon]
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site) :
    site.1 ∈ (((app).occupationControlLaw (mixture).scheduler (players profile)
      (inputs.map State.initial) horizon).map ((app).observe owner)).support := by
  classical
  have antichain := (menu).decisionInformationAntichain
    (inputs.map State.initial) horizon (mixture).scheduler owner site
  have massPositive : 0 < ((model).informationMass profile owner site).toReal :=
    ENNReal.toReal_pos (ne_of_gt positive)
      (ne_of_lt (lt_of_le_of_lt
        ((model).informationMass_le_one profile owner site antichain) ENNReal.one_lt_top))
  have marginal := (menu).occupation_information_mass
    (inputs.map State.initial) horizon (mixture).scheduler profile owner site
  have marginalPositive : 0 <
      ((((app).occupationControlLaw (mixture).scheduler (players profile)
        (inputs.map State.initial) horizon).map ((app).observe owner)) site.1).toReal := by
    rw [marginal]
    exact div_pos massPositive (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne horizon)))
  exact (PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp marginalPositive).1

/-- Tagging standard finite-site Bayes beliefs with the actual seed posterior
is exactly conditioning the original immutable seeded command law. -/
theorem bayesBelief_seededDecision [NeZero horizon]
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site) :
    (fiberPosterior
      (controller.seededSampledRoundDecisionLaw remainder laws inputs (players profile)
        ((PMF.uniformOfFintype (Fin horizon)).map Fin.val))
      (fun outcome => decisionObservation (owner := owner) outcome.1.2) site.1).map
        (fun outcome =>
          (decisionControl (runtime := runtime) (leaks := leaks) horizon outcome.1, outcome.2)) =
      ((((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain
          (inputs.map State.initial) horizon (mixture).scheduler owner site) positive).map
            (fun history => history.1.state)).bind fun state =>
              (draws state).map (Prod.mk state)) := by
  classical
  let source := controller.seededSampledRoundDecisionLaw remainder laws inputs (players profile)
    ((PMF.uniformOfFintype (Fin horizon)).map Fin.val)
  let read := fun outcome :
      (Nat × graph.Inputs × (app).Command × (app).Execution) × ((side : Bool) → A side) =>
    (decisionControl (runtime := runtime) (leaks := leaks) horizon outcome.1, outcome.2)
  let observe := fun outcome : (app).ProtocolState × ((side : Bool) → A side) =>
    (app).observe owner outcome.1
  let law := (app).occupationControlLaw (mixture).scheduler (players profile)
    (inputs.map State.initial) horizon
  have observationPresent := controller.occupation_observation_support remainder laws bounds
    inputs horizon profile site positive
  have mapped : source.map read = law.bind fun state => (draws state).map (Prod.mk state) :=
    controller.seededSampledRoundDecisionLaw_control remainder laws inputs (players profile) horizon
  have sourcePresent : site.1 ∈ (source.map (observe ∘ read)).support := by
    have observationEq : source.map (observe ∘ read) = law.map ((app).observe owner) := by
      rw [← PMF.map_comp, mapped]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, observe]
      change (law.bind fun state => (draws state).map
        (Function.const _ ((app).observe owner state))) = _
      simp_rw [PMF.map_const]
      exact PMF.bind_pure_comp _ _
    rwa [observationEq]
  have transported := map_fiberPosterior_readout source read observe site.1 sourcePresent
  have conditioned := fiberPosterior_bind_of_observation law
    (fun state => (draws state).map (Prod.mk state)) ((app).observe owner) observe
    (by
      intro state _ outcome supported
      obtain ⟨values, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      rw [← equal]) site.1 observationPresent
  have bayes := (menu).bayesBelief_state_eq_occupationPosterior
    (inputs.map State.initial) horizon (mixture).scheduler profile owner site
      ((menu).decisionInformationAntichain
        (inputs.map State.initial) horizon (mixture).scheduler owner site) positive
  change (fiberPosterior source (observe ∘ read) site.1).map read = _
  rw [mapped] at transported
  exact transported.trans (conditioned.trans
    (congrArg (fun distribution : PMF (app).ProtocolState =>
      distribution.bind fun state => (draws state).map (Prod.mk state)) bayes.symm))

end Vegas.EventGraphRuntime.LocalSeedController
