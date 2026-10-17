/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePrivateService
import Interaction.ReactiveRoundTrace

/-! # Resolved native binding success as an original local-seed function

The function is extracted from genuine initialized counted histories. Private
success identifies every such resolved history with the same function, retaining
its original seed and entire emission-clock word. The existing native runner is
used throughout; no new execution process is introduced.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "Seeds" => RestSeed × (PhaseSeedAddress graph → LocalSeed)
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

open Classical in
/-- An actual resolved accepting episode realizes this local seed and emission
word. Outside the genuine domain the function is false. -/
def bindingSuccess (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (seed : LocalSeed) (clocks : List Nat) : Bool :=
  decide (∃ seeds ∈ seedLaw.support, ∃ control : (app).Control,
    Nonempty (((menu).protocol initial horizon (family seeds)).Trace (some control)) ∧
      coordinate.1.Resolved control.execution.application ∧
      seeds.2 coordinate = seed ∧
      bindingEmissionClocks runtime leaks coordinate.1 owner control.execution = clocks ∧
      BindingAccepted runtime leaks coordinate.1 owner control.execution)

open Classical in
/-- Strong private success makes the extracted function agree with every
genuine resolved endpoint, not only its existential representative. -/
theorem bindingSuccess_eq_of_resolved
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (seeds : Seeds) (supported : seeds ∈ seedLaw.support)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon (family seeds)).Trace (some control))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (resolved : coordinate.1.Resolved control.execution.application) :
    bindingSuccess runtime leaks bounds plan inputs horizon seedLaw family owner coordinate
        (seeds.2 coordinate) (bindingEmissionClocks runtime leaks coordinate.1 owner
          control.execution) =
      decide (BindingAccepted runtime leaks coordinate.1 owner control.execution) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bindingSuccess, decide_eq_true_eq]
  constructor
  · rintro ⟨otherSeeds, otherSupport, other, ⟨otherTrace⟩, otherResolved, sameSeed,
      sameClocks, accepted⟩
    exact (privateSuccess otherSeeds otherSupport seeds supported other control otherTrace trace
      coordinate owner payload output otherResolved resolved sameSeed sameClocks).mp accepted
  · intro accepted
    exact ⟨seeds, supported, control, ⟨trace⟩, resolved, rfl, rfl, accepted⟩

open Classical in
/-- A genuinely unsent binding cannot acquire an accepting receipt. The local
success function therefore assigns it zero, also after its attempt retires. -/
theorem bindingSuccess_eq_false_of_unsent
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (seeds : Seeds) (supported : seeds ∈ seedLaw.support)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon (family seeds)).Trace (some control))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (resolved : coordinate.1.Resolved control.execution.application)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate.1) :
    bindingSuccess runtime leaks bounds plan inputs horizon seedLaw family owner coordinate
        (seeds.2 coordinate) (bindingEmissionClocks runtime leaks coordinate.1 owner
          control.execution) = false := by
  rw [bindingSuccess_eq_of_resolved runtime leaks bounds plan inputs horizon seedLaw family
    privateSuccess seeds supported control trace owner coordinate payload output resolved]
  apply decide_eq_false_iff_not.mpr
  rintro ⟨message, member, sender, attempt, event, _receipt⟩
  have recalled := (app).history_inputRecall initial horizon (family seeds)
    ((menu).toRawTrace initial horizon (family seeds) trace)
  have authored : message ∈ (app).outputs (control.execution.recall owner) := by
    rw [← recalled owner]
    exact List.mem_filter.mpr ⟨member, by simp only [sender, decide_true]⟩
  apply unsent message authored
  simp only [PhaseCount.event?, event, Option.map_some, attempt]

open Classical in
/-- Every supported distribution on actual resolved histories retains its
whole original tag jointly with the extracted service success. -/
theorem bindingSuccess_joint {Tag Result : Type}
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (law : PMF Tag) (seeds : Tag → Seeds) (control : Tag → (app).Control)
    (supported : ∀ tag ∈ law.support, seeds tag ∈ seedLaw.support)
    (genuine : ∀ tag ∈ law.support,
      Nonempty (((menu).protocol initial horizon (family (seeds tag))).Trace (some (control tag))))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (resolved : ∀ tag ∈ law.support, coordinate.1.Resolved (control tag).execution.application)
    (retain : Tag → Result) :
    law.map (fun tag => (decide (BindingAccepted runtime leaks coordinate.1 owner
      (control tag).execution), retain tag)) =
      law.map (fun tag => (bindingSuccess runtime leaks bounds plan inputs horizon seedLaw family
        owner coordinate ((seeds tag).2 coordinate)
          (bindingEmissionClocks runtime leaks coordinate.1 owner (control tag).execution),
        retain tag)) := by
  apply map_congr_on_support
  intro tag member
  obtain ⟨trace⟩ := genuine tag member
  exact congrArg (fun accepted => (accepted, retain tag))
    (bindingSuccess_eq_of_resolved runtime leaks bounds plan inputs horizon seedLaw family
      privateSuccess (seeds tag) (supported tag member) (control tag) trace owner coordinate
        payload output (resolved tag member)).symm

open Classical in
/-- The actual native continuation runner has this same success readout,
jointly with its final execution and arbitrary original tags. Initial tags
may carry their likelihood-induced posterior and need not be independent. -/
theorem runRounds_bindingSuccess_joint {Tag Result : Type}
    (seedLaw : PMF Seeds) (family : Seeds → (app).Scheduler)
    (privateSuccess : PrivateBindingSuccess runtime leaks bounds plan inputs horizon seedLaw family)
    (law : PMF Tag) (seeds : Tag → Seeds) (execution : Tag → (app).Execution)
    (players : Tag → Player → (app).Policy)
    (covered : ∀ tag ∈ law.support, ∀ who past view action,
      action ∈ (players tag who past view).support → action ∈ (menu).actions who past view)
    (remaining count : Nat)
    (supported : ∀ tag ∈ law.support, seeds tag ∈ seedLaw.support)
    (genuine : ∀ tag ∈ law.support,
      Nonempty (((menu).protocol initial horizon (family (seeds tag))).Trace
        (some ⟨remaining + count, none, execution tag⟩)))
    (owner : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (output : graph.outputLayout coordinate.1.event = .binding owner payload)
    (resolved : ∀ tag ∈ law.support, ∀ final ∈ ((app).runRounds (family (seeds tag))
      (players tag) count (execution tag)).support, coordinate.1.Resolved final.application)
    (retain : Tag → (app).Execution → Result) :
    (law.bind fun tag => ((app).runRounds (family (seeds tag)) (players tag) count
      (execution tag)).map (fun final =>
        (decide (BindingAccepted runtime leaks coordinate.1 owner final), retain tag final))) =
      law.bind (fun tag => ((app).runRounds (family (seeds tag)) (players tag) count
        (execution tag)).map (fun final =>
          (bindingSuccess runtime leaks bounds plan inputs horizon seedLaw family owner coordinate
            ((seeds tag).2 coordinate)
              (bindingEmissionClocks runtime leaks coordinate.1 owner final),
            retain tag final))) := by
  apply bind_congr_on_support
  intro tag member
  apply map_congr_on_support
  intro final reached
  obtain ⟨trace⟩ := genuine tag member
  obtain ⟨finalTrace⟩ := (menu).trace_runRounds initial horizon (family (seeds tag))
    (players tag) (covered tag member) remaining count (execution tag) final trace reached
  exact congrArg (fun accepted => (accepted, retain tag final))
    (bindingSuccess_eq_of_resolved runtime leaks bounds plan inputs horizon seedLaw family
      privateSuccess (seeds tag) (supported tag member) ⟨remaining, none, final⟩ finalTrace
        owner coordinate payload output (resolved tag member final reached)).symm

end Vegas.EventGraphRuntime.PhaseService
