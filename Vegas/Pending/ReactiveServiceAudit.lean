/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingOmission
import Interaction.ReactiveAuditCollection
import Interaction.ReactiveTrafficState

/-! # Collected charges from traffic evidence and public binding omissions

The terminal service combines its actual sampled-traffic verdict with the
ledger's missed-binding predicate. A player is charged once if either branch
finds a breach. A missing sample never counts as omission evidence. The
public branch assumes the stated protected-inclusion service and collectible
escrow; without those backend guarantees it is not an attribution theorem.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- Only a completed binding without an accepted handle counts as an omission.
The responsible account is the statically declared actor of that event. -/
def PublicView.missedBindingBy (view : PublicView graph) (who : Player) : Bool :=
  decide (∃ event, graph.actor? event = some who ∧ view.missedBinding event = true)

theorem PublicView.missedBindingBy_of_event (view : PublicView graph) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (missed : view.missedBinding event = true) : view.missedBindingBy who = true := by
  classical
  exact decide_eq_true ⟨event, owned, missed⟩

theorem PublicView.missedBindingBy_clear (view : PublicView graph)
    (clear : ∀ event, view.missedBinding event = false) (who : Player) :
    view.missedBindingBy who = false := by
  classical
  apply decide_eq_false
  rintro ⟨event, _owned, missed⟩
  rw [clear event] at missed
  cases missed

/-- The actual traffic history and terminal public application view. No
private value, player response representation or unsampled absence is used. -/
def serviceAuditObservation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : (runtime.reactiveApplication leaks).ProtocolState) :=
  ((runtime.reactiveApplication leaks).stateTraffic state,
    state.map fun control => control.execution.application.publicView)

/-- One collected verdict, with arbitrary correlation between players and
arbitrary sampling inside the supplied authentic traffic audit. -/
def serviceAudit (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (observed : List (runtime.reactiveApplication leaks).TrafficRecord ×
      Option (PublicView graph)) :
    FinDist (Player → Bool) :=
  (trafficAudit observed.1).map fun verdict who =>
    verdict who || observed.2.elim false (fun view => view.missedBindingBy who)

theorem serviceAuditObservation_normalization (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (normal : (runtime.reactiveApplication leaks).SubmissionNormalization)
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    runtime.serviceAuditObservation leaks (normal.state state) =
      runtime.serviceAuditObservation leaks state := by
  cases state <;> rfl

/-- The public branch collects with certainty; otherwise the actual traffic
collection probability is retained exactly. There is no independence premise. -/
theorem serviceAudit_charge (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (state : (runtime.reactiveApplication leaks).ProtocolState) (who : Player) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks trafficAudit) state who =
      if state.elim false (fun control => control.execution.application.publicView.missedBindingBy
          who) then 1 else
        TerminalAudit.charge (runtime.reactiveApplication leaks).stateTraffic trafficAudit state
          who := by
  unfold TerminalAudit.charge serviceAudit serviceAuditObservation
  simp only [FinDist.map_comp, Function.comp_def]
  cases state with
  | none => simp only [Option.map_none, Option.elim_none, Bool.or_false, Bool.false_eq_true,
      ite_false]
  | some control =>
      simp only [Option.map_some, Option.elim_some]
      by_cases missing : control.execution.application.publicView.missedBindingBy who = true
      · simp only [missing, Bool.or_true, ↓reduceIte,
          FinDist.map_const, FinDist.prob_pure_self]
      · have clear : control.execution.application.publicView.missedBindingBy who = false :=
          Bool.eq_false_iff.mpr missing
        simp only [clear, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

theorem serviceAudit_charge_ge_traffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (state : (runtime.reactiveApplication leaks).ProtocolState) (who : Player) :
    TerminalAudit.charge (runtime.reactiveApplication leaks).stateTraffic trafficAudit state who ≤
      TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks trafficAudit) state who := by
  rw [runtime.serviceAudit_charge]
  split
  · exact FinDist.prob_le_one _ _
  · exact le_refl _

theorem serviceAudit_charge_of_omission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (control : (runtime.reactiveApplication leaks).Control) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (missed : control.execution.application.publicView.missedBinding event = true) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
      (runtime.serviceAudit leaks trafficAudit) (some control) who = 1 := by
  rw [runtime.serviceAudit_charge]
  simp only [Option.elim_some,
    control.execution.application.publicView.missedBindingBy_of_event who event owned missed,
    ↓reduceIte]

/-- Existing traffic coverage bounds remain valid for every actual law of
continuations after adding the public omission branch. -/
theorem serviceAudit_collection_ge_traffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (law : FinDist (runtime.reactiveApplication leaks).ProtocolState) (who : Player) :
    ((((law.map (runtime.reactiveApplication leaks).stateTraffic).bind trafficAudit).map
        (fun verdict => verdict who)).prob true) ≤
      ((((law.map (runtime.serviceAuditObservation leaks)).bind
        (runtime.serviceAudit leaks trafficAudit)).map
          (fun verdict => verdict who)).prob true) := by
  rw [TerminalAudit.collection_probability, TerminalAudit.collection_probability]
  apply FinDist.expect_mono
  intro state _supported
  exact runtime.serviceAudit_charge_ge_traffic leaks trafficAudit state who

/-- An attributed forbidden record supplies the same conditional collection
bound when the terminal service also checks public omissions. This applies to
arbitrary continuation laws, including reactions after the violation. -/
theorem serviceAudit_collection_from_record (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Evidence : Type}
    (project : (runtime.reactiveApplication leaks).TrafficRecord → Evidence)
    (attribution : Evidence → Player) (permitted : Evidence → Bool)
    (sample : List Evidence → FinDist (List Evidence))
    (law : FinDist (runtime.reactiveApplication leaks).ProtocolState)
    (who : Player) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ (sample actual).probOf {observed | record ∈ observed})
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : ∀ state ∈ law.support,
      record ∈ (runtime.reactiveApplication leaks).stateTraffic state)
    (owner : attribution (project record) = who)
    (forbidden : permitted (project record) = false) :
    rate ≤ (((law.map (runtime.serviceAuditObservation leaks)).bind
      (runtime.serviceAudit leaks ((runtime.reactiveApplication leaks).sampledTrafficAudit
        project attribution permitted sample))).map (fun verdict => verdict who)).prob true := by
  exact ((runtime.reactiveApplication leaks).sampledTrafficAudit_collection_from_record
    project attribution permitted sample law _ who rate coverage record present owner
      forbidden).trans
      (runtime.serviceAudit_collection_ge_traffic leaks _ law who)

/-- Publicly certified omission is collected with certainty, regardless of
which binding was missed on each branch and regardless of packet sampling. -/
theorem serviceAudit_collection_of_omission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : List (runtime.reactiveApplication leaks).TrafficRecord →
      FinDist (Player → Bool))
    (law : FinDist (runtime.reactiveApplication leaks).ProtocolState) (who : Player)
    (missing : ∀ state ∈ law.support,
      state.elim false (fun control =>
        control.execution.application.publicView.missedBindingBy who) = true) :
    (((law.map (runtime.serviceAuditObservation leaks)).bind
      (runtime.serviceAudit leaks trafficAudit)).map
        (fun verdict => verdict who)).prob true = 1 := by
  rw [TerminalAudit.collection_probability]
  calc
    _ = law.expect (fun _ => (1 : ℝ)) := by
      apply FinDist.expect_congr
      intro state supported
      rw [runtime.serviceAudit_charge, missing state supported]
      rfl
    _ = 1 := FinDist.expect_const _ _

end Vegas.EventGraphRuntime
