/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.ReactiveSettledVerdict
import Interaction.ReactiveAuditCollection
import Interaction.ReactiveTrafficState
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Collected charges from traffic evidence and public binding omissions

The terminal service reads the actual traffic history and the contract's
settled record. It combines a traffic verdict, which may judge each packet
against the settled record, with the record's missed-binding predicate. A
player is charged once if either branch finds a breach. A missing sample never
counts as omission evidence. The public branch assumes the stated
protected-inclusion service and collectible escrow; without those backend
guarantees it is not an attribution theorem.
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

/-- A graph without binding events has no binding to omit. -/
theorem PublicView.missedBindingBy_of_publications (view : PublicView graph)
    (publications : ∀ event owner payload, graph.outputLayout event ≠ .binding owner payload)
    (who : Player) : view.missedBindingBy who = false := by
  apply view.missedBindingBy_clear
  intro event
  unfold PublicView.missedBinding
  split
  · rename_i owner payload layout
    exact (publications event owner payload layout).elim
  · rfl
  · rfl
  · rfl

/-- The contract's settled record at an execution: its public view and the
receipts of every inclusion. -/
def settledRecord (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : SettledRecord graph :=
  ⟨execution.application.publicView, execution.receipts⟩

/-- The actual traffic history and the settled record. No private value,
player response representation or unsampled absence is used. -/
def serviceAuditObservation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : (runtime.reactiveApplication leaks).ProtocolState) :=
  ((runtime.reactiveApplication leaks).stateTraffic state,
    state.map fun control => runtime.settledRecord leaks control.execution)

/-- One collected verdict, with arbitrary correlation between players and
arbitrary sampling inside the supplied authentic traffic audit, which may read
the settled record. Before initialization nothing is collected. -/
def serviceAudit (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (observed : List (runtime.reactiveApplication leaks).TrafficRecord ×
      Option (SettledRecord graph)) :
    PMF (Player → Bool) :=
  match observed.2 with
  | none => PMF.pure fun _ => false
  | some record => (trafficAudit record observed.1).map fun verdict who =>
      verdict who || record.view.missedBindingBy who

theorem serviceAuditObservation_normalization (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (normal : (runtime.reactiveApplication leaks).SubmissionNormalization)
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    runtime.serviceAuditObservation leaks (normal.state state) =
      runtime.serviceAuditObservation leaks state := by
  cases state <;> rfl

/-- Nothing is collected before initialization. -/
theorem serviceAudit_charge_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (who : Player) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
      (runtime.serviceAudit leaks trafficAudit) none who = 0 := by
  unfold TerminalAudit.charge serviceAudit serviceAuditObservation
  simp only [Option.map_none, PMF.pure_map]
  rw [PMF.pure_apply_of_ne _ _ Bool.noConfusion, ENNReal.toReal_zero]

/-- The public branch collects with certainty; otherwise the actual traffic
collection probability is retained exactly. There is no independence premise. -/
theorem serviceAudit_charge (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (control : (runtime.reactiveApplication leaks).Control) (who : Player) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks trafficAudit) (some control) who =
      if control.execution.application.publicView.missedBindingBy who then 1 else
        ((((trafficAudit (runtime.settledRecord leaks control.execution)
          ((runtime.reactiveApplication leaks).executionTraffic control.execution)).map
            (fun verdict => verdict who)) true).toReal) := by
  unfold TerminalAudit.charge serviceAudit serviceAuditObservation
  simp only [Option.map_some, PMF.map_comp, Function.comp_def]
  by_cases missing : control.execution.application.publicView.missedBindingBy who = true
  · simp only [settledRecord, missing, Bool.or_true, ↓reduceIte]
    erw [PMF.map_const]
    simp [PMF.pure_apply]
  · have clear : control.execution.application.publicView.missedBindingBy who = false :=
      Bool.eq_false_iff.mpr missing
    simp only [settledRecord, clear, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem serviceAudit_charge_of_omission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (control : (runtime.reactiveApplication leaks).Control) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (missed : control.execution.application.publicView.missedBinding event = true) :
    TerminalAudit.charge (runtime.serviceAuditObservation leaks)
      (runtime.serviceAudit leaks trafficAudit) (some control) who = 1 := by
  rw [runtime.serviceAudit_charge]
  simp only [control.execution.application.publicView.missedBindingBy_of_event who event owned
    missed, ↓reduceIte]

/-- A charge of the traffic branch is a lower bound for the collected charge. -/
theorem serviceAudit_charge_ge_traffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (trafficAudit : SettledRecord graph →
      List (runtime.reactiveApplication leaks).TrafficRecord → PMF (Player → Bool))
    (control : (runtime.reactiveApplication leaks).Control) (who : Player) :
    ((((trafficAudit (runtime.settledRecord leaks control.execution)
        ((runtime.reactiveApplication leaks).executionTraffic control.execution)).map
          (fun verdict => verdict who)) true).toReal) ≤
      TerminalAudit.charge (runtime.serviceAuditObservation leaks)
        (runtime.serviceAudit leaks trafficAudit) (some control) who := by
  rw [runtime.serviceAudit_charge]
  split
  · exact pmf_toReal_apply_le_one _ _
  · exact le_refl _

/-- A forbidden record in the actual traffic, judged against the settled record
of the same state, bounds the collected charge below by its sampling rate. -/
theorem serviceAudit_charge_from_record (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Evidence : Type}
    (project : SettledRecord graph → (runtime.reactiveApplication leaks).TrafficRecord → Evidence)
    (attribution : Evidence → Player) (permitted : Evidence → Bool)
    (sample : List Evidence → PMF (List Evidence))
    (who : Player) (rate : ℝ)
    (coverage : ∀ actual record, record ∈ actual →
      attribution record = who → permitted record = false →
      rate ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (control : (runtime.reactiveApplication leaks).Control)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (present : record ∈ (runtime.reactiveApplication leaks).executionTraffic control.execution)
    (owner : attribution (project (runtime.settledRecord leaks control.execution) record) = who)
    (forbidden : permitted (project (runtime.settledRecord leaks control.execution) record) =
      false) :
    rate ≤ TerminalAudit.charge (runtime.serviceAuditObservation leaks)
      (runtime.serviceAudit leaks fun settled =>
        (runtime.reactiveApplication leaks).sampledTrafficAudit (project settled) attribution
          permitted sample) (some control) who := by
  have lower := (runtime.reactiveApplication leaks).sampledTrafficAudit_collection_from_record
    (project (runtime.settledRecord leaks control.execution)) attribution permitted sample
    (PMF.pure control.execution) (runtime.reactiveApplication leaks).executionTraffic who rate
    coverage record (fun outcome supported => by
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact present) owner forbidden
  simp only [PMF.pure_map, PMF.pure_bind] at lower
  exact lower.trans (runtime.serviceAudit_charge_ge_traffic leaks (fun settled =>
    (runtime.reactiveApplication leaks).sampledTrafficAudit (project settled) attribution
      permitted sample) control who)

end Vegas.EventGraphRuntime
