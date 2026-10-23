/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingOmission
import Vegas.Pending.ReactiveSettledVerdict
import Interaction.ReactiveTrafficState
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

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

end Vegas.EventGraphRuntime
