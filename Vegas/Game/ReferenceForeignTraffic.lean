module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.AsyncDeviationForeign
public import Vegas.Game.LastOwnedPhase

@[expose] public section

/-! # Foreign bindings of reference clients

An honest foreign owner's binding is ready alone. Fixing the owner's first
choice agrees with the decided client while the other honest owners are idle,
and decided bindings of equal admission give the deviator equal traffic laws
from equal starting traffic. The proofs retain the supplied dependency choice
and reference profile.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Before the ready event completes, fixing its owner's first choice agrees
with the decided client while every other honest owner is idle. -/
theorem reference_foreign_fixedRun {horizon : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (focal : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup deps).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (action : (serviceGraph setup deps).Action event)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (ready : execution.application.config.cut.Ready event) :
    let baseline := turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference
    let member := fun past view =>
      if turnIndex (serviceTimeouts setup deps duration) leaks owner event past view = some 0 then
        fixedOpportunity (serviceTimeouts setup deps duration) leaks
          bound owner event action past view
      else baseline owner past view
    ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (Function.update baseline focal deviation) owner member)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    (serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  intro baseline member
  have solitary : (serviceGraph setup deps).Solitary event :=
    fun cut _ otherReady ready => alone cut _ ready otherReady
  let app := serviceApplication setup deps duration leaks
  let players := Function.update baseline focal deviation
  unfold ReactiveApplication.runUntilHorizon
  apply app.runUntil_congr_of_agree scheduler (Function.update players owner member)
    (Function.update
      (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
      (decidedTurnPolicy setup leaks bound owner event action))
    (fun final => event ∈ final.application.config.cut.completed)
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current holds running command _ middle moved actor active
    have activateIs : command = .activate actor := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have unchanged := activation_application (setup := setup) leaks current middle actor moved
    have middleReady : middle.application.config.cut.Ready event := by
      rw [unchanged]
      exact holds running
    by_cases isOwner : actor = owner
    · subst actor
      simp only [Function.update_self]
      have serving := middle.application.ownTurn?_of_ready solitary.ownerSolitary middleReady
        owned
      dsimp only [member, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy]
      simp only [Fin.val_zero]
      by_cases selected : turnIndex (serviceTimeouts setup deps duration) leaks owner event
          (middle.logs owner) (middle.observe app owner) = some 0
      · simp only [selected, ite_true]
      · simp only [selected, ite_false]
        exact sourceServiceTurnPolicy_laterTurn_reference owned serving selected
    · simp only [Function.update_of_ne isOwner]
      by_cases isFocal : actor = focal
      · subst actor
        simp only [players, focalPlayers, Function.update_self]
      · simp only [players, focalPlayers, Function.update_of_ne isFocal]
        have idle : (middle.observe app actor).application.publicView.ownTurn? actor = none := by
          apply ownTurn?_none_of_alone alone middle.application middleReady actor
          rw [owned]
          exact fun equal => isOwner (Option.some.inj equal).symm
        simp only [baseline, EventGraphRuntime.turnPolicy, idle,
          ReactiveApplication.silentPolicy_apply]
  · intro current holds running next reached
    exact round_ready_of_pending alone (holds running) reached
  · exact fun _ => ready

/-- An honest foreign binding has the same deviator traffic law at equal public
admission choices and equal initial deviator traffic, from initialized
executions where the binding is ready and untouched. -/
theorem reference_binding_traffic_congr (serial : (serviceGraph setup deps).ActorSerial)
    {horizon : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (focal owner : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy) (foreign : owner ≠ focal)
    (event : (serviceGraph setup deps).EventId) {payload : L.Ty}
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup deps) event = .bind owner payload outputEq codeEq)
    (alone : ∀ (cut : (serviceGraph setup deps).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (left right : (serviceApplication setup deps duration leaks).Execution)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftSupported : left ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation)
      left.environmentRecall.length).support)
    (rightSupported : right ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation)
      right.environmentRecall.length).support)
    (leftUntouched : Untouched setup leaks event left)
    (rightUntouched : Untouched setup leaks event right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (same : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right) :
    (((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal)) =
    (((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal)) := by
  let app := serviceApplication setup deps duration leaks
  let players := Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) reference) focal deviation
  have follows : players owner = turnPolicy (serviceTimeouts setup deps duration) leaks
      bound turns (firstTurnTiming setup turns deps) reference owner :=
    Function.update_of_ne foreign _ _
  have facts (current : app.Execution)
      (supported : current ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler players
        current.environmentRecall.length).support)
      (untouched : Untouched setup leaks event current)
      (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks current owner ∧
      CanonicalSlotsUsed setup leaks current owner ∧
      ownerTurns owner event current = 0 ∧
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (current.logs owner) event =
        false := by
    obtain ⟨own, slots⟩ := canonicalSlots_roundsFrom_reference (setup := setup) (leaks := leaks)
      serial scheduler players owner (firstTurnTiming setup turns deps) reference follows
      current.environmentRecall.length current supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact untouched owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler players
      current.environmentRecall.length bounded current supported, own, slots, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ :=
        ((eventRecorded_iff (serviceTimeouts setup deps duration)) leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftOwn, leftSlots, leftTurns, leftRecorded⟩ :=
    facts left leftSupported leftUntouched leftBounded
  obtain ⟨⟨rightTrace⟩, rightOwn, rightSlots, rightTurns, rightRecorded⟩ :=
    facts right rightSupported rightUntouched rightBounded
  have equal : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right := by
    simp only [foreignReadout, same, leftTurns, rightTurns, leftRecorded, rightRecorded]
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  rw [environments] at leftTrace
  have coupled := binding_stopped_readout_congr serial scheduler focal deviation bound foreign
    outputEq codeEq node leftChoice rightChoice admitted alone left right
    (leftRemaining := 0) (rightRemaining := 0)
    (by simpa only [Nat.zero_add] using leftTrace)
    (by simpa only [Nat.zero_add] using rightTrace)
    leftReady rightReady leftOwn leftSlots rightOwn rightSlots equal
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [ReactiveApplication.runUntilHorizon, environments, PMF.map_comp,
    foreignReadout, Function.comp_def] using projected

end Vegas
