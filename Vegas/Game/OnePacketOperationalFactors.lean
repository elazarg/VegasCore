/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOperationalReads

/-! # Operational factors of a response

A late-delivery key carries the player's emitted envelopes
(`Vegas.LateKey.outputs`), its last emission (`Vegas.LateKey.lastEmitted`), its
turn, the events its envelopes name (`Vegas.LateKey.Recorded`), the count
verdict on a commitment at each prepared slot (`Vegas.LateKey.slotPermitted`),
and its canonical slot (`Vegas.LateKey.canonicalSlot`), all read from the
operational part of its recall.

From the keys before and after a response at a pending binding, the factors of
the as-if-honest law (`Vegas.pendingBindingHonestFactor`), of silence
(`Vegas.silenceFactor`) and of the slot tier (`Vegas.pendingBindingSlotFactor`)
are read: the as-if-honest law commits at the canonical slot, silence emits
nothing, and the slot tier draws a uniform tremble slot. Along every history of
the one-packet game, at a pending binding, the masses these laws give a
realized response with positive content are its content factor times these
factors (`Vegas.onePacket_pendingBinding_operational_masses`); without a turn or
after the player's packet for it, the realized response is silence, and all
three masses are one (`Vegas.onePacket_settled_operational_masses`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup runtime leaks) in
/-- The late-delivery key of a player at a player view. -/
def LateKey.ofView (who : Player) (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) : LateKey setup runtime leaks where
  owner := who
  current := operationalView setup runtime leaks view
  recalled := past.map fun entry => (operationalView setup runtime leaks
    entry.beforeView, entry.emitted)
  delivered := deliveredValue setup runtime leaks who view

theorem lateKey_some (who : Player) (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) :
    lateKey setup runtime leaks who (some (past, view)) = some (LateKey.ofView setup runtime leaks
      who past view) :=
  rfl

namespace LateKey

/-- The envelopes the key's owner emitted. -/
def outputs (key : LateKey setup runtime leaks) :
    List (Message Player (application setup runtime leaks).Payload) :=
  key.recalled.filterMap Prod.snd

/-- The last emission in the key's recall. -/
def lastEmitted (key : LateKey setup runtime leaks) :
    Option (Message Player (application setup runtime leaks).Payload) :=
  key.recalled.getLast?.bind Prod.snd

/-- The owner's turn in the key's public view. -/
def turn (key : LateKey setup runtime leaks) : Option (graph setup).EventId :=
  key.current.1.ownTurn? key.owner

/-- An emitted envelope of the key's owner names the event. -/
def Recorded (key : LateKey setup runtime leaks) (event : (graph setup).EventId) : Prop :=
  ∃ message ∈ key.outputs, message.payload.call.event? (graph setup) = some
    event

/-- The count verdict on the owner's commitment at a prepared slot for an event,
as its next envelope. -/
def slotPermitted (key : LateKey setup runtime leaks) (event : (graph setup).EventId) (slot : Nat) :
    Bool :=
  countPermits key.outputs ⟨(key.owner, key.outputs
    (runtime := runtime).length),
    ⟨.commitment event (key.owner, .prepared slot), none,
      key.current.1.tokenFor (.commitment event (key.owner, .prepared slot))⟩⟩

/-- The owner's canonical slot, read from its envelopes and its completed
bindings. -/
def canonicalSlot (key : LateKey setup runtime leaks) : Option Nat :=
  publicFreshSlot key.outputs key.owner (key.current.1.bindingCount key.owner)

end LateKey

/-- Silence emits nothing. -/
def silenceFactor (after : LateKey setup runtime leaks) : ℝ :=
  if after.lastEmitted = none then 1 else 0

/-- At a pending binding, the as-if-honest law commits at the canonical slot. -/
def pendingBindingHonestFactor (before after : LateKey setup runtime leaks) : ℝ :=
  match (after.lastEmitted.map fun message => message.payload.call :
      Option (Payload (graph setup))) with
  | some (.commitment _ (_, .prepared slot)) => if before.canonicalSlot =
    some slot then 1 else 0
  | _ => 0

variable [Fintype Player] (bounds : MessageBounds (graph setup))

open Classical in
/-- At a pending binding, the slot tier draws a uniform tremble slot: a
commitment has the uniform slot mass, and silence the share of rejected slots. -/
def pendingBindingSlotFactor (before after : LateKey setup runtime leaks)
    (event : (graph setup).EventId) : ℝ :=
  match after.lastEmitted with
  | none => ((trembleSlots setup bounds).filter fun slot =>
      before.slotPermitted event slot = false).card / (trembleSlots setup
        bounds).card
  | some _ => 1 / ((trembleSlots setup bounds).card : ℝ)

end Vegas

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Reads

theorem LateKey.ofView_outputs (who : Player) (past : List (application setup runtime
  leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) :
    (LateKey.ofView setup runtime leaks who past view).outputs =
      (application setup runtime leaks).outputs past := by
  simp only [LateKey.outputs, LateKey.ofView, List.filterMap_map]
  rfl

/-- After a response, the key's last emission is the response's envelope. -/
theorem LateKey.respond_lastEmitted (execution : (application setup runtime leaks).Execution)
    (who : Player) (response : (application setup runtime leaks).Action) :
    (LateKey.ofView setup runtime leaks who
      ((execution.respond (application setup runtime leaks) who response).recall who)
      ((execution.respond (application setup runtime leaks) who response).observe
        (application setup runtime leaks) who)).lastEmitted =
      response.transmission.map fun material =>
        ⟨(who, execution.network.nextSerial who), (application setup runtime leaks).packet
          ((application setup runtime leaks).submit execution.application who material)
          who (execution.network.known who) material⟩ := by
  simp only [LateKey.lastEmitted, LateKey.ofView]
  rw [runtime.respond_recall leaks execution who who response, ite_eq_left rfl,
    List.map_append, List.getLast?_append]
  rfl

variable {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
  {control : (application setup runtime leaks).Control}

/-- Along every history, the key records exactly the events the player's
recall has submitted for. -/
theorem LateKey.ofView_recorded
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) :
    (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).Recorded (runtime :=
        runtime) event ↔
      runtime.eventRecorded leaks (control.execution.recall who) event = true := by
  rw [history_eventRecorded_iff (runtime := runtime) trace who event]
  unfold LateKey.Recorded
  rw [LateKey.ofView_outputs]

/-- Along every history, the key's count verdict on a slot is the verdict on
the slot's envelope. -/
theorem LateKey.ofView_slotPermitted
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) (slot : Nat) :
    (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).slotPermitted (runtime :=
        runtime) event slot =
      countPermits ((application setup runtime leaks).outputs (control.execution.recall who))
        (slotEnvelope setup runtime leaks who (control.execution.recall who)
          (control.execution.observe (application setup runtime leaks) who) event slot) := by
  unfold LateKey.slotPermitted slotEnvelope
  rw [LateKey.ofView_outputs, history_outputs_length (runtime := runtime) trace who]
  rfl

/-- Along every history, the key's canonical slot is the player's canonical
slot. -/
theorem LateKey.ofView_canonicalSlot
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) :
    (LateKey.ofView setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who)).canonicalSlot (runtime :=
        runtime) =
      canonicalFreshSlot who
        (control.execution.observe (application setup runtime leaks) who).application := by
  rw [history_canonicalFreshSlot (runtime := runtime) trace who]
  unfold LateKey.canonicalSlot
  rw [LateKey.ofView_outputs]
  rfl

end Reads

section Masses

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- The one-packet choice sending silence is the silence choice. -/
theorem choice_eq_silenceChoice (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (past, view)))
    (chosen : choice.1 = some ⟨none⟩) :
    choice = silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who
      (some (past, view)) := by
  classical
  apply Subtype.ext
  rw [chosen]
  simp only [silenceChoice, responseChoice, bounds.silence_onePacket runtime leaks who,
    ↓reduceDIte]

/-- **Settled responses.** Along every history of the one-packet game, where the
player has no turn or its recall has submitted for its turn, a response with
positive content is silence with content one, and the as-if-honest law, the
slot tier and silence all give it mass one. -/
theorem onePacket_settled_operational_masses
    (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player)
    (settled : ∀ event, control.execution.application.publicView.ownTurn? who = some event →
      runtime.eventRecorded leaks (control.execution.recall who) event = true)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    (positive : 0 < contentFactor setup runtime leaks assessment who control.execution
      (control.execution.respond (application setup runtime leaks) who response) response)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response) :
    response = ⟨none⟩ ∧
      contentFactor setup runtime leaks assessment who control.execution
        (control.execution.respond (application setup runtime leaks) who response) response = 1 ∧
      honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice = 1 ∧
      slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice = 1 ∧
      PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who _)
        choice = 1 := by
  have silent : response = ⟨none⟩ := by
    rcases response with ⟨_ | material⟩
    · rfl
    · exfalso
      obtain ⟨event, turn, unsent, _⟩ :=
        onePacket_content_pos (runtime := runtime) assessment trace who _ member material rfl _
          positive
      rw [settled event turn] at unsent
      cases unsent
  subst silent
  have choiceEq := choice_eq_silenceChoice (runtime := runtime) who _ _ choice chosen
  subst choiceEq
  refine ⟨rfl, rfl, ?_, ?_, PMF.pure_apply_self _⟩
  · cases turn : control.execution.application.publicView.ownTurn? who with
    | none =>
        rw [honestChoice_silence_of_noTurn (runtime := runtime) assessment who _ _ turn]
        exact PMF.pure_apply_self _
    | some event =>
        rw [honestChoice_silence_of_recorded (runtime := runtime) assessment trace who event turn
          (settled event turn)]
        exact PMF.pure_apply_self _
  · cases turn : control.execution.application.publicView.ownTurn? who with
    | none =>
        rw [slotChoice_silence_of_noTurn (runtime := runtime) assessment who _ _ turn]
        exact PMF.pure_apply_self _
    | some event =>
        rw [slotChoice_silence_of_recorded (runtime := runtime) assessment trace who event turn
          (settled event turn)]
        exact PMF.pure_apply_self _

open Classical in
/-- **Operational masses at a pending binding.** Along every history of the
one-packet game, at a binding of the player's turn its recall has not submitted
for, the as-if-honest law, silence and the slot tier give a realized response
with positive content its content factor times the factors read from the
player's keys before and after the response. -/
theorem onePacket_pendingBinding_operational_masses
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : runtime.eventRecorded leaks (control.execution.recall who) event = false)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    (positive : 0 < contentFactor setup runtime leaks assessment who control.execution
      (control.execution.respond (application setup runtime leaks) who response) response)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response) :
    (honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        pendingBindingHonestFactor (runtime := runtime)
          (LateKey.ofView setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who))
          (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)) ∧
    (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who _)
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        silenceFactor (runtime := runtime) (LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who response).recall who)
          ((control.execution.respond (application setup runtime leaks) who response).observe
            (application setup runtime leaks) who)) ∧
    (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice).toReal =
      contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who response) response *
        pendingBindingSlotFactor (runtime := runtime) bounds
          (LateKey.ofView setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who))
          (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)) event := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  cases sends : response.transmission with
  | none =>
      have silent : response = ⟨none⟩ := by
        rcases response with ⟨transmission⟩
        change transmission = none at sends
        rw [sends]
      subst silent
      have choiceEq := choice_eq_silenceChoice (runtime := runtime) who _ _ choice chosen
      subst choiceEq
      have contentOne : contentFactor setup runtime leaks assessment who control.execution
          (control.execution.respond (application setup runtime leaks) who ⟨none⟩) ⟨none⟩ = 1 := rfl
      have lastNone : (LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).recall who)
          ((control.execution.respond (application setup runtime leaks) who ⟨none⟩).observe
            (application setup runtime leaks) who)).lastEmitted = none := by
        rw [LateKey.respond_lastEmitted]
        rfl
      rw [contentOne, one_mul, one_mul, one_mul]
      refine ⟨?_, ?_, ?_⟩
      · rw [honestChoice_silence_of_pending (runtime := runtime) assessment covers capacity trace
          who event turn
          unsent node, ENNReal.toReal_zero]
        unfold pendingBindingHonestFactor
        rw [lastNone]
        rfl
      · rw [PMF.pure_apply_self, ENNReal.toReal_one]
        unfold silenceFactor
        rw [lastNone]
        simp
      · rw [slotChoice_silence_of_pending (runtime := runtime) assessment covers capacity trace
          who event turn node]
        unfold pendingBindingSlotFactor
        rw [lastNone]
        dsimp only
        rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
        congr 3
        ext slot
        simp only [Finset.mem_filter, LateKey.ofView_slotPermitted rawTrace
          who event slot]
  | some material =>
      obtain ⟨serial, canonical, _, selected, ⟨value, responseEq⟩, honestMass, slotMass,
        silenceMass⟩ := onePacket_binding_transmission_masses (runtime := runtime) assessment
          covers capacity trace who
          event turn node response member material sends positive choice chosen
      obtain ⟨delivered, transmits, envelope⟩ := slotResponse_transmission setup runtime leaks who
        (control.execution.recall who) (control.execution.observe (application setup runtime
          leaks) who)
        event node serial (sourceOfValue setup event outputEq value) _
        (sourceOfValue_encoded setup event outputEq codeEq value)
      rw [← responseEq, sends] at transmits
      cases Option.some.inj transmits
      have packetEq : material.call.packet = .commitment event (who, .prepared serial) :=
        congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
          message.payload.call) envelope
      have lastSome : (LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who response).recall who)
          ((control.execution.respond (application setup runtime leaks) who response).observe
            (application setup runtime leaks) who)).lastEmitted ≠ none := by
        rw [LateKey.respond_lastEmitted, sends]
        exact Option.some_ne_none _
      have lastCall : ((LateKey.ofView setup runtime leaks who
          ((control.execution.respond (application setup runtime leaks) who response).recall who)
          ((control.execution.respond (application setup runtime leaks) who response).observe
            (application setup runtime leaks) who)).lastEmitted.map fun
              message => message.payload.call :
            Option (Payload (graph setup))) = some (.commitment event (who, .prepared serial)) := by
        rw [LateKey.respond_lastEmitted, sends]
        exact congrArg some packetEq
      have canonicalEq := (LateKey.ofView_canonicalSlot rawTrace who).trans
        selected
      refine ⟨?_, ?_, ?_⟩
      · rw [honestMass]
        congr 1
        unfold pendingBindingHonestFactor
        rw [lastCall, canonicalEq]
        dsimp only
        rcases eq_or_ne serial canonical with same | different
        · subst same
          simp
        · simp [different, different.symm]
      · rw [silenceMass]
        congr 1
        unfold silenceFactor
        simp [lastSome]
      · rw [slotMass]
        congr 1
        unfold pendingBindingSlotFactor
        cases last : (LateKey.ofView setup runtime leaks who
            ((control.execution.respond (application setup runtime leaks) who response).recall who)
            ((control.execution.respond (application setup runtime leaks) who response).observe
              (application setup runtime leaks) who)).lastEmitted with
        | none => exact absurd last lastSome
        | some _ => rfl

end Masses

end Vegas
