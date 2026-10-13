/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateLumping
import Vegas.Game.OnePacketBindingSite
import Vegas.Game.OnePacketLateMasses

/-! # The owner's law of moves for slot-trembled late components

At a pending binding of the owner's turn along a one-packet history, the
response committing a covered source choice at a slot within capacity moves as
the slot does: when the count verdict permits the slot's envelope, it commits at
the slot with a successful candidate, and otherwise it keeps silence
(`Vegas.commitMove_slotChoiceOf`). The move does not depend on the value.

So a slot-trembled late component, sorted into moves, is within the cube of the
scale of the mixture of its slot tier, silence and late options read as slot
moves (`Vegas.lateComponent_moves_close`). Slot moves are read off the
operational state (`Vegas.slotMove_congr`), so when the owner plays such
components keyed by its late-delivery key, its law of moves is within the cube
of the scale of a keyed law (`Vegas.ownerBindingLaw_of_lateComponents`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **A permitted envelope is first for its event.** Along every history of
the one-packet game, when the count verdict permits a commitment of the player
for an event, the player has no pending commitment to it. -/
theorem commitStatuses_nil_of_permitted {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) (slot : Nat)
    (permitted : countPermits ((application setup leaks).outputs (control.execution.recall who))
      (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot) = true)
    (payload : L.Ty) :
    commitStatuses event who payload control.execution.application
      control.execution.network.pending = [] := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := (runtime setup).countRecall_history leaks rawTrace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
  have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
  unfold commitStatuses
  rw [List.filterMap_eq_nil_iff]
  intro message member
  unfold commitStatus
  split
  · rename_i named candidate call
    split
    · rename_i owned
      exfalso
      obtain ⟨namedEq, sender⟩ := owned
      have input : message ∈ control.execution.network.inputs :=
        facts.carried.pending message member
      have output : message ∈ (application setup leaks).outputs
          (control.execution.recall who) := by
        rw [← recalled.1 who]
        exact List.mem_filter.mpr ⟨input, by simp [sender]⟩
      obtain ⟨inOutputs, owner, lower⟩ := earlierOwnPacket_of_output rawTrace who
        (slotEnvelope setup leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event slot).payload
        message output
      apply first message ⟨inOutputs, owner, ?_⟩
      · rw [call, namedEq]
        rfl
      · change message.id.2 < (application setup leaks).submissionCount
          (control.execution.recall who)
        rw [← recalled.2.1 who]
        exact lower
    · rfl
  · rfl

omit [Fintype Player] in
/-- A commitment to the binding at a handle whose candidate succeeds, made with
no pending commitment of the owner to it, moves to that handle. -/
theorem commitMove_eq_some {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    {execution : (application setup leaks).Execution} {action : (application setup leaks).Action}
    {submission : (application setup leaks).Submission} {candidate : Handle (graph setup)}
    (sent : action.transmission = some submission)
    (call : submission.call.packet = .commitment event candidate)
    (succeeds : candidateSucceeds ((application setup leaks).submit execution.application owner
      submission) candidate payload = true)
    (empty : commitStatuses event owner payload execution.application
      execution.network.pending = []) :
    commitMove event owner payload execution action = some (some candidate) := by
  have committed : ∃ (submission : (application setup leaks).Submission)
      (candidate : Handle (graph setup)), action.transmission = some submission ∧
      submission.call.packet = .commitment event candidate ∧
      candidateSucceeds ((application setup leaks).submit execution.application owner
        submission) candidate payload = true ∧
      commitStatuses event owner payload execution.application execution.network.pending = [] :=
    ⟨submission, candidate, sent, call, succeeds, empty⟩
  have notSilent : ¬ action.transmission = none := by
    rw [sent]
    exact Option.some_ne_none _
  unfold commitMove
  simp only [notSilent, ↓reduceIte, dite_eq_left committed]
  obtain ⟨chosenSent, chosenCall, _, _⟩ := committed.choose_spec.choose_spec
  have same : submission = committed.choose := Option.some.inj (sent.symm.trans chosenSent)
  have callEq : Payload.commitment event candidate =
      Payload.commitment event committed.choose_spec.choose := by
    rw [← call, same]
    exact chosenCall
  rw [(Payload.commitment.inj callEq).2]

omit [Fintype Player] in
/-- Silence moves to silence. -/
theorem commitMove_silent {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (execution : (application setup leaks).Execution) :
    commitMove event owner payload execution ⟨none⟩ = some none := by
  unfold commitMove
  rfl

/-- The move of committing at a slot: to the slot's handle when the count
verdict permits its envelope, and silence otherwise. -/
def slotMove (execution : (application setup leaks).Execution) (who : Player)
    (event : (graph setup).EventId) (slot : Nat) : Option (Handle (graph setup)) :=
  if countPermits ((application setup leaks).outputs (execution.recall who))
      (slotEnvelope setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event slot) = true then
    some (who, .prepared slot)
  else none

/-- **The move of a slot-tier choice.** Along every history of the one-packet
game, at a covered pending binding of the player's turn, committing an
as-if-honest source choice at a slot within capacity moves as the slot does. -/
theorem commitMove_slotChoiceOf {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event payload outputEq codeEq)
    (slot : Nat) (capacity : slot < bounds.candidateCount) (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support) :
    commitMove event who payload control.execution
        ((slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
          (control.execution.recall who) (control.execution.observe (application setup leaks) who)
          event slot choice).1.getD ⟨none⟩) =
      some (slotMove control.execution who event slot) := by
  have covered := site.covered choice supported
  have membership := slotResponse_mem_onePacket_iff setup leaks bounds who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) event
    site.node slot capacity choice covered
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq site.node
  unfold slotMove
  by_cases permitted : countPermits ((application setup leaks).outputs
      (control.execution.recall who)) (slotEnvelope setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot) = true
  · have member := membership.mpr permitted
    simp only [permitted, ↓reduceIte]
    have chosen : (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event slot choice).1 = some (slotResponse setup leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event slot choice) := by
      simp only [slotChoiceOf, responseChoice, member, ↓reduceDIte]
    rw [chosen, Option.getD_some]
    obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
      event site.node slot choice action encoded
    have call : material.call.packet = .commitment event (who, .prepared slot) :=
      congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
        message.payload.call) envelope
    have bound := slotResponse_of_bind setup leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event site.node slot choice
      action encoded
    rw [bound] at transmits
    have materialEq := Option.some.inj transmits.symm
    have submitted : (application setup leaks).submit control.execution.application who material =
        (control.execution.respond (application setup leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
            .none⟩⟩).application := by
      rw [materialEq]
      change (application setup leaks).submit control.execution.application who
        (((runtime setup).reactiveNormalization leaks).normalize who
          ((application setup leaks).observePlayer control.execution.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
            (control.execution.observe (application setup leaks) who))
          ⟨⟨.commitment event (who, .prepared slot), match (cast (congrArg
            EventGraph.EventField.Action outputEq) action : PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩) = _
      rw [((runtime setup).reactiveNormalization leaks).submit, successful]
      rfl
    have fresh : control.execution.application.candidates.lookup (who, .prepared slot) = .fresh :=
      site.freshOfPermitted slot permitted
    have result := submitted_bindingResult (runtime setup) leaks control.execution who event
      payload slot (some ⟨payload, value⟩) fresh
    apply commitMove_eq_some (submission := material) (by rw [bound]; exact transmits) call
    · unfold candidateSucceeds
      rw [submitted]
      change (match (control.execution.respond (application setup leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
            .none⟩⟩).application.bindingResult (who, .prepared slot) payload with
        | .success _ => true
        | .failure => false) = true
      rw [result]
      simp [Raw.as?]
    · exact commitStatuses_nil_of_permitted trace who event slot permitted payload
  · have notMember : slotResponse setup leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event slot choice ∉
        bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) :=
      fun member => permitted (membership.mp member)
    simp only [permitted, Bool.false_eq_true, ↓reduceIte]
    have chosen : (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event slot choice).1 = some ⟨none⟩ := by
      simp only [slotChoiceOf, responseChoice, notMember, ↓reduceDIte]
    rw [chosen, Option.getD_some]
    exact commitMove_silent control.execution

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
/-- A mixture with weight `t` on a law is `t`-close on unit payoffs to its
other part. -/
theorem unitClose_mix {α : Type} (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : PMF α) :
    UnitClose t (mix t h0 h1 μ ν) ν := by
  intro f unit
  have bound : ∀ a, |f a| ≤ 1 := fun a =>
    abs_le.mpr ⟨by linarith [(unit a).1], (unit a).2⟩
  rw [expect_mix t h0 h1 μ ν f (payoffIntegrable_of_bounded μ f bound)
    (payoffIntegrable_of_bounded ν f bound)]
  have first := expect_mem_unit μ f unit
  have second := expect_mem_unit ν f unit
  have difference : t * expect μ f + (1 - t) * expect ν f - expect ν f =
      t * (expect μ f - expect ν f) := by ring
  rw [difference, abs_mul, abs_of_nonneg h0]
  have : |expect μ f - expect ν f| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
/-- The first coordinate of a product law built as a bind is the first law. -/
private theorem bind_map_pair_map_fst_eq {α β : Type} (first : PMF α) (second : PMF β) :
    (first.bind fun x => second.map (Prod.mk x)).map Prod.fst = first := by
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure first]
  congr 1
  funext x
  rw [PMF.map_comp]
  exact PMF.map_const _ _

/-- The silence choice decodes to silence. -/
theorem silenceChoice_val (who : Player) (info : (application setup leaks).Info)
    (active : info.isSome) :
    (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who info).1 =
      some ⟨none⟩ := by
  rcases info with _ | ⟨past, view⟩
  · cases active
  · unfold silenceChoice responseChoice
    dsimp only
    split <;> rfl

/-- The moves of a slot-trembled late component at an execution, apart from its
uniform tier: the slot tier's moves with weight the square of the scale, then
silence with weight the scale, then the moves of the late options. -/
def lateMoves (execution : (application setup leaks).Execution) (who : Player)
    (event : (graph setup).EventId) (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {slots : Nat} (options : PMF (LateOption slots)) : PMF (Option (Handle (graph setup))) :=
  mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
    ((PMF.uniformOfFinset (trembleSlots setup bounds) (trembleSlots_nonempty setup bounds)).map
      (slotMove execution who event))
    (mix scale nonnegative le_one (PMF.pure none)
      (options.map fun option => option.elim none fun slot =>
        slotMove execution who event slot.val))

/-- **The moves of a slot-trembled late component.** Along every history of the
one-packet game, at a covered pending binding of the player's turn, a
slot-trembled component of a mixture of late options over slots within capacity,
with silence as its alternative and the slot tier, sorted into moves, is within
the cube of the scale of the component's moves. -/
theorem lateComponent_moves_close {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event payload outputEq codeEq)
    {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount) (options : PMF (LateOption slots))
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    UnitClose (scale ^ 3)
      ((slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
          nonnegative le_one who (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))
          (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
            assessment who (some (control.execution.recall who,
              control.execution.observe (application setup leaks) who))))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            (some (control.execution.recall who,
              control.execution.observe (application setup leaks) who))))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
            (some (control.execution.recall who,
              control.execution.observe (application setup leaks) who)))).map
        fun choice => commitMove event who payload control.execution (choice.1.getD ⟨none⟩))
      ((lateMoves (bounds := bounds) control.execution who event scale nonnegative le_one
        options).map some) := by
  set past := control.execution.recall who
  set view := control.execution.observe (application setup leaks) who
  set sort : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      (some (past, view)) → Option (Option (Handle (graph setup))) :=
    fun choice => commitMove event who payload control.execution (choice.1.getD ⟨none⟩)
    with sortEq
  have slotSorted : ∀ slot, slot < bounds.candidateCount →
      ∀ choice ∈ (asIfHonestProfile setup leaks assessment who (some (past, view))).support,
        sort (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who past view
          event slot choice) = some (slotMove control.execution who event slot) :=
    fun slot capacity choice supported =>
      commitMove_slotChoiceOf trace assessment who event site slot capacity choice supported
  have silenceSorted : sort (silenceChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who (some (past, view))) = some none := by
    simp only [sort, silenceChoice_val who (some (past, view)) rfl, Option.getD_some]
    exact commitMove_silent control.execution
  have slotTier : (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
      who (some (past, view))).map sort =
      ((PMF.uniformOfFinset (trembleSlots setup bounds) (trembleSlots_nonempty setup bounds)).map
        (slotMove control.execution who event)).map some := by
    rw [slotChoice_eq_map (initial := initialLaw setup) (horizon := horizon)
        (scheduler := scheduler) site.turn, PMF.map_comp, PMF.map_comp]
    have pairs : PMF.uniformOfFinset (trembleSlots setup bounds)
        (trembleSlots_nonempty setup bounds) =
        (slotPairs setup leaks bounds assessment who past view).map Prod.fst :=
      (bind_map_pair_map_fst_eq _ _).symm
    rw [pairs, PMF.map_comp]
    apply map_congr_on_support
    intro pair supported
    unfold slotPairs at supported
    obtain ⟨slot, chosen, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨choice, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
    have capacity : slot < bounds.candidateCount :=
      (mem_trembleSlots_iff setup bounds site.capacity slot).mp
        ((PMF.mem_support_uniformOfFinset_iff _ _).mp chosen)
    exact slotSorted slot capacity choice drawn
  have mainTier : (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon
      scheduler assessment who (some (past, view)))).map sort =
      (options.map fun option => option.elim none fun slot =>
        slotMove control.execution who event slot.val).map some := by
    rw [PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp]
    congr 1
    funext option
    cases option with
    | none =>
        rw [lateChoice_none, PMF.pure_map, silenceSorted]
        rfl
    | some slot =>
        rw [lateChoice_some_eq_map (bounds := bounds) (initial := initialLaw setup)
          (horizon := horizon) (scheduler := scheduler) assessment who past view event site.turn
          slot, PMF.map_comp]
        have constant : (asIfHonestProfile setup leaks assessment who (some (past, view))).map
            (sort ∘ slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who past
              view event slot.val) =
            (asIfHonestProfile setup leaks assessment who (some (past, view))).map
              (Function.const _ (some (slotMove control.execution who event slot.val))) :=
          map_congr_on_support _ fun choice supported =>
            slotSorted slot.val (lt_of_lt_of_le slot.isLt slotsLe) choice supported
        rw [constant, PMF.map_const]
        rfl
  have rest : (mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
      (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (past, view)))
      (mix scale nonnegative le_one
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (past, view))))
        (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
          assessment who (some (past, view)))))).map sort =
      (lateMoves (bounds := bounds) control.execution who event scale nonnegative le_one
        options).map some := by
    rw [mix_map, mix_map, slotTier, mainTier, PMF.pure_map, silenceSorted]
    unfold lateMoves
    rw [mix_map, mix_map, PMF.pure_map]
  unfold slotTrembledChoice
  rw [mix_map, rest]
  exact unitClose_mix _ _ _ _ _

/-- The decoded native policy of a menu profile reads the chosen action. -/
theorem decodeProfile_eq_map
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile who past view =
      (profile who (some (past, view))).map fun choice => choice.1.getD ⟨none⟩ := by
  unfold ReactiveApplication.ResponseMenu.decodeProfile ReactiveApplication.decodePolicy
    ReactiveApplication.ResponseMenu.embedPolicy
  rw [PMF.map_comp]
  rfl

omit [Fintype Player] in
/-- Protocol states with the same operational state give every player the same
late-delivery key. -/
theorem ofView_congr {first second : (application setup leaks).Control}
    (same : operationalState setup leaks (some first) = operationalState setup leaks (some second))
    (who : Player) :
    LateKey.ofView setup leaks who (first.execution.recall who)
        (first.execution.observe (application setup leaks) who) =
      LateKey.ofView setup leaks who (second.execution.recall who)
        (second.execution.observe (application setup leaks) who) :=
  Option.some.inj (congrFun (congrArg OperationalState.keys (Option.some.inj same)) who)

/-- **Slot moves are read off the operational state.** At states of one-packet
histories with the same operational state, every slot moves alike. -/
theorem slotMove_congr {remaining : Nat} {actor : Option Player}
    (firstHistory secondHistory : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {first second : (application setup leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining, actor, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining, actor, second⟩)
    (same : operationalState setup leaks (some ⟨remaining, actor, first⟩) =
      operationalState setup leaks (some ⟨remaining, actor, second⟩))
    (who : Player) (event : (graph setup).EventId) :
    slotMove first who event = slotMove second who event := by
  have serial (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      {execution : (application setup leaks).Execution}
      (current : history.state = some ⟨remaining, actor, execution⟩) :
      (application setup leaks).submissionCount (execution.recall who) =
        execution.network.nextSerial who := by
    have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some ⟨remaining, actor, execution⟩) :=
      current ▸ (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
        scheduler history.trace
    exact (((runtime setup).countRecall_history leaks rawTrace).2.1 who).symm
  have keys := ofView_congr same who
  have recalled := congrArg LateKey.recalled keys
  simp only [LateKey.ofView] at recalled
  have emitted := congrArg (List.map Prod.snd) recalled
  simp only [List.map_map, Function.comp_def] at emitted
  have viaMap : ∀ entries : List (application setup leaks).PlayerEntry,
      entries.filterMap ReactiveApplication.PlayerEntry.emitted =
        (entries.map fun entry => entry.emitted).filterMap id := by
    intro entries
    rw [List.filterMap_map]
    rfl
  have outputs : (application setup leaks).outputs (first.recall who) =
      (application setup leaks).outputs (second.recall who) := by
    unfold ReactiveApplication.outputs
    rw [viaMap, viaMap, emitted]
  have publics : first.application.publicView = second.application.publicView :=
    SameOperational.publicView same
  have networks : first.network = second.network := SameOperational.network same
  have envelope : ∀ slot, slotEnvelope setup leaks who (first.recall who)
      (first.observe (application setup leaks) who) event slot =
      slotEnvelope setup leaks who (second.recall who)
        (second.observe (application setup leaks) who) event slot := by
    intro slot
    unfold slotEnvelope
    have tokens : (first.observe (application setup leaks) who).application.publicView =
        (second.observe (application setup leaks) who).application.publicView := publics
    rw [serial firstHistory firstCurrent, serial secondHistory secondCurrent, networks, tokens]
  funext slot
  unfold slotMove
  rw [outputs, envelope slot]

omit [Fintype Player] in
/-- A key decides at most one binding event, with one payload type. -/
theorem bindingTurn_of_bindingTurn {key : LateKey setup leaks} {event : (graph setup).EventId}
    {payload : L.Ty} (turn : BindingTurn key event payload) :
    bindingTurn key = some (event, payload) := by
  have exists_ : ∃ decided : (graph setup).EventId × L.Ty, BindingTurn key decided.1 decided.2 :=
    ⟨(event, payload), turn⟩
  unfold bindingTurn
  rw [dite_eq_left exists_]
  obtain ⟨chosenTurn, ⟨chosenOutput, chosenCode, chosenNode⟩, _⟩ := exists_.choose_spec
  obtain ⟨ownTurn, ⟨outputEq, codeEq, node⟩, _⟩ := turn
  rw [ownTurn] at chosenTurn
  have sameEvent := Option.some.inj chosenTurn
  apply congrArg some
  apply Prod.ext
  · exact sameEvent.symm
  · have kinds : (EventGraph.EventField.binding key.owner exists_.choose.2 :
        EventGraph.EventField Player L) = .binding key.owner payload := by
      rw [← chosenOutput, ← sameEvent]
      exact outputEq
    exact (EventGraph.EventField.binding.inj kinds).2

variable (bounds horizon scheduler) in
open Classical in
/-- **The keyed law of moves.** At a key deciding a binding, the moves of the
slot-trembled late component at a representative state of a one-packet history
with the given operational state and statuses, the owner acting; silence when
there is none. -/
def lateBindingMoves {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup leaks → PMF (LateOption slots)) (key : LateKey setup leaks)
    (image : Option (OperationalState setup leaks) × List (MessageId Player × Bool)) :
    PMF (Option (Handle (graph setup))) :=
  match bindingTurn key with
  | none => PMF.pure none
  | some decided =>
      if represented : ∃ witness : (onePacketProtocol setup leaks bounds horizon
          scheduler).History × Nat × (application setup leaks).Execution,
          witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
          (operationalState setup leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩),
            commitStatuses decided.1 key.owner decided.2 witness.2.2.application
              witness.2.2.network.pending) = image then
        lateMoves (bounds := bounds) represented.choose.2.2 key.owner decided.1 scale nonnegative
          le_one (options (LateKey.ofView setup leaks key.owner
            (represented.choose.2.2.recall key.owner)
            (represented.choose.2.2.observe (application setup leaks) key.owner)))
      else PMF.pure none

/-- **The owner's law of moves for late components.** Suppose that at every
forced state of a one-packet history with the decided binding ready and the
owner acting, the owner's policy is the slot-trembled component, with silence as
its alternative and the slot tier, of a mixture of late options over slots
within capacity chosen by the owner's late-delivery key. When every binding value
is a bounded value and the capacity is at least one, the owner's law of moves
is within the cube of the scale of the keyed law of moves. -/
theorem ownerBindingLaw_of_lateComponents {LateOption' : Type}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup leaks → LateOption' → LateKey setup leaks →
      PMF (LateOption slots))
    (key : LateKey setup leaks) (option : LateOption')
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {allowed : (application setup leaks).ProtocolState → Prop}
    (shape : ∀ event payload, BindingTurn key event payload →
      ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
        (remaining : Nat) (execution : (application setup leaks).Execution),
        history.state = some ⟨remaining, some key.owner, execution⟩ →
        allowed history.state →
        ForcedState setup leaks key.owner history.state →
        execution.application.config.cut.Ready event →
        profile key.owner (some (execution.recall key.owner,
            execution.observe (application setup leaks) key.owner)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one key.owner (some (execution.recall key.owner,
              execution.observe (application setup leaks) key.owner))
            ((options key option (LateKey.ofView setup leaks key.owner
                (execution.recall key.owner)
                (execution.observe (application setup leaks) key.owner))).bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup leaks) key.owner))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup leaks) key.owner))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup leaks) key.owner)))) :
    OwnerBindingLaw bounds horizon scheduler
      (fun key option => lateBindingMoves bounds horizon scheduler scale nonnegative le_one
        (options key option) key) key option profile (scale ^ 3) allowed := by
  intro event payload turn history remaining execution current allowedState forced ready
  have decided := bindingTurn_of_bindingTurn turn
  obtain ⟨_, ⟨outputEq, codeEq, node⟩, _⟩ := turn
  have trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some key.owner, execution⟩) := current ▸ history.trace
  have site := onePacket_coveredPendingBinding assessment covers capacity trace key.owner event
    (ownTurn?_of_ready setup _ ready (nodeView_bind_actor outputEq codeEq)) node
  have close := lateComponent_moves_close trace assessment key.owner event site slotsLe
    (options key option (LateKey.ofView setup leaks key.owner (execution.recall key.owner)
      (execution.observe (application setup leaks) key.owner))) scale nonnegative le_one
  rw [decodeProfile_eq_map, PMF.map_comp,
    shape event payload ⟨‹_›, ⟨outputEq, codeEq, node⟩, ‹_›⟩ history remaining execution current
      allowedState forced ready]
  have represented : ∃ witness : (onePacketProtocol setup leaks bounds horizon
      scheduler).History × Nat × (application setup leaks).Execution,
      witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
      (operationalState setup leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩),
        commitStatuses event key.owner payload witness.2.2.application
          witness.2.2.network.pending) =
      (operationalState setup leaks (some ⟨remaining, some key.owner, execution⟩),
        commitStatuses event key.owner payload execution.application
          execution.network.pending) :=
    ⟨(history, remaining, execution), current, rfl⟩
  have movesEq : lateBindingMoves bounds horizon scheduler scale nonnegative le_one
      (options key option) key
      (operationalState setup leaks (some ⟨remaining, some key.owner, execution⟩),
        commitStatuses event key.owner payload execution.application
          execution.network.pending) =
      lateMoves (bounds := bounds) execution key.owner event scale nonnegative le_one
        (options key option (LateKey.ofView setup leaks key.owner (execution.recall key.owner)
          (execution.observe (application setup leaks) key.owner))) := by
    unfold lateBindingMoves
    rw [decided]
    simp only
    rw [dite_eq_left represented]
    have spec := represented.choose_spec
    generalize represented.choose = witness at spec ⊢
    obtain ⟨chosenHistory, chosenRemaining, chosenExecution⟩ := witness
    obtain ⟨chosenCurrent, chosenImage⟩ := spec
    have same := (Prod.mk.inj chosenImage).1
    have remainingEq : chosenRemaining = remaining := SameOperational.remaining same
    subst remainingEq
    have moves := slotMove_congr chosenHistory history chosenCurrent current same key.owner event
    have keys := ofView_congr same key.owner
    simp only at moves keys ⊢
    unfold lateMoves
    rw [moves, keys]
  beta_reduce
  rw [movesEq]
  exact close

end Vegas
