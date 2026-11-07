/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockClosure

/-! # A block of concurrent reveals on the graph

When the deviator is served last, the graph run of a block of concurrent
reveals first completes every honest reveal of the block, each opened exactly
when its opening is accepted. These completions are point masses, so the
last-served erased-key law at the start of the block is that law after them.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode}

/-- An honest effective opening completes a ready reveal with its exact record:
an accepted opening, or a withholding whose failure defaults its owner. -/
theorem honest_complete_records {who : Player}
    {config : (serviceGraph setup mode).Config} {event : (serviceGraph setup mode).EventId}
    (ready : config.cut.Ready event) {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (honest : owner ≠ who) (active : owner ∉ config.defaulted) :
    ∃ value, config.step event ready (cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event config.store)) =
      PMF.pure (config.complete event ready (cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event config.store)) value) ∧
      (HonestOpened who (config.complete event ready (cast (congrArg EventField.Action
          outputEq.symm) (openingAccepted event config.store)) value) event ∨
        HonestExpired who (config.complete event ready (cast (congrArg EventField.Action
          outputEq.symm) (openingAccepted event config.store)) value) event) := by
  have available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (config.store field).isSome := fun field read => config.read_available ready read
  have keep (action : (serviceGraph setup mode).Action event)
      (value : ((serviceGraph setup mode).outputLayout event).Value) :
      ∀ field stored, config.store field = some stored →
        (config.complete event ready action value).store field = some stored :=
    fun field stored found => config.complete_store_of_some event ready action value field
      stored found
  have availableAfter (action : (serviceGraph setup mode).Action event)
      (value : ((serviceGraph setup mode).outputLayout event).Value) :
      ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
        ((config.complete event ready action value).store field).isSome := by
    intro field read
    obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp (available field read)
    rw [keep action value field stored found]
    rfl
  have acceptedAfter (action : (serviceGraph setup mode).Action event)
      (value : ((serviceGraph setup mode).outputLayout event).Value) :
      openingAccepted event (config.complete event ready action value).store =
        openingAccepted event config.store := by
    apply openingAccepted_congr event
    intro field read
    obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp (available field read)
    rw [keep action value field stored found, found]
  have recorded (action : (serviceGraph setup mode).Action event)
      (value : ((serviceGraph setup mode).outputLayout event).Value) :
      completionOf (config.complete event ready action value) event =
        some (EventGraph.completion (serviceGraph setup mode) event
          (config.actualDecision event action) value) := by
    rw [completionOf_complete, Function.update_self]
  cases acceptedEq : openingAccepted event config.store
  · refine ⟨cast (congrArg EventField.Value outputEq.symm) (PublicationResult.failure),
      step_of_opening_rejected config event ready node acceptedEq _, Or.inr ⟨owner, payload,
        binding, checks, outputEq, codeEq, honest, node, availableAfter _ _, ?_, ?_, ?_⟩⟩
    · rw [acceptedAfter, acceptedEq]
    · rw [recorded, completion_resolve_eq config event outputEq codeEq active false .failure]
      rfl
    · exact config.complete_output_same event ready _ _
  · obtain ⟨opened, resolved⟩ := resolveOutput_of_accepted node acceptedEq
    refine ⟨cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success opened),
      resolve_step_eq ready outputEq codeEq active true (.success opened) resolved,
      Or.inl ⟨owner, payload, binding, checks, outputEq, codeEq, honest, node,
        availableAfter _ _, ?_, ?_, ?_⟩⟩
    · rw [acceptedAfter, acceptedEq]
    · rw [recorded, completion_resolve_eq config event outputEq codeEq active true
        (.success opened)]
      rfl
    · rw [config.complete_output_same event ready _ _,
        resolveOutput_keep (keep _ _) (outputEq := outputEq) codeEq available, resolved]
      rfl

/-- **The honest reveals of a block come first on the graph.** Under a
profile whose honest owners open a block reveal exactly when its opening is
accepted, the last-served erased-key law inside a flat block equals that law
after completing every honest block reveal, each with its exact record. -/
theorem lastErasedLaw_honest_block {who : Player} {start finish : Nat}
    (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (honestLaw : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      owner ≠ who → owner ∉ config.defaulted →
        actionLaw profile config event = PMF.pure (cast (congrArg EventField.Action
          outputEq.symm) (openingAccepted event config.store)))
    (origin : (serviceGraph setup mode).Config) :
    ∀ (count : Nat) (current : (serviceGraph setup mode).Config), current.remaining = count →
      InBlock start finish current →
      Relation.ReflTransGen Config.Step origin current →
      BlockRecordsSound who start finish origin current →
      (∀ event : (serviceGraph setup mode).EventId, start ≤ event.val → event.val < finish →
        event ∉ current.cut.completed → ∀ owner,
          (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
            owner ∉ current.defaulted) →
      ∃ final : (serviceGraph setup mode).Config,
        Relation.ReflTransGen Config.Step current final ∧ InBlock start finish final ∧
        Relation.ReflTransGen Config.Step origin final ∧
        BlockRecordsSound who start finish origin final ∧
        lastErasedLaw profile who current = lastErasedLaw profile who final ∧
        (∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
          event.val < finish → event ∉ final.cut.completed →
            (serviceGraph setup mode).actor? event = some who) ∧
        (∀ event, event ∈ final.cut.completed → event ∈ current.cut.completed ∨
          (start ≤ event.val ∧ event.val < finish ∧
            (serviceGraph setup mode).actor? event ≠ some who)) ∧
        (who ∈ final.defaulted → who ∈ current.defaulted) := by
  intro count
  induction count using Nat.strong_induction_on with
  | _ count ih =>
  intro current counted inside path sound active
  by_cases pendingHonest : ∃ event : (serviceGraph setup mode).EventId, start ≤ event.val ∧
      event.val < finish ∧ event ∉ current.cut.completed ∧
      (serviceGraph setup mode).actor? event ≠ some who
  swap
  · push Not at pendingHonest
    exact ⟨current, .refl, inside, path, sound, rfl,
      fun event early late pending => pendingHonest event early late pending,
      fun event done => Or.inl done, id⟩
  obtain ⟨witness, witnessEarly, witnessLate, witnessPending, witnessHonest⟩ := pendingHonest
  have witnessReady := flat.ready inside witnessEarly witnessLate witnessPending
  have notTerminal : ¬ current.cut.Terminal := by
    intro terminal
    apply witnessReady.1
    rw [terminal]
    exact Finset.mem_univ _
  have nonempty := enabled_nonempty_of_not_terminal current notTerminal
  let picked := (serviceGraph setup mode).lastPick who current.cut.enabled nonempty
  have pickedReady : current.cut.Ready picked :=
    (EventOrder.Cut.mem_enabled _ _).mp ((serviceGraph setup mode).lastPick_mem who _ nonempty)
  have pickedHonest : (serviceGraph setup mode).actor? picked ≠ some who :=
    (serviceGraph setup mode).lastPick_other who nonempty
      ((EventOrder.Cut.mem_enabled _ _).mpr witnessReady) witnessHonest
  have running : ¬ BlockDone finish current := fun done => witnessPending (done witness witnessLate)
  have pickedBounds := shaped current inside running picked pickedReady
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication (publications picked pickedBounds.1 pickedBounds.2)
  have owned := nodeView_resolve_actor outputEq codeEq
  have honest : owner ≠ who := fun same => pickedHonest (same ▸ owned)
  have ownerActive := active picked pickedBounds.1 pickedBounds.2 pickedReady.1 owner owned honest
  obtain ⟨value, stepEq, records⟩ :=
    honest_complete_records (who := who) pickedReady node honest ownerActive
  let action := cast (congrArg EventField.Action outputEq.symm)
    (openingAccepted picked current.store)
  let next := current.complete picked pickedReady action value
  have member : next ∈ (current.step picked pickedReady action).support := by
    rw [stepEq, PMF.support_pure]
    rfl
  have moved : Config.Step current next := ⟨picked, pickedReady, action, member⟩
  have lawEq : lastErasedLaw profile who current = lastErasedLaw profile who next := by
    unfold lastErasedLaw
    rw [lastRun_step profile who current notTerminal picked pickedReady rfl, PMF.map_bind]
    unfold eventStep
    rw [honestLaw current picked owner payload binding checks outputEq codeEq node honest
      ownerActive, PMF.pure_bind, stepEq, PMF.pure_bind]
  have smaller : next.remaining < count := by
    have consumed := current.remaining_step picked pickedReady action next member
    omega
  have nextInside : InBlock start finish next := by
    refine ⟨fun event early => Config.Step.path_completed_mono (.single moved)
      (inside.1 event early), fun event late done => ?_⟩
    rw [Config.complete_cut, EventOrder.Cut.mem_complete] at done
    rcases done with same | old
    · subst same
      omega
    · exact inside.2 event late old
  have nextSound : BlockRecordsSound who start finish origin next := by
    intro event fresh done
    by_cases same : event = picked
    · subst same
      exact Or.inr ⟨pickedBounds.1, pickedBounds.2, Or.inr records⟩
    · have old : event ∈ current.cut.completed := by
        rw [Config.complete_cut, EventOrder.Cut.mem_complete] at done
        exact done.resolve_left same
      exact BlockRecordsSound.path (.single moved) sound event fresh old
  have nextActive : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ next.cut.completed → ∀ other,
        (serviceGraph setup mode).actor? event = some other → other ≠ who →
          other ∉ next.defaulted := by
    intro event early late pending other otherOwned otherHonest
    have pendingNow : event ∉ current.cut.completed := fun done =>
      pending (Config.Step.path_completed_mono (.single moved) done)
    have different : event ≠ picked := fun same => by
      subst same
      apply pending
      rw [Config.complete_cut, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    have eventReady := flat.ready inside early late pendingNow
    have actorsDiffer : (serviceGraph setup mode).actor? picked ≠ some other := by
      intro pickedOther
      rcases concurrent current.cut pickedReady eventReady (Ne.symm different) with
        independent | independent
      · exact independent.2.2.2 (pickedOther.trans otherOwned.symm)
      · exact independent.2.2.2 (otherOwned.trans pickedOther.symm)
    rw [EventGraph.mem_defaulted_complete_of_actor_ne current picked pickedReady action value other
      actorsDiffer]
    exact active event early late pendingNow other otherOwned otherHonest
  obtain ⟨final, finalPath, finalInside, originPath, finalSound, finalLaw, finalPending,
      finalNew, finalWho⟩ :=
    ih next.remaining smaller next rfl nextInside (path.tail moved) nextSound nextActive
  refine ⟨final, Relation.ReflTransGen.head moved finalPath, finalInside, originPath,
    finalSound, lawEq.trans finalLaw, finalPending, fun event done => ?_, fun defaulted => ?_⟩
  · rcases finalNew event done with old | fresh
    · rw [Config.complete_cut, EventOrder.Cut.mem_complete] at old
      rcases old with same | earlier
      · subst same
        exact Or.inr ⟨pickedBounds.1, pickedBounds.2, pickedHonest⟩
      · exact Or.inl earlier
    · exact Or.inr fresh
  · exact (EventGraph.mem_defaulted_complete_of_actor_ne current picked pickedReady action value who
      pickedHonest).mp (finalWho defaulted)

/-- A path completes each newly completed event by one of its steps. -/
theorem path_new_event {graph : Vegas.EventGraph Player L} {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) {event : graph.EventId}
    (fresh : event ∉ before.cut.completed) (done : event ∈ after.cut.completed) :
    ∃ (middle next : graph.Config) (ready : middle.cut.Ready event) (action : graph.Action event),
      Relation.ReflTransGen Config.Step before middle ∧
        next ∈ (middle.step event ready action).support ∧
        Relation.ReflTransGen Config.Step next after := by
  induction path with
  | refl => exact (fresh done).elim
  | @tail middle last walked moved ih =>
      by_cases earlier : event ∈ middle.cut.completed
      · obtain ⟨first, second, ready, action, firstPath, member, secondPath⟩ := ih earlier
        exact ⟨first, second, ready, action, firstPath, member, secondPath.tail moved⟩
      · obtain ⟨stepped, steppedReady, action, member⟩ := moved
        have same : event = stepped := by
          rw [middle.step_cut stepped steppedReady action last member,
            EventOrder.Cut.mem_complete] at done
          exact done.resolve_right earlier
        subst same
        exact ⟨middle, last, steppedReady, action, walked, member, .refl⟩

/-- **A decided resolution along a path.** A reveal completed along a path from
a configuration storing its footprint, whose record carries a decision, records
that disclosure and publishes the resolution of the starting store. -/
theorem resolve_record_of_path {origin current : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step origin current)
    {event : (serviceGraph setup mode).EventId} (fresh : event ∉ origin.cut.completed)
    (done : event ∈ current.cut.completed) {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (origin.store field).isSome)
    (decided : ∃ record, completionOf current event = some record ∧ record.decision.isSome) :
    ∃ (disclose : Bool) (output : PublicationResult (L.Val payload)),
      EventCode.resolveOutput? binding checks disclose origin.store = some output ∧
      completionOf current event = some (EventGraph.completion (serviceGraph setup mode) event
        (some (cast (congrArg EventField.Action outputEq.symm) disclose))
        (cast (congrArg EventField.Value outputEq.symm) output)) ∧
      current.outputs event = some (cast (congrArg EventField.Value outputEq.symm) output) := by
  obtain ⟨middle, next, ready, action, before, member, after⟩ := path_new_event path fresh done
  have owned := nodeView_resolve_actor outputEq codeEq
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  have actionEq : action = cast (congrArg EventField.Action outputEq.symm) disclose := by
    simp only [disclose, cast_cast, cast_eq]
  obtain ⟨value, nextOutput, history⟩ := middle.step_completion event ready action next member
  have nextRecord : completionOf next event = some (EventGraph.completion
      (serviceGraph setup mode) event (middle.actualDecision event action) value) :=
    (completionOf_eq_some_iff next event _).mpr ⟨by
      rw [history]
      exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  have currentRecord := Config.Step.path_completionOf_of_some after event _ nextRecord
  obtain ⟨chosen, chosenFound, decision⟩ := decided
  rw [currentRecord] at chosenFound
  have chosenEq := Option.some.inj chosenFound
  subst chosenEq
  have activeMiddle : owner ∉ middle.defaulted := by
    intro inactive
    change (middle.actualDecision event action).isSome = true at decision
    rw [middle.actualDecision_of_defaulted event owner owned inactive action] at decision
    cases decision
  have kept : ∀ field stored, origin.store field = some stored →
      middle.store field = some stored :=
    fun field stored found => Config.Step.path_store_of_some before field stored found
  have availableMiddle : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (middle.store field).isSome := by
    intro field read
    obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp (available field read)
    rw [kept field stored found]
    rfl
  have footprint := EventCode.readFields_cast outputEq ((serviceGraph setup mode).nodes event)
  rw [codeEq] at footprint
  obtain ⟨output, resolved⟩ := Option.isSome_iff_exists.mp
    (EventCode.resolveOutput?_isSome binding checks disclose middle.store
      (fun field member => availableMiddle field (by rw [← footprint]; exact member)))
  have stepEq := resolve_step_eq ready outputEq codeEq activeMiddle disclose output resolved
  rw [actionEq, stepEq, PMF.mem_support_pure_iff] at member
  have valueEq : value = cast (congrArg EventField.Value outputEq.symm) output := by
    rw [member, Config.complete_output_same] at nextOutput
    exact (Option.some.inj nextOutput).symm
  refine ⟨disclose, output, ?_, ?_, ?_⟩
  · rw [← resolveOutput_keep kept (outputEq := outputEq) codeEq available disclose]
    exact resolved
  · rw [currentRecord, middle.actualDecision_of_active event owner owned activeMiddle action,
      valueEq, ← actionEq]
  · have nextDone : event ∈ next.cut.completed := by
      rw [middle.step_cut event ready _ next
          (by rw [stepEq, member]; exact (PMF.mem_support_pure_iff _ _).mpr rfl),
        EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    rw [outputs_path after nextDone, nextOutput, valueEq]

/-- **No block reveal pending at the start completes silently.** Its owner is
active at the start and owns no other block event, and only block events record
new defaults. -/
theorem pending_not_silent {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin current : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : DefaultOwners current)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed) {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (silent : completionOf current event = some ⟨event, none, none⟩)
    (inactive : owner ∈ current.defaulted) : False := by
  have active : owner ∉ origin.defaulted := fun defaulted =>
    pending ((begin.drained event early late).mpr ⟨owner, owned, defaulted⟩)
  obtain ⟨other, recorded⟩ := (mem_defaulted_iff_completionOf current owner).mp inactive
  obtain ⟨record, found, defaulted⟩ := Option.bind_eq_some_iff.mp recorded
  have recordEvent := completionOf_tagged current other record found
  have member := ((completionOf_eq_some_iff current other record).mp found).1
  have otherOwned : (serviceGraph setup mode).actor? other = some owner := by
    rw [← recordEvent]
    exact owners record member owner defaulted
  have otherDone : other ∈ current.cut.completed :=
    (completionOf_isSome_iff current other).mp (by rw [found]; rfl)
  have clash (otherEarly : start ≤ other.val) (otherLate : other.val < finish)
      (old : other ∉ origin.cut.completed) : False := by
    by_cases same : other = event
    · subst same
      rw [silent] at found
      cases found
      cases defaulted
    · have eventReady := flat.ready_of_earlier begin.earlier early late pending
      have otherReady := flat.ready_of_earlier begin.earlier otherEarly otherLate old
      rcases concurrent origin.cut eventReady otherReady (Ne.symm same) with
        independent | independent
      · exact independent.2.2.2 (owned.trans otherOwned.symm)
      · exact independent.2.2.2 (otherOwned.trans owned.symm)
  by_cases old : other ∈ origin.cut.completed
  · obtain ⟨earlier, earlierFound⟩ :=
      Option.isSome_iff_exists.mp ((completionOf_isSome_iff origin other).mpr old)
    have kept := Config.Step.path_completionOf_of_some path other earlier earlierFound
    rw [kept] at found
    have same : earlier = record := Option.some.inj found
    subst same
    exact active ((mem_defaulted_iff_completionOf origin owner).mpr
      ⟨other, by rw [earlierFound]; exact defaulted⟩)
  rcases sound other old otherDone with ⟨quiet, _, _⟩ |
    ⟨otherEarly, otherLate, _ | opened | _⟩
  · rw [quiet] at found
    cases found
    cases defaulted
  · exact clash otherEarly otherLate old
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, openedRecord, _⟩ := opened
    rw [openedRecord] at found
    cases found
    cases defaulted
  · exact clash otherEarly otherLate old

/-- Distinct events of a flat block of concurrent reveals have distinct owners. -/
theorem block_actor_unique {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {left right : (serviceGraph setup mode).EventId} (leftEarly : start ≤ left.val)
    (leftLate : left.val < finish) (rightEarly : start ≤ right.val) (rightLate : right.val < finish)
    {player : Player} (leftOwned : (serviceGraph setup mode).actor? left = some player)
    (rightOwned : (serviceGraph setup mode).actor? right = some player) : left = right := by
  by_contra different
  let prefixCut : (serviceGraph setup mode).order.Cut :=
    { completed := Finset.univ.filter fun event => event.val < start
      predecessor_closed := fun {event} member prior priorMember => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
        exact lt_trans ((serviceGraph setup mode).order.predecessor_lt priorMember) member }
  have readyOf {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
      (late : event.val < finish) : prefixCut.Ready event := by
    refine ⟨fun member => ?_, fun prior priorMember => ?_⟩
    · simp only [prefixCut, Finset.mem_filter, Finset.mem_univ, true_and] at member
      omega
    · simp only [prefixCut, Finset.mem_filter, Finset.mem_univ, true_and]
      exact flat event prior early late priorMember
  rcases concurrent prefixCut (readyOf leftEarly leftLate) (readyOf rightEarly rightLate)
      different with independent | independent
  · exact independent.2.2.2 (leftOwned.trans rightOwned.symm)
  · exact independent.2.2.2 (rightOwned.trans leftOwned.symm)

/-- A block reveal pending at the start completes with a decision. -/
theorem decided_of_pending {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin current : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : DefaultOwners current)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed)
    (done : event ∈ current.cut.completed) {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∃ record, completionOf current event = some record ∧ record.decision.isSome := by
  obtain ⟨middle, next, ready, action, before, member, after⟩ := path_new_event path pending done
  obtain ⟨value, _, history⟩ := middle.step_completion event ready action next member
  have nextRecord : completionOf next event = some (EventGraph.completion
      (serviceGraph setup mode) event (middle.actualDecision event action) value) :=
    (completionOf_eq_some_iff next event _).mpr ⟨by
      rw [history]
      exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  have currentRecord := Config.Step.path_completionOf_of_some after event _ nextRecord
  refine ⟨_, currentRecord, ?_⟩
  by_cases inactive : owner ∈ middle.defaulted
  · exfalso
    have silent : completionOf current event = some ⟨event, none, none⟩ := by
      rw [currentRecord, middle.actualDecision_of_defaulted event owner owned inactive action]
      rfl
    have laterInactive : owner ∈ current.defaulted :=
      Config.Step.path_defaulted_mono (Relation.ReflTransGen.head ⟨event, ready, action, member⟩
        after) inactive
    exact pending_not_silent concurrent flat begin path sound owners early late pending owned
      silent laterInactive
  · change (middle.actualDecision event action).isSome = true
    rw [middle.actualDecision_of_active event owner owned inactive action]
    rfl

/-- A state with no automatically ready event has a quiescent configuration. -/
theorem quiescent_of_automatic (state : EventGraphRuntime.State (serviceGraph setup mode))
    (quiet : ∀ event, ¬ state.AutomaticReady event) : state.config.Quiescent := by
  intro event ready owner owned inactive
  apply quiet event
  unfold EventGraphRuntime.State.AutomaticReady
  rw [owned]
  exact ⟨ready, inactive⟩

/-- Draining a configuration reaches a quiescent configuration. -/
theorem drainConfig_quiescent (config : (serviceGraph setup mode).Config) :
    (State.drainConfig config).Quiescent :=
  quiescent_of_automatic _ (State.drain_quiescent (State.ofConfig config))

/-- Draining a configuration keeps the block's records classified. -/
theorem BlockRecordsSound.drainConfig {who : Player} {start finish : Nat}
    {origin config : (serviceGraph setup mode).Config}
    (sound : BlockRecordsSound who start finish origin config) :
    BlockRecordsSound who start finish origin (State.drainConfig config) := by
  have path : Relation.ReflTransGen Config.Step config (State.drainConfig config) :=
    State.drain_graph_steps (State.ofConfig config)
  intro event fresh done
  by_cases old : event ∈ config.cut.completed
  · exact BlockRecordsSound.path path sound event fresh old
  obtain ⟨record, recorded⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff (State.drainConfig config) event).mpr done)
  obtain ⟨present, recordEvent⟩ :=
    (completionOf_eq_some_iff (State.drainConfig config) event record).mp recorded
  have primary : record ∉ config.history := fun inside =>
    old ((config.history_exact event).mp (List.mem_map.mpr ⟨record, inside, recordEvent⟩))
  obtain ⟨silent, quiet, _, output, owner, owned, inactive⟩ :=
    drainRecord_of_not_mem (State.ofConfig config) record primary present
  subst recordEvent
  exact Or.inl ⟨completionOf_of_silent present silent quiet, output, owner, owned, inactive⟩

end Vegas
