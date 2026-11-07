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

end Vegas
