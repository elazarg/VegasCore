/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockCoupling
import Vegas.Game.RevealBlockEndpoint

/-! # Reading the start of a block from its end

At the end of a block of concurrent reveals, the deviator's normalized view
determines its view at the start of the block and the output every honest
reveal pending at the start would publish if opened. A block is flat: every
predecessor of a block event precedes the block, so every block event pending
at the start is ready, and concurrently ready events have distinct owners.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

section Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- **A configuration is the restriction of its successors to its completed
events.** -/
theorem Config.restrictionOf_completed_path {before after : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after) :
    before.RestrictionOf (fun event => event ∈ before.cut.completed) after where
  records event := by
    by_cases done : event ∈ before.cut.completed
    · rw [ite_eq_left done]
      obtain ⟨completion, found⟩ :=
        Option.isSome_iff_exists.mp ((completionOf_isSome_iff before event).mpr done)
      rw [found, Config.Step.path_completionOf_of_some path event completion found]
    · rw [ite_eq_right done]
      exact (completionOf_eq_none_iff before event).mpr done
  store field := by
    cases field with
    | inl input =>
        rw [ite_eq_left (show FieldWithin (fun event : graph.EventId =>
          event ∈ before.cut.completed) (.inl input) from trivial)]
        change some (before.inputs input) = some (after.inputs input)
        rw [Config.Step.path_inputs_eq path]
    | inr event =>
        by_cases done : event ∈ before.cut.completed
        · rw [ite_eq_left (show FieldWithin (fun event : graph.EventId =>
            event ∈ before.cut.completed) (.inr event) from done)]
          obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
            ((before.output_available event).mpr done)
          change before.outputs event = after.store (.inr event)
          rw [stored]
          exact (Config.Step.path_store_of_some path (.inr event) value stored).symm
        · rw [ite_eq_right (show ¬ FieldWithin (fun event : graph.EventId =>
            event ∈ before.cut.completed) (.inr event) from done)]
          change before.outputs event = none
          exact Option.not_isSome_iff_eq_none.mp fun available =>
            done ((before.output_available event).mp available)

/-- A block is flat: every predecessor of a block event precedes the block. -/
def BlockFlat (start finish : Nat) : Prop :=
  ∀ event prior : graph.EventId, start ≤ event.val → event.val < finish →
    prior ∈ graph.order.predecessors event → prior.val < start

omit [DecidableEq Player] in
/-- In a flat block every pending block event is ready once every earlier
event has completed. -/
theorem BlockFlat.ready_of_earlier {start finish : Nat}
    (flat : BlockFlat (graph := graph) start finish) {config : graph.Config}
    (earlier : ∀ event : graph.EventId, event.val < start → event ∈ config.cut.completed)
    {event : graph.EventId} (early : start ≤ event.val) (late : event.val < finish)
    (pending : event ∉ config.cut.completed) : config.cut.Ready event :=
  ⟨pending, fun prior member => earlier prior (flat event prior early late member)⟩

omit [DecidableEq Player] in
/-- Inside a flat block every pending block event is ready. -/
theorem BlockFlat.ready {start finish : Nat} (flat : BlockFlat (graph := graph) start finish)
    {config : graph.Config} (inside : InBlock start finish config)
    {event : graph.EventId} (early : start ≤ event.val) (late : event.val < finish)
    (pending : event ∉ config.cut.completed) : config.cut.Ready event :=
  ⟨pending, fun prior member => inside.1 prior (flat event prior early late member)⟩

end Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode}

/-- The start of a block: every earlier event has completed, a later event only
once the block is done, and every block or later event completed so far was
completed silently, a block event exactly when its owner is defaulted. -/
structure BlockStart (start finish : Nat) (config : (serviceGraph setup mode).Config) :
    Prop where
  earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
    event ∈ config.cut.completed
  later : ∀ event : (serviceGraph setup mode).EventId, finish ≤ event.val →
    event ∈ config.cut.completed → BlockDone finish config
  beyond : ∀ event : (serviceGraph setup mode).EventId, finish ≤ event.val →
    event ∈ config.cut.completed → completionOf config event = some ⟨event, none, none⟩
  failed : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
    event.val < finish → event ∈ config.cut.completed →
      config.outputs event = failureOutput event
  drained : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
    event.val < finish → (event ∈ config.cut.completed ↔
      ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧ owner ∈ config.defaulted)
  silent : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
    event.val < finish → event ∈ config.cut.completed →
      completionOf config event = some ⟨event, none, none⟩

/-- A block start whose block is unfinished lies inside the block. -/
theorem BlockStart.inside {start finish : Nat} {config : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish config) (running : ¬ BlockDone finish config) :
    InBlock start finish config :=
  ⟨begin.earlier, fun event late done => running (begin.later event late done)⟩

/-- The output a reveal would publish if opened now. -/
def acceptedOutput (event : (serviceGraph setup mode).EventId)
    (store : EventGraph.Store (serviceGraph setup mode).layout) :
    Option ((serviceGraph setup mode).outputLayout event).Value :=
  match nodeView (serviceGraph setup mode) event with
  | .resolve _ _ binding checks outputEq _ =>
      (EventCode.resolveOutput? binding checks true store).map
        (cast (congrArg EventField.Value outputEq.symm))
  | .bind .. | .sample .. => none

/-- The hidden data of a block read from a run key: the output each honest
block reveal pending at the start would publish if opened. -/
def blockHidden (who : Player) (start finish : Nat) (key : RunKey (serviceGraph setup mode)) :
    (event : (serviceGraph setup mode).EventId) →
      Option ((serviceGraph setup mode).outputLayout event).Value :=
  fun event => if start ≤ event.val ∧ event.val < finish ∧ event ∉ key.1.completed ∧
      (serviceGraph setup mode).actor? event ≠ some who then acceptedOutput event key.2.1
    else none

/-- A rejected opening with a stored footprint publishes a failure. -/
theorem resolveOutput_of_rejected {event : (serviceGraph setup mode).EventId} {owner : Player}
    {payload : L.Ty} {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    {store : EventGraph.Store (serviceGraph setup mode).layout}
    (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (store field).isSome)
    (rejected : openingAccepted event store = false) :
    EventCode.resolveOutput? binding checks true store = some .failure := by
  have footprint := EventCode.readFields_cast outputEq ((serviceGraph setup mode).nodes event)
  rw [codeEq] at footprint
  have defined := EventCode.resolveOutput?_isSome binding checks true store (fun field member =>
    available field (by rw [← footprint]; exact member))
  unfold openingAccepted at rejected
  rw [node] at rejected
  dsimp only at rejected
  cases result : EventCode.resolveOutput? binding checks true store with
  | none => rw [result] at defined; cases defined
  | some output =>
      cases output with
      | success value => rw [result] at rejected; cases rejected
      | failure => rfl

/-- **No honest block reveal pending at the start completes silently.** Its
owner is active at the start and owns no other block event, and only block
events record new defaults. -/
theorem honest_pending_not_silent {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin current : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : ∀ completion ∈ current.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed) {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner) (honest : owner ≠ who)
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
    ⟨otherEarly, otherLate, otherWho | opened | expired⟩
  · rw [quiet] at found
    cases found
    cases defaulted
  · exact honest (Option.some.inj (otherOwned.symm.trans otherWho))
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, openedRecord, _⟩ := opened
    rw [openedRecord] at found
    cases found
    cases defaulted
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := expired
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

/-- Once every honest block reveal pending at the start has completed, each
stores the output it would have published if opened at the start. -/
theorem acceptedOutput_eq_of_honestDone {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin current : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : ∀ completion ∈ current.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (honestDone : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ origin.cut.completed →
        (serviceGraph setup mode).actor? event ≠ some who → event ∈ current.cut.completed)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed)
    (honest : (serviceGraph setup mode).actor? event ≠ some who) :
    acceptedOutput event origin.store = current.outputs event := by
  have ready := flat.ready_of_earlier begin.earlier early late pending
  have available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (origin.store field).isSome := fun field read => origin.read_available ready read
  have kept : ∀ field value, origin.store field = some value → current.store field = some value :=
    fun field value stored => Config.Step.path_store_of_some path field value stored
  rcases sound event pending (honestDone event early late pending honest) with
    ⟨quiet, _, owner, owned, inactive⟩ | ⟨_, _, whoOwned | opened | expired⟩
  · exact (honest_pending_not_silent concurrent flat begin path sound owners early late pending
      owned (fun same => honest (same ▸ owned)) quiet inactive).elim
  · exact (honest whoOwned).elim
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, _, node, _, _, _, stored⟩ :=
      opened
    rw [stored, resolveOutput_keep kept (outputEq := outputEq) codeEq available]
    simp only [acceptedOutput, node]
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, _, node, _, rejected, _,
      stored⟩ := expired
    rw [openingAccepted_path_eq path available] at rejected
    rw [stored]
    simp only [acceptedOutput, node, resolveOutput_of_rejected node available rejected,
      Option.map_some]

/-- At the end of a block, an honest block reveal pending at the start stores
the output it would have published if opened at the start. -/
theorem acceptedOutput_eq_end {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin current : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (path : Relation.ReflTransGen Config.Step origin current)
    (sound : BlockRecordsSound who start finish origin current)
    (owners : ∀ completion ∈ current.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (finished : BlockDone finish current)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed)
    (honest : (serviceGraph setup mode).actor? event ≠ some who) :
    acceptedOutput event origin.store = current.outputs event :=
  acceptedOutput_eq_of_honestDone concurrent flat begin path sound owners
    (fun event _ late _ _ => finished event late) early late pending honest

/-- A default recorded before a block is read from the end of the block. -/
private theorem defaulted_of_end {who : Player} {start finish : Nat}
    {startLeft startRight endLeft endRight : (serviceGraph setup mode).Config}
    (beginLeft : BlockStart start finish startLeft)
    (beginRight : BlockStart start finish startRight)
    (pathLeft : Relation.ReflTransGen Config.Step startLeft endLeft)
    (pathRight : Relation.ReflTransGen Config.Step startRight endRight)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endRight))
    {player : Player} (defaulted : player ∈ startLeft.defaulted) :
    player ∈ startRight.defaulted := by
  obtain ⟨event, recorded⟩ := (mem_defaulted_iff_completionOf startLeft player).mp defaulted
  obtain ⟨record, found, entry⟩ := Option.bind_eq_some_iff.mp recorded
  have done : event ∈ startLeft.cut.completed :=
    (completionOf_isSome_iff startLeft event).mp (by rw [found]; rfl)
  have early : event.val < start := by
    by_contra late
    push Not at late
    by_cases beyond : finish ≤ event.val
    · rw [beginLeft.beyond event beyond done] at found
      cases found
      cases entry
    · push Not at beyond
      rw [beginLeft.silent event late beyond done] at found
      cases found
      cases entry
  have doneRight : event ∈ startRight.cut.completed := beginRight.earlier event early
  obtain ⟨other, otherFound⟩ :=
    Option.isSome_iff_exists.mp ((completionOf_isSome_iff startRight event).mpr doneRight)
  have leftEnd := Config.Step.path_completionOf_of_some pathLeft event record found
  have rightEnd := Config.Step.path_completionOf_of_some pathRight event other otherFound
  have defaults := normalize_defaultEvent_congr who views event (by rw [leftEnd]; rfl)
  rw [leftEnd, rightEnd] at defaults
  exact (mem_defaulted_iff_completionOf startRight player).mpr
    ⟨event, by rw [otherFound, ← defaults]; exact Option.bind_eq_some_iff.mpr ⟨record, rfl, entry⟩⟩

/-- **The start of a block is read from a later configuration.** Two runs of a
block whose honest reveals pending at the start have completed and whose
configurations give the deviator equal normalized views started from equal
views of the deviator and equal hidden outputs of the honest reveals. -/
theorem blockStart_reflect_of_honestDone {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {startLeft startRight endLeft endRight : (serviceGraph setup mode).Config}
    (beginLeft : BlockStart start finish startLeft)
    (beginRight : BlockStart start finish startRight)
    (runningLeft : ¬ BlockDone finish startLeft) (runningRight : ¬ BlockDone finish startRight)
    (pathLeft : Relation.ReflTransGen Config.Step startLeft endLeft)
    (pathRight : Relation.ReflTransGen Config.Step startRight endRight)
    (soundLeft : BlockRecordsSound who start finish startLeft endLeft)
    (soundRight : BlockRecordsSound who start finish startRight endRight)
    (ownersLeft : ∀ completion ∈ endLeft.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (ownersRight : ∀ completion ∈ endRight.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (honestLeft : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ startLeft.cut.completed →
        (serviceGraph setup mode).actor? event ≠ some who → event ∈ endLeft.cut.completed)
    (honestRight : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ startRight.cut.completed →
        (serviceGraph setup mode).actor? event ≠ some who → event ∈ endRight.cut.completed)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endRight)) :
    (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startRight) ∧
    blockHidden who start finish (runKey startLeft) =
      blockHidden who start finish (runKey startRight) := by
  have defaultedEq : startLeft.defaulted = startRight.defaulted := by
    ext player
    exact ⟨defaulted_of_end beginLeft beginRight pathLeft pathRight views,
      defaulted_of_end beginRight beginLeft pathRight pathLeft views.symm⟩
  have completedIff (event : (serviceGraph setup mode).EventId) :
      event ∈ startLeft.cut.completed ↔ event ∈ startRight.cut.completed := by
    by_cases early : event.val < start
    · exact ⟨fun _ => beginRight.earlier event early, fun _ => beginLeft.earlier event early⟩
    push Not at early
    by_cases beyond : finish ≤ event.val
    · exact ⟨fun done => ((beginLeft.inside runningLeft).2 event beyond done).elim,
        fun done => ((beginRight.inside runningRight).2 event beyond done).elim⟩
    push Not at beyond
    rw [beginLeft.drained event early beyond, beginRight.drained event early beyond,
      defaultedEq]
  have leftRestricted := Config.restrictionOf_completed_path pathLeft
  have rightOwn := Config.restrictionOf_completed_path pathRight
  have rightRestricted : startRight.RestrictionOf
      (fun event => event ∈ startLeft.cut.completed) endRight :=
    { records := fun event => by
        rw [rightOwn.records event]
        by_cases done : event ∈ startLeft.cut.completed
        · rw [ite_eq_left done, ite_eq_left ((completedIff event).mp done)]
        · rw [ite_eq_right done,
            ite_eq_right (fun other => done ((completedIff event).mpr other))]
      store := fun field => by
        rw [rightOwn.store field]
        cases field with
        | inl input =>
            rw [ite_eq_left (show FieldWithin (fun event : (serviceGraph setup mode).EventId =>
                event ∈ startLeft.cut.completed) (.inl input) from trivial),
              ite_eq_left (show FieldWithin (fun event : (serviceGraph setup mode).EventId =>
                event ∈ startRight.cut.completed) (.inl input) from trivial)]
        | inr event =>
            by_cases done : event ∈ startLeft.cut.completed
            · rw [ite_eq_left (show FieldWithin (fun event : (serviceGraph setup mode).EventId =>
                  event ∈ startLeft.cut.completed) (.inr event) from done),
                ite_eq_left (show FieldWithin (fun event : (serviceGraph setup mode).EventId =>
                  event ∈ startRight.cut.completed) (.inr event) from
                  (completedIff event).mp done)]
            · rw [ite_eq_right (show ¬ FieldWithin
                  (fun event : (serviceGraph setup mode).EventId =>
                    event ∈ startLeft.cut.completed) (.inr event) from done),
                ite_eq_right (show ¬ FieldWithin
                  (fun event : (serviceGraph setup mode).EventId =>
                    event ∈ startRight.cut.completed) (.inr event) from
                  fun other => done ((completedIff event).mpr other))] }
  refine ⟨normalizeObservation_playerObserve_restrict who _ leftRestricted rightRestricted views,
    ?_⟩
  have stores := congrArg (fun observation : (serviceGraph setup mode).PlayerObservation who =>
    observation.store) views
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
  simp only at stores
  funext event
  unfold blockHidden
  change (if start ≤ event.val ∧ event.val < finish ∧ event ∉ startLeft.cut.completed ∧
      (serviceGraph setup mode).actor? event ≠ some who then acceptedOutput event startLeft.store
      else none) = (if start ≤ event.val ∧ event.val < finish ∧
      event ∉ startRight.cut.completed ∧ (serviceGraph setup mode).actor? event ≠ some who then
      acceptedOutput event startRight.store else none)
  by_cases hidden : start ≤ event.val ∧ event.val < finish ∧ event ∉ startLeft.cut.completed ∧
      (serviceGraph setup mode).actor? event ≠ some who
  · obtain ⟨early, late, pending, honest⟩ := hidden
    have pendingRight : event ∉ startRight.cut.completed :=
      fun done => pending ((completedIff event).mpr done)
    rw [ite_eq_left ⟨early, late, pending, honest⟩,
      ite_eq_left ⟨early, late, pendingRight, honest⟩,
      acceptedOutput_eq_of_honestDone concurrent flat beginLeft pathLeft soundLeft ownersLeft
        honestLeft early late pending honest,
      acceptedOutput_eq_of_honestDone concurrent flat beginRight pathRight soundRight ownersRight
        honestRight early late pendingRight honest]
    have visible := congrFun stores (.inr event)
    rwa [playerStore_of_visible (visible := fieldVisibleTo_of_publication who
        (publications event early late)),
      playerStore_of_visible (visible := fieldVisibleTo_of_publication who
        (publications event early late))] at visible
  · have hiddenRight : ¬ (start ≤ event.val ∧ event.val < finish ∧
        event ∉ startRight.cut.completed ∧ (serviceGraph setup mode).actor? event ≠ some who) :=
      fun ⟨early, late, pending, honest⟩ =>
        hidden ⟨early, late, fun done => pending ((completedIff event).mp done), honest⟩
    rw [ite_eq_right hidden, ite_eq_right hiddenRight]

/-- **The start of a block is read from its end.** Two block runs whose ends
give the deviator equal normalized views started from equal views of the
deviator and equal hidden outputs of the honest reveals. -/
theorem blockStart_reflect {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    {startLeft startRight endLeft endRight : (serviceGraph setup mode).Config}
    (beginLeft : BlockStart start finish startLeft)
    (beginRight : BlockStart start finish startRight)
    (runningLeft : ¬ BlockDone finish startLeft) (runningRight : ¬ BlockDone finish startRight)
    (pathLeft : Relation.ReflTransGen Config.Step startLeft endLeft)
    (pathRight : Relation.ReflTransGen Config.Step startRight endRight)
    (soundLeft : BlockRecordsSound who start finish startLeft endLeft)
    (soundRight : BlockRecordsSound who start finish startRight endRight)
    (ownersLeft : ∀ completion ∈ endLeft.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (ownersRight : ∀ completion ∈ endRight.history, ∀ player,
      completion.defaultEvent = some player →
        (serviceGraph setup mode).actor? completion.event = some player)
    (finishedLeft : BlockDone finish endLeft) (finishedRight : BlockDone finish endRight)
    (views : (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who endRight)) :
    (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startLeft) =
      (serviceGraph setup mode).normalizeObservation who
        ((serviceGraph setup mode).playerObserve who startRight) ∧
    blockHidden who start finish (runKey startLeft) =
      blockHidden who start finish (runKey startRight) :=
  blockStart_reflect_of_honestDone concurrent flat publications beginLeft beginRight runningLeft
    runningRight pathLeft pathRight soundLeft soundRight ownersLeft ownersRight
    (fun event _ late _ _ => finishedLeft event late)
    (fun event _ late _ _ => finishedRight event late) views

end Vegas
