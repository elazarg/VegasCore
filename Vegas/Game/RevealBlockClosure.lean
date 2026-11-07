/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockRun

/-! # Block ends fixed by the deviator's records

Two quiescent configurations that complete the same base events, complete
every other event automatically for a defaulted owner, and have the same
defaults complete the same events. Hence two quiescent ends of a block of
concurrent reveals run from the same start have the same order-free key when
they agree on the deviator's new block records and outputs.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

section Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A configuration is quiescent when no ready event belongs to a defaulted
owner. -/
def EventGraph.Config.Quiescent (config : graph.Config) : Prop :=
  ∀ event, config.cut.Ready event → ∀ owner, graph.actor? event = some owner →
    owner ∉ config.defaulted

/-- **Automatic closures agree.** Two quiescent configurations that complete
the same base events, complete every other event for a defaulted owner, and
have the same defaults complete the same events. -/
theorem completed_eq_of_quiescent {left right : graph.Config} (base : graph.EventId → Prop)
    (leftBase : ∀ event, base event → event ∈ left.cut.completed)
    (rightBase : ∀ event, base event → event ∈ right.cut.completed)
    (leftAutomatic : ∀ event, event ∈ left.cut.completed → ¬ base event →
      ∃ owner, graph.actor? event = some owner ∧ owner ∈ left.defaulted)
    (rightAutomatic : ∀ event, event ∈ right.cut.completed → ¬ base event →
      ∃ owner, graph.actor? event = some owner ∧ owner ∈ right.defaulted)
    (defaults : left.defaulted = right.defaulted)
    (leftQuiet : left.Quiescent) (rightQuiet : right.Quiescent) :
    left.cut.completed = right.cut.completed := by
  have one (first second : graph.Config)
      (secondBase : ∀ event, base event → event ∈ second.cut.completed)
      (firstAutomatic : ∀ event, event ∈ first.cut.completed → ¬ base event →
        ∃ owner, graph.actor? event = some owner ∧ owner ∈ first.defaulted)
      (sameDefaults : first.defaulted = second.defaulted) (secondQuiet : second.Quiescent)
      (event : graph.EventId)
      (earlier : ∀ prior : graph.EventId, prior.val < event.val →
        prior ∈ first.cut.completed → prior ∈ second.cut.completed)
      (done : event ∈ first.cut.completed) : event ∈ second.cut.completed := by
    by_cases based : base event
    · exact secondBase event based
    obtain ⟨owner, owned, defaulted⟩ := firstAutomatic event done based
    by_contra pending
    have ready : second.cut.Ready event := ⟨pending, fun prior member =>
      earlier prior (graph.order.predecessor_lt member)
        (first.cut.predecessor_closed done member)⟩
    exact secondQuiet event ready owner owned (sameDefaults ▸ defaulted)
  ext event
  induction hval : event.val using Nat.strong_induction_on generalizing event with
  | _ rank ih =>
      have earlier (prior : graph.EventId) (smaller : prior.val < event.val) :
          prior ∈ left.cut.completed ↔ prior ∈ right.cut.completed :=
        ih prior.val (hval ▸ smaller) prior rfl
      exact ⟨one left right rightBase leftAutomatic defaults rightQuiet event
          (fun prior smaller => (earlier prior smaller).mp),
        one right left leftBase rightAutomatic defaults.symm leftQuiet event
          (fun prior smaller => (earlier prior smaller).mpr)⟩

end Generic

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode}

/-- Two ends of a block from starts with equal keys record and store alike
every honest reveal pending at the start. -/
theorem honest_end_congr_of_keys {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {leftOrigin rightOrigin left right : (serviceGraph setup mode).Config}
    (keys : runKey leftOrigin = runKey rightOrigin)
    (leftBegin : BlockStart start finish leftOrigin)
    (rightBegin : BlockStart start finish rightOrigin)
    (leftPath : Relation.ReflTransGen Config.Step leftOrigin left)
    (rightPath : Relation.ReflTransGen Config.Step rightOrigin right)
    (leftSound : BlockRecordsSound who start finish leftOrigin left)
    (rightSound : BlockRecordsSound who start finish rightOrigin right)
    (leftOwners : DefaultOwners left) (rightOwners : DefaultOwners right)
    (leftDone : BlockDone finish left) (rightDone : BlockDone finish right)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ leftOrigin.cut.completed)
    (honest : (serviceGraph setup mode).actor? event ≠ some who) :
    completionOf left event = completionOf right event ∧
      left.outputs event = right.outputs event := by
  have cuts : leftOrigin.cut = rightOrigin.cut := congrArg Prod.fst keys
  have stores : leftOrigin.store = rightOrigin.store := congrArg (fun key => key.2.1) keys
  have rightPending : event ∉ rightOrigin.cut.completed := by rw [← cuts]; exact pending
  have leftReady := flat.ready_of_earlier leftBegin.earlier early late pending
  have rightReady := flat.ready_of_earlier rightBegin.earlier early late rightPending
  have leftAvailable : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (leftOrigin.store field).isSome := fun field read => leftOrigin.read_available leftReady read
  have rightAvailable : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (rightOrigin.store field).isSome :=
    fun field read => rightOrigin.read_available rightReady read
  refine ⟨?_, (acceptedOutput_eq_end concurrent flat leftBegin leftPath leftSound leftOwners
    leftDone early late pending honest).symm.trans (by
      rw [stores]
      exact acceptedOutput_eq_end concurrent flat rightBegin rightPath rightSound rightOwners
        rightDone early late rightPending honest)⟩
  have silentFalse {origin current : (serviceGraph setup mode).Config}
      (begin : BlockStart start finish origin) (originPending : event ∉ origin.cut.completed)
      (path : Relation.ReflTransGen Config.Step origin current)
      (sound : BlockRecordsSound who start finish origin current) (owners : DefaultOwners current)
      {owner : Player} (owned : (serviceGraph setup mode).actor? event = some owner)
      (quiet : completionOf current event = some ⟨event, none, none⟩)
      (inactive : owner ∈ current.defaulted) : False :=
    honest_pending_not_silent concurrent flat begin path sound owners early late originPending
      owned (fun same => honest (same ▸ owned)) quiet inactive
  have leftAccepted := openingAccepted_path_eq leftPath leftAvailable
  have rightAccepted := openingAccepted_path_eq rightPath rightAvailable
  rw [← stores] at rightAccepted
  rcases leftSound event pending (leftDone event late) with
    ⟨leftQuiet, _, leftOwner, leftOwned, leftInactive⟩ |
    ⟨_, _, leftWho | leftOpened | leftExpired⟩
  · exact (silentFalse leftBegin pending leftPath leftSound leftOwners leftOwned leftQuiet
      leftInactive).elim
  · exact (honest leftWho).elim
  · rcases rightSound event rightPending (rightDone event late) with
      ⟨rightQuiet, _, rightOwner, rightOwned, rightInactive⟩ |
      ⟨_, _, rightWho | rightOpened | rightExpired⟩
    · exact (silentFalse rightBegin rightPending rightPath rightSound rightOwners rightOwned
        rightQuiet rightInactive).elim
    · exact (honest rightWho).elim
    · obtain ⟨_, _, _, _, _, _, _, leftNode, _, _, leftRecorded, _⟩ := leftOpened
      obtain ⟨_, _, _, _, _, _, _, rightNode, _, _, rightRecorded, _⟩ := rightOpened
      rw [leftNode] at rightNode
      cases rightNode
      exact leftRecorded.trans rightRecorded.symm
    · exfalso
      obtain ⟨_, _, _, _, _, _, _, _, _, accepted, _, _⟩ := leftOpened
      obtain ⟨_, _, _, _, _, _, _, _, _, rejected, _, _⟩ := rightExpired
      rw [leftAccepted] at accepted
      rw [rightAccepted, accepted] at rejected
      cases rejected
  · rcases rightSound event rightPending (rightDone event late) with
      ⟨rightQuiet, _, rightOwner, rightOwned, rightInactive⟩ |
      ⟨_, _, rightWho | rightOpened | rightExpired⟩
    · exact (silentFalse rightBegin rightPending rightPath rightSound rightOwners rightOwned
        rightQuiet rightInactive).elim
    · exact (honest rightWho).elim
    · exfalso
      obtain ⟨_, _, _, _, _, _, _, _, _, rejected, _, _⟩ := leftExpired
      obtain ⟨_, _, _, _, _, _, _, _, _, accepted, _, _⟩ := rightOpened
      rw [rightAccepted] at accepted
      rw [leftAccepted, accepted] at rejected
      cases rejected
    · obtain ⟨_, _, _, _, _, _, _, leftNode, _, _, leftRecorded, _⟩ := leftExpired
      obtain ⟨_, _, _, _, _, _, _, rightNode, _, _, rightRecorded, _⟩ := rightExpired
      rw [leftNode] at rightNode
      cases rightNode
      exact leftRecorded.trans rightRecorded.symm

/-- Two ends of a block from one start record and store alike every honest
reveal pending at the start. -/
theorem honest_end_congr {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin left right : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (leftPath : Relation.ReflTransGen Config.Step origin left)
    (rightPath : Relation.ReflTransGen Config.Step origin right)
    (leftSound : BlockRecordsSound who start finish origin left)
    (rightSound : BlockRecordsSound who start finish origin right)
    (leftOwners : DefaultOwners left) (rightOwners : DefaultOwners right)
    (leftDone : BlockDone finish left) (rightDone : BlockDone finish right)
    {event : (serviceGraph setup mode).EventId} (early : start ≤ event.val)
    (late : event.val < finish) (pending : event ∉ origin.cut.completed)
    (honest : (serviceGraph setup mode).actor? event ≠ some who) :
    completionOf left event = completionOf right event ∧
      left.outputs event = right.outputs event :=
  honest_end_congr_of_keys concurrent flat rfl begin begin leftPath rightPath leftSound
    rightSound leftOwners rightOwners leftDone rightDone early late pending honest

/-- A default of one block end is a default of another that records the block
alike, from starts with equal keys. -/
private theorem defaulted_of_block_records {who : Player} {start finish : Nat}
    {leftOrigin rightOrigin left right : (serviceGraph setup mode).Config}
    (keys : runKey leftOrigin = runKey rightOrigin)
    (leftPath : Relation.ReflTransGen Config.Step leftOrigin left)
    (rightPath : Relation.ReflTransGen Config.Step rightOrigin right)
    (leftSound : BlockRecordsSound who start finish leftOrigin left)
    (block : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ leftOrigin.cut.completed →
        completionOf left event = completionOf right event)
    {player : Player} (defaulted : player ∈ left.defaulted) : player ∈ right.defaulted := by
  have cuts : leftOrigin.cut = rightOrigin.cut := congrArg Prod.fst keys
  have records : completionOf leftOrigin = completionOf rightOrigin :=
    congrArg (fun key => key.2.2) keys
  obtain ⟨event, recorded⟩ := (mem_defaulted_iff_completionOf left player).mp defaulted
  obtain ⟨record, found, entry⟩ := Option.bind_eq_some_iff.mp recorded
  apply (mem_defaulted_iff_completionOf right player).mpr
  refine ⟨event, ?_⟩
  by_cases old : event ∈ leftOrigin.cut.completed
  · obtain ⟨earlier, earlierFound⟩ :=
      Option.isSome_iff_exists.mp ((completionOf_isSome_iff leftOrigin event).mpr old)
    have rightFound : completionOf rightOrigin event = some earlier := by
      rw [← records]
      exact earlierFound
    rw [Config.Step.path_completionOf_of_some rightPath event earlier rightFound,
      ← Config.Step.path_completionOf_of_some leftPath event earlier earlierFound, found]
    exact entry
  have done : event ∈ left.cut.completed :=
    (completionOf_isSome_iff left event).mp (by rw [found]; rfl)
  rcases leftSound event old done with ⟨quiet, _, _⟩ | ⟨early, late, _⟩
  · rw [quiet] at found
    cases found
    cases entry
  · rw [← block event early late old, found]
    exact entry

/-- **Block ends fixed by the deviator's records.** Two quiescent ends of a
block of concurrent reveals run by graph steps from starts with equal keys have
the same order-free key when they agree on the records and outputs of the
deviator's block reveals pending at the start. -/
theorem blockEnd_runKey_eq_of_owned_of_keys {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {leftOrigin rightOrigin left right : (serviceGraph setup mode).Config}
    (keys : runKey leftOrigin = runKey rightOrigin)
    (leftBegin : BlockStart start finish leftOrigin)
    (rightBegin : BlockStart start finish rightOrigin)
    (leftPath : Relation.ReflTransGen Config.Step leftOrigin left)
    (rightPath : Relation.ReflTransGen Config.Step rightOrigin right)
    (leftSound : BlockRecordsSound who start finish leftOrigin left)
    (rightSound : BlockRecordsSound who start finish rightOrigin right)
    (leftOwners : DefaultOwners left) (rightOwners : DefaultOwners right)
    (leftDone : BlockDone finish left) (rightDone : BlockDone finish right)
    (leftQuiet : left.Quiescent) (rightQuiet : right.Quiescent)
    (owned : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ leftOrigin.cut.completed →
      (serviceGraph setup mode).actor? event = some who →
        completionOf left event = completionOf right event ∧
          left.outputs event = right.outputs event) :
    runKey left = runKey right := by
  have cuts : leftOrigin.cut = rightOrigin.cut := congrArg Prod.fst keys
  have stores : leftOrigin.store = rightOrigin.store := congrArg (fun key => key.2.1) keys
  have records : completionOf leftOrigin = completionOf rightOrigin :=
    congrArg (fun key => key.2.2) keys
  have block (event : (serviceGraph setup mode).EventId) (early : start ≤ event.val)
      (late : event.val < finish) (pending : event ∉ leftOrigin.cut.completed) :
      completionOf left event = completionOf right event ∧
        left.outputs event = right.outputs event := by
    by_cases mine : (serviceGraph setup mode).actor? event = some who
    · exact owned event early late pending mine
    · exact honest_end_congr_of_keys concurrent flat keys leftBegin rightBegin leftPath
        rightPath leftSound rightSound leftOwners rightOwners leftDone rightDone early late
        pending mine
  have defaults : left.defaulted = right.defaulted := by
    ext player
    exact ⟨defaulted_of_block_records keys leftPath rightPath leftSound
        (fun event early late pending => (block event early late pending).1),
      defaulted_of_block_records keys.symm rightPath leftPath rightSound
        (fun event early late pending => (block event early late
          (by rw [cuts]; exact pending)).1.symm)⟩
  let base := fun event : (serviceGraph setup mode).EventId =>
    event ∈ leftOrigin.cut.completed ∨ (start ≤ event.val ∧ event.val < finish)
  have automatic {origin current : (serviceGraph setup mode).Config}
      (originCut : origin.cut = leftOrigin.cut)
      (sound : BlockRecordsSound who start finish origin current)
      (event : (serviceGraph setup mode).EventId) (done : event ∈ current.cut.completed)
      (unbased : ¬ base event) :
      completionOf current event = some ⟨event, none, none⟩ ∧
        current.outputs event = failureOutput event ∧
        ∃ owner, (serviceGraph setup mode).actor? event = some owner ∧
          owner ∈ current.defaulted := by
    rcases sound event (fun old => unbased (Or.inl (originCut ▸ old))) done with silent |
      ⟨early, late, _⟩
    · exact silent
    · exact (unbased (Or.inr ⟨early, late⟩)).elim
  have completed : left.cut.completed = right.cut.completed :=
    completed_eq_of_quiescent base
      (fun event based => based.elim (fun old => Config.Step.path_completed_mono leftPath old)
        (fun bounds => leftDone event bounds.2))
      (fun event based => based.elim (fun old => Config.Step.path_completed_mono rightPath
          (cuts ▸ old))
        (fun bounds => rightDone event bounds.2))
      (fun event done unbased => (automatic rfl leftSound event done unbased).2.2)
      (fun event done unbased => (automatic cuts.symm rightSound event done unbased).2.2)
      defaults leftQuiet rightQuiet
  have each (event : (serviceGraph setup mode).EventId) :
      completionOf left event = completionOf right event ∧
        left.outputs event = right.outputs event := by
    by_cases old : event ∈ leftOrigin.cut.completed
    · have rightOld : event ∈ rightOrigin.cut.completed := cuts ▸ old
      obtain ⟨record, recorded⟩ :=
        Option.isSome_iff_exists.mp ((completionOf_isSome_iff leftOrigin event).mpr old)
      have rightRecorded : completionOf rightOrigin event = some record := by
        rw [← records]
        exact recorded
      refine ⟨(Config.Step.path_completionOf_of_some leftPath event _ recorded).trans
        (Config.Step.path_completionOf_of_some rightPath event _ rightRecorded).symm, ?_⟩
      rw [outputs_path leftPath old, outputs_path rightPath rightOld]
      exact congrFun stores (.inr event)
    by_cases bounds : start ≤ event.val ∧ event.val < finish
    · exact block event bounds.1 bounds.2 old
    have unbased : ¬ base event := fun based => based.elim old bounds
    by_cases done : event ∈ left.cut.completed
    · have doneRight : event ∈ right.cut.completed := completed ▸ done
      obtain ⟨leftRecord, leftOutput, _⟩ := automatic rfl leftSound event done unbased
      obtain ⟨rightRecord, rightOutput, _⟩ :=
        automatic cuts.symm rightSound event doneRight unbased
      exact ⟨leftRecord.trans rightRecord.symm, leftOutput.trans rightOutput.symm⟩
    · have doneRight : event ∉ right.cut.completed := fun finished => done (completed ▸ finished)
      refine ⟨((completionOf_eq_none_iff left event).mpr done).trans
        ((completionOf_eq_none_iff right event).mpr doneRight).symm, ?_⟩
      rw [Option.not_isSome_iff_eq_none.mp (fun stored =>
          done ((left.output_available event).mp stored)),
        Option.not_isSome_iff_eq_none.mp (fun stored =>
          doneRight ((right.output_available event).mp stored))]
  have cutEq : left.cut = right.cut := EventOrder.Cut.ext completed
  have storeEq : left.store = right.store := by
    funext field
    cases field with
    | inl input =>
        change some (left.inputs input) = some (right.inputs input)
        rw [Config.Step.path_inputs_eq leftPath, Config.Step.path_inputs_eq rightPath]
        exact congrFun stores (.inl input)
    | inr event => exact (each event).2
  have recordEq : completionOf left = completionOf right := funext fun event => (each event).1
  change (left.cut, (left.store, completionOf left)) =
    (right.cut, (right.store, completionOf right))
  rw [cutEq, storeEq, recordEq]

/-- **Block ends fixed by the deviator's records.** Two quiescent ends of a
block of concurrent reveals run from one start by graph steps have the same
order-free key when they agree on the records and outputs of the deviator's
block reveals pending at the start. -/
theorem blockEnd_runKey_eq_of_owned {who : Player} {start finish : Nat}
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {origin left right : (serviceGraph setup mode).Config}
    (begin : BlockStart start finish origin)
    (leftPath : Relation.ReflTransGen Config.Step origin left)
    (rightPath : Relation.ReflTransGen Config.Step origin right)
    (leftSound : BlockRecordsSound who start finish origin left)
    (rightSound : BlockRecordsSound who start finish origin right)
    (leftOwners : DefaultOwners left) (rightOwners : DefaultOwners right)
    (leftDone : BlockDone finish left) (rightDone : BlockDone finish right)
    (leftQuiet : left.Quiescent) (rightQuiet : right.Quiescent)
    (owned : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → event ∉ origin.cut.completed →
      (serviceGraph setup mode).actor? event = some who →
        completionOf left event = completionOf right event ∧
          left.outputs event = right.outputs event) :
    runKey left = runKey right :=
  blockEnd_runKey_eq_of_owned_of_keys concurrent flat rfl begin begin leftPath rightPath
    leftSound rightSound leftOwners rightOwners leftDone rightDone leftQuiet rightQuiet owned

end Vegas
