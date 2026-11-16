module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveGuardConformance
public import Vegas.EventGraph.SchedulerReplay
public import Vegas.EventGraph.RevealRelaxedScheduling
public import Vegas.EventGraph.LastSchedulerErasure
public import Vegas.EventGraph.FootprintIndependence
public import Vegas.EventGraph.ErasureTwin
public import Vegas.Pending.CanonicalKeyPublication
public import Vegas.EventGraph.PrefixPolicy
public import Vegas.EventGraph.StoredBindingProfile
public import Vegas.EventGraph.PolicyCongruence
public import Vegas.EventGraph.BindingSubmission

@[expose] public section

/-! # Effective openings

An opening of a publication is accepted when its binding holds a value and the
publication's checks accept it. The owner can tell before acting: the binding
is its own field and the checks read only public fields. The effective opening
of a profile opens a publication exactly when the opening would be accepted and
withholds it otherwise; elsewhere it follows the profile.

Its kernel at a publication reads only the publication's own read footprint.
That footprint has completed when the publication is ready, so completing a
concurrently ready event leaves the kernel unchanged. Effective opening preserves
ready independence and binding submission, and commutes with source-prefix observation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Whether an opening of a publication would be accepted at a store. -/
def openingAccepted (event : graph.EventId) (store : EventGraph.Store graph.layout) : Bool :=
  match nodeView graph event with
  | .resolve _ _ binding checks _ _ =>
      match EventCode.resolveOutput? binding checks true store with
      | some (.success _) => true
      | _ => false
  | .bind .. => false
  | .sample .. => false

/-- **The effective opening.** At a publication, open exactly when the opening
would be accepted on the observed store; elsewhere, follow the base profile. -/
def effectiveOpening (base : graph.BehavioralProfile) : graph.BehavioralProfile :=
  fun who event actor observation active =>
    match nodeView graph event with
    | .resolve _ _ _ _ outputEq _ =>
        PMF.pure (cast (congrArg EventField.Action outputEq.symm)
          (openingAccepted event observation.store))
    | .bind .. => base who event actor observation active
    | .sample .. => base who event actor observation active

theorem effectiveOpening_of_resolve (base : graph.BehavioralProfile) {who : Player}
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (actor : (graph.nodes event).actor = some who) (observation : graph.PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    effectiveOpening base who event actor observation active =
      PMF.pure (cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event observation.store)) := by
  unfold effectiveOpening
  rw [node]

theorem effectiveOpening_of_not_publication (base : graph.BehavioralProfile) {who : Player}
    {event : graph.EventId} (notPublication : ¬ (graph.outputLayout event).IsPublication)
    (actor : (graph.nodes event).actor = some who) (observation : graph.PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    effectiveOpening base who event actor observation active =
      base who event actor observation active := by
  unfold effectiveOpening
  cases view : nodeView graph event with
  | resolve owner payload binding checks outputEq codeEq =>
      exact (notPublication (by rw [outputEq]; trivial)).elim
  | bind => rfl
  | sample => rfl

omit [DecidableEq Player] in
/-- Acceptance reads only the publication's read footprint. -/
theorem openingAccepted_congr (event : graph.EventId) {left right : EventGraph.Store graph.layout}
    (agree : Store.AgreeOn left right (graph.nodes event).readFields) :
    openingAccepted event left = openingAccepted event right := by
  unfold openingAccepted
  cases view : nodeView graph event with
  | resolve owner payload binding checks outputEq codeEq =>
      have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
      rw [codeEq] at footprint
      have same := EventCode.resolveOutput?_congr binding checks true left right (by
        intro field member
        apply agree
        rw [← footprint]
        exact member)
      simp only [same]
  | bind => rfl
  | sample => rfl

/-- The owner sees whether its opening would be accepted. -/
theorem openingAccepted_playerStore (event : graph.EventId) {owner : Player}
    (actor : graph.actor? event = some owner) (store : EventGraph.Store graph.layout) :
    openingAccepted event (graph.playerStore owner store) = openingAccepted event store := by
  unfold openingAccepted
  cases view : nodeView graph event with
  | resolve actorName payload binding checks outputEq codeEq =>
      have sameActor : actorName = owner :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans actor)
      subst actorName
      have bound := binding.get?_playerStore owner store rfl
      have checked (proposal : PublicationResult (L.Val payload)) :
          GuardCheck.allAccepted? checks (graph.playerStore owner store) proposal =
            GuardCheck.allAccepted? checks store proposal := by
        rw [← GuardCheck.allAccepted?_publicStore checks (graph.playerStore owner store),
          graph.publicStore_playerStore, GuardCheck.allAccepted?_publicStore]
      simp only [EventCode.resolveOutput?, bound, checked]
  | bind => rfl
  | sample => rfl

omit [DecidableEq Player] in
/-- A publication's node is a resolution. -/
theorem exists_resolve_of_publication {event : graph.EventId}
    (publication : (graph.outputLayout event).IsPublication) :
    ∃ (owner : Player) (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (GuardCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
        .resolve owner payload binding checks),
      nodeView graph event = .resolve owner payload binding checks outputEq codeEq := by
  cases view : nodeView graph event with
  | resolve owner payload binding checks outputEq codeEq =>
      exact ⟨owner, payload, binding, checks, outputEq, codeEq, rfl⟩
  | bind owner payload outputEq codeEq =>
      rw [outputEq] at publication
      exact publication.elim
  | sample payload law outputEq codeEq =>
      rw [outputEq] at publication
      exact publication.elim

/-- **The effective opening reads only read footprints at publications.** -/
theorem effectiveOpening_footprint (base : graph.BehavioralProfile) :
    graph.FootprintOblivious (effectiveOpening base) fun _ => True := by
  intro owner _ event actor publication left right leftActive rightActive agree
  obtain ⟨_, _, _, _, _, _, node⟩ := exists_resolve_of_publication publication
  rw [effectiveOpening_of_resolve base node actor left leftActive,
    effectiveOpening_of_resolve base node actor right rightActive,
    openingAccepted_congr event agree]

/-- A deviation from the effective opening keeps the other players footprint
oblivious. -/
theorem effectiveOpening_update_footprint (base : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) :
    graph.FootprintOblivious
      (GameTheory.Profile.update (sig := graph.gameSignature) (effectiveOpening base) who policy)
      fun owner => owner ≠ who := by
  intro owner different event actor publication left right leftActive rightActive agree
  simp only [GameTheory.Profile.update_of_ne _ _ different]
  exact effectiveOpening_footprint base owner trivial event actor publication left right
    leftActive rightActive agree

/-- The normalized effective opening at an active owner's publication opens
exactly when the opening is accepted on the configuration's store. -/
theorem normalize_effectiveOpening_publication (base : graph.BehavioralProfile)
    (config : graph.Config) {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (actor : (graph.nodes event).actor = some owner)
    (active : owner ∉ (graph.playerObserve owner config).defaulted) :
    graph.normalizeProfile (effectiveOpening base) owner event actor
        (graph.playerObserve owner config) active =
      PMF.pure (cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event config.store)) := by
  unfold normalizeProfile normalizePolicy
  rw [effectiveOpening_of_resolve base node actor]
  change PMF.pure (cast _ (openingAccepted event (graph.playerStore owner config.store))) = _
  rw [openingAccepted_playerStore event actor]

/-- A rejected opening publishes a failure whatever is disclosed. -/
theorem step_of_opening_rejected (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (rejected : openingAccepted event config.store = false) (action : graph.Action event) :
    config.step event ready action = PMF.pure (config.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm) .failure)) := by
  have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
  rw [codeEq] at footprint
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (config.store field).isSome = true := by
    intro field member
    apply config.read_available ready
    rw [← footprint]
    exact member
  have opened : EventCode.resolveOutput? binding checks true config.store = some .failure := by
    have defined := EventCode.resolveOutput?_isSome binding checks true config.store available
    unfold openingAccepted at rejected
    rw [node] at rejected
    dsimp only at rejected
    cases result : EventCode.resolveOutput? binding checks true config.store with
    | none => rw [result] at defined; cases defined
    | some output =>
        cases output with
        | failure => rfl
        | success value => rw [result] at rejected; cases rejected
  have anyDisclose (disclose : Bool) :
      EventCode.resolveOutput? binding checks disclose config.store = some .failure := by
    cases disclose
    · exact EventCode.resolveOutput?_false_eq_failure binding checks config.store available
    · exact opened
  obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
      action = cast (congrArg EventField.Action outputEq.symm) disclose :=
    ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
  rw [config.step_eq_map_of_code event ready outputEq (.resolve owner payload binding checks)
    codeEq disclose (PMF.pure .failure) (by rw [EventCode.resolve_eval?, anyDisclose]; rfl),
    PMF.pure_map]

/-- **The effective opening and the always-open profile are twins.** For a base
profile that opens every publication of an active owner, the normalized
deviations of one player from the base and from its effective opening have the
same law of erased successors at every step: they act alike except at a rejected
opening of another player, where withholding and opening both publish a failure
and default the owner. -/
theorem erasureTwins_effectiveOpening (base : graph.BehavioralProfile)
    (opens : ∀ owner event (actor : (graph.nodes event).actor = some owner)
      (publication : (graph.outputLayout event).IsPublication)
      (observation : graph.PlayerObservation owner) (active : owner ∉ observation.defaulted),
      base owner event actor observation active =
        PMF.pure (EventField.openAction _ publication))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    ErasureTwins
      (graph.normalizeProfile
        (GameTheory.Profile.update (sig := graph.gameSignature) (effectiveOpening base) who
          policy))
      (graph.normalizeProfile
        (GameTheory.Profile.update (sig := graph.gameSignature) base who policy)) := by
  apply erasureTwins_of_pointwise
  intro config event ready
  cases ownerEq : (graph.nodes event).actor with
  | none =>
      left
      rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      by_cases inactive : owner ∈ config.defaulted
      · left
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq, dite_eq_left inactive,
          dite_eq_left inactive]
      by_cases same : owner = who
      · subst owner
        left
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq,
          dite_eq_right inactive, dite_eq_right inactive]
        simp only [normalizeProfile, normalizePolicy, GameTheory.Profile.update_same]
      by_cases publication : (graph.outputLayout event).IsPublication
      · obtain ⟨actorName, payload, binding, checks, outputEq, codeEq, node⟩ :=
          exists_resolve_of_publication publication
        have actorSame : actorName = owner :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans ownerEq)
        subst actorName
        have effective : actionLaw (graph.normalizeProfile
            (GameTheory.Profile.update (sig := graph.gameSignature) (effectiveOpening base) who
              policy)) config event =
            PMF.pure (cast (congrArg EventField.Action outputEq.symm)
              (openingAccepted event config.store)) := by
          rw [actionLaw_of_actor _ _ ownerEq, dite_eq_right inactive]
          simp only [normalizeProfile, normalizePolicy, GameTheory.Profile.update_of_ne _ _ same]
          rw [effectiveOpening_of_resolve base node ownerEq]
          change PMF.pure (cast _ (openingAccepted event
            (graph.playerStore owner config.store))) = _
          rw [openingAccepted_playerStore event ownerEq]
        have always : actionLaw (graph.normalizeProfile
            (GameTheory.Profile.update (sig := graph.gameSignature) base who policy)) config
              event =
            PMF.pure (cast (congrArg EventField.Action outputEq.symm) true) := by
          rw [actionLaw_of_actor _ _ ownerEq, dite_eq_right inactive]
          simp only [normalizeProfile, normalizePolicy, GameTheory.Profile.update_of_ne _ _ same]
          rw [opens owner event ownerEq publication, openAction_eq_cast_true outputEq publication]
        cases accepted : openingAccepted event config.store
        · right
          refine ⟨_, _, by rw [effective, accepted], always, ?_⟩
          rw [step_of_opening_rejected config event ready node accepted,
            step_of_opening_rejected config event ready node accepted, PMF.pure_map,
            PMF.pure_map]
          apply congrArg PMF.pure
          exact Config.erase_complete_of_defaulting config event ready owner ownerEq inactive _ _ _
            (defaultEvent_of_failed_publication event outputEq codeEq _)
            (defaultEvent_of_failed_publication event outputEq codeEq _)
        · left
          rw [effective, always, accepted]
      · left
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq,
          dite_eq_right inactive, dite_eq_right inactive]
        simp only [normalizeProfile, normalizePolicy, GameTheory.Profile.update_of_ne _ _ same]
        rw [effectiveOpening_of_not_publication base publication ownerEq]

/-- Effective opening and an always-open base have the same erased event laws,
without changing either profile's nonpublication kernels. -/
theorem erasureTwins_effectiveOpening_honest (base : graph.BehavioralProfile)
    (opens : ∀ owner event (actor : (graph.nodes event).actor = some owner)
      (publication : (graph.outputLayout event).IsPublication)
      (observation : graph.PlayerObservation owner) (active : owner ∉ observation.defaulted),
      base owner event actor observation active =
        PMF.pure (EventField.openAction _ publication)) :
    ErasureTwins (effectiveOpening base) base := by
  apply erasureTwins_of_pointwise
  intro config event ready
  cases ownerEq : (graph.nodes event).actor with
  | none =>
      left
      rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      by_cases inactive : owner ∈ config.defaulted
      · left
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq, dite_eq_left inactive,
          dite_eq_left inactive]
      by_cases publication : (graph.outputLayout event).IsPublication
      · obtain ⟨actorName, payload, binding, checks, outputEq, codeEq, node⟩ :=
          exists_resolve_of_publication publication
        have actorSame : actorName = owner :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans ownerEq)
        subst actorName
        have effective : actionLaw (effectiveOpening base) config event =
            PMF.pure (cast (congrArg EventField.Action outputEq.symm)
              (openingAccepted event config.store)) := by
          rw [actionLaw_of_actor _ _ ownerEq, dite_eq_right inactive]
          rw [effectiveOpening_of_resolve base node ownerEq]
          change PMF.pure (cast _ (openingAccepted event
            (graph.playerStore owner config.store))) = _
          rw [openingAccepted_playerStore event ownerEq]
        have always : actionLaw base config event =
            PMF.pure (cast (congrArg EventField.Action outputEq.symm) true) := by
          rw [actionLaw_of_actor _ _ ownerEq, dite_eq_right inactive]
          rw [opens owner event ownerEq publication, openAction_eq_cast_true outputEq publication]
        cases accepted : openingAccepted event config.store
        · right
          refine ⟨_, _, by rw [effective, accepted], always, ?_⟩
          rw [step_of_opening_rejected config event ready node accepted,
            step_of_opening_rejected config event ready node accepted, PMF.pure_map,
            PMF.pure_map]
          apply congrArg PMF.pure
          exact Config.erase_complete_of_defaulting config event ready owner ownerEq inactive _ _ _
            (defaultEvent_of_failed_publication event outputEq codeEq _)
            (defaultEvent_of_failed_publication event outputEq codeEq _)
        · left
          rw [effective, always, accepted]
      · left
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq,
          dite_eq_right inactive, dite_eq_right inactive]
        rw [effectiveOpening_of_not_publication base publication ownerEq]


private theorem actionLaw_effectiveOpening_of_not_publication
    (base : graph.BehavioralProfile) (config : graph.Config) (event : graph.EventId)
    (plain : ¬ (graph.outputLayout event).IsPublication) :
    actionLaw (effectiveOpening base) config event = actionLaw base config event := by
  cases actor : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
  | some owner =>
      rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left inactive, dite_eq_left inactive]
      · rw [dite_eq_right inactive, dite_eq_right inactive]
        exact effectiveOpening_of_not_publication base plain actor _ _

/-- Effective openings preserve ready independence of every base profile. -/
theorem _root_.Vegas.EventGraph.ReadyIndependent.effectiveOpening
    {base : graph.BehavioralProfile} (independent : ReadyIndependent base) :
    ReadyIndependent (EventGraphRuntime.effectiveOpening base) where
  actorsDiffer := independent.actorsDiffer
  stable config event other ready otherReady different action value := by
    by_cases publication : (graph.outputLayout event).IsPublication
    swap
    · rw [actionLaw_effectiveOpening_of_not_publication base _ _ publication,
        actionLaw_effectiveOpening_of_not_publication base _ _ publication]
      exact independent.stable config ready otherReady different action value
    cases actor : (graph.nodes event).actor with
    | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
    | some owner =>
        rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
        have foreign : graph.actor? other ≠ some owner :=
          fun same => independent.actorsDiffer config ready otherReady different.symm owner actor
            same
        have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
          owner foreign
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
        · rw [dite_eq_right (fun present => inactive (member.mp present)), dite_eq_right inactive]
          exact effectiveOpening_footprint base owner trivial event actor publication _ _ _ _
            (playerStore_complete_agreeOn owner config ready otherReady action value)
  congr {left right} same event := by
    by_cases publication : (graph.outputLayout event).IsPublication
    swap
    · rw [actionLaw_effectiveOpening_of_not_publication base _ _ publication,
        actionLaw_effectiveOpening_of_not_publication base _ _ publication]
      exact independent.congr same event
    have stores : left.store = right.store := congrArg (fun key => key.2.1) same
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaults := defaulted_eq_of_completionOf_eq records
    cases actor : (graph.nodes event).actor with
    | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
    | some owner =>
        rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
        by_cases inactive : owner ∈ left.defaulted
        · rw [dite_eq_left inactive, dite_eq_left (defaults ▸ inactive)]
        · rw [dite_eq_right inactive, dite_eq_right (defaults ▸ inactive)]
          apply effectiveOpening_footprint base owner trivial event actor publication
          intro field _read
          change graph.playerStore owner left.store field =
            graph.playerStore owner right.store field
          rw [stores]

/-- Source-prefix observation and effective opening commute: neither changes the store. -/
theorem prefixProfile_effectiveOpening (base : graph.BehavioralProfile) :
    graph.prefixProfile (effectiveOpening base) = effectiveOpening (graph.prefixProfile base) := by
  funext who event actor observation active
  unfold prefixProfile prefixPolicy effectiveOpening
  cases node : nodeView graph event <;> rfl

/-- Effective opening does not change any binding submission. -/
theorem _root_.Vegas.EventGraph.SubmitsBindings.effectiveOpening
    {base : graph.BehavioralProfile} (submits : graph.SubmitsBindings base) :
    graph.SubmitsBindings (EventGraphRuntime.effectiveOpening base) := by
  intro who event actor observation active action selected
  by_cases publication : (graph.outputLayout event).IsPublication
  · exact EventField.submitted_of_publication _ publication _
  · rw [effectiveOpening_of_not_publication base publication actor] at selected
    exact submits who event actor observation active action selected

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem storedBindingLaw_publication
    (field : EventField Player L) (publication : field.IsPublication)
    (stored : Option field.Value) (original : PMF field.Action) :
    field.storedBindingLaw stored original = original := by
  cases field with
  | publication payload => rfl
  | publicData payload => cases publication
  | privateInput owner payload => cases publication
  | binding owner payload => cases publication

/-- Freezing binding results commutes with effective opening. -/
theorem effectiveOpening_freezeBindingsBefore
    (profile : graph.BehavioralProfile) (start rank : Nat) (ghost : graph.Config) :
    effectiveOpening (graph.freezeBindingsBefore profile start rank ghost) =
      graph.freezeBindingsBefore (effectiveOpening profile) start rank ghost := by
  funext who event actor observation active
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [effectiveOpening, node, freezeBindingsBefore]
  | sample payload law outputEq codeEq =>
      simp only [effectiveOpening, node, freezeBindingsBefore]
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [effectiveOpening, node, freezeBindingsBefore]
      by_cases inside : start ≤ event.val ∧ event.val < rank
      · rw [ite_eq_left inside]
        exact (storedBindingLaw_publication (graph.outputLayout event)
          (by rw [outputEq]; trivial) _ _).symm
      · rw [ite_eq_right inside]

/-- Effective opening preserves the full canonical law on a binding interval. -/
theorem runPlan_effectiveOpening_binding_interval
    (profile : graph.BehavioralProfile) (count start : Nat) (origin : graph.Config)
    (ordered : origin.cut.IsPrefix start) (bounded : start + count ≤ graph.order.eventCount)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
      ∃ owner payload, graph.outputLayout event = .binding owner payload) :
    graph.runPlan (graph.policyPlan (effectiveOpening profile) graph.canonicalScheduler)
        count origin =
      graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) count origin := by
  apply runPlan_canonical_prefix_congr _ _ count start origin ordered bounded
  intro event lower upper who actor observation active
  obtain ⟨owner, payload, outputEq⟩ := bindings event lower upper
  exact effectiveOpening_of_not_publication profile (by rw [outputEq]; exact id) actor _ _

/-- Updating a focal policy retains effective-opening equivalence on a binding interval. -/
theorem runPlan_prefix_effectiveOpening_update_binding_interval
    (profile : graph.BehavioralProfile) (focal : Player) (policy : graph.BehavioralPolicy focal)
    (count start : Nat) (origin : graph.Config)
    (ordered : origin.cut.IsPrefix start) (bounded : start + count ≤ graph.order.eventCount)
    (bindings : ∀ event : graph.EventId, start ≤ event.val → event.val < start + count →
      ∃ owner payload, graph.outputLayout event = .binding owner payload) :
    graph.runPlan (graph.policyPlan
        (graph.prefixProfile (Function.update (effectiveOpening profile) focal policy))
        graph.canonicalScheduler) count origin =
      graph.runPlan (graph.policyPlan
        (graph.prefixProfile (Function.update profile focal policy))
        graph.canonicalScheduler) count origin := by
  apply runPlan_canonical_prefix_congr _ _ count start origin ordered bounded
  intro event lower upper who actor observation active
  simp only [prefixProfile, prefixPolicy]
  by_cases own : who = focal
  · subst who
    simp only [Function.update_self]
  · simp only [Function.update_of_ne own]
    obtain ⟨owner, payload, outputEq⟩ := bindings event lower upper
    exact effectiveOpening_of_not_publication profile (by rw [outputEq]; exact id) actor _ _

end Vegas.EventGraphRuntime
