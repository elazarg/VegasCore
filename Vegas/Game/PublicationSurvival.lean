module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealRunCoupling
public import Vegas.Game.RevealRunPoint
public import Vegas.Game.RevealServiceEffectiveTimely
public import Vegas.Pending.CanonicalOutcomePublication
public import Vegas.EventGraph.DefaultFailure
public import Vegas.EventGraph.PrefixRestriction
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # Surviving public phases under arbitrary focal clients

Ordinary source-opening continuation law is an internal potential, independent
of the actual honest clients' reference. Native public runs preserve that
potential until the focal player defaults. Surviving complete traffic has an
exact channel through the full source successor view, including nonflat runs.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Against actual effective-opening clients, one raw unilateral public round
preserves the clear ordinary-opening potential unless it defaults the deviator.
Deadline protection is derived from the original asynchronous contract. -/
theorem publication_round_clear_or_focal_default
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (current next : (serviceApplication setup deps duration leaks).Execution)
    (supported : current ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      current.environmentRecall.length).support)
    (bounded : current.environmentRecall.length ≤ horizon)
    (law : outcomeLaw profile Config.defaulted current.application.config = PMF.pure ∅)
    (publications : ∀ event, current.application.config.cut.Ready event →
      ((serviceGraph setup deps).outputLayout event).IsPublication)
    (moved : next ∈ ((serviceApplication setup deps duration leaks).round scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      current).support) :
    focal ∈ next.application.config.defaulted ∨
      (next.application.config.defaulted = ∅ ∧ canonicalLaw profile next.application.config =
        canonicalLaw profile current.application.config) := by
  let G := serviceGraph setup deps
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  have decides : ∀ (config : G.Config) (event : G.EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef G.layout (.binding owner payload))
      (checks : List (GuardCheck G.layout payload))
      (outputEq : G.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
        .resolve owner payload binding checks),
      nodeView G event = .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : G.actor? event = some owner)
        (active : owner ∉ (G.playerObserve owner config).defaulted),
      effectiveOpening reference owner event actor (G.playerObserve owner config) active =
        PMF.pure (cast (congrArg EventField.Action outputEq.symm)
          (openingAccepted event config.store)) := by
    intro config event owner payload binding checks outputEq codeEq node actor active
    rw [effectiveOpening_of_resolve reference node actor]
    change PMF.pure (cast _ (openingAccepted event (G.playerStore owner config.store))) = _
    rw [openingAccepted_playerStore event actor]
  apply reactive_round_publication_clear_or_focal_default independent opens
    (serviceTimeouts setup deps duration) leaks scheduler players current next focal law
    publications _ moved
  intro event owner ready actor foreign
  have follows : players owner = serviceReferenceTurnPolicy setup deps duration leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening reference) owner := by
    simp only [players, Function.update_of_ne foreign]
  exact effectivePublication_withinDeadline contract timely players owner
    (effectiveOpening reference) decides follows current.environmentRecall.length bounded
    current supported event
    (relaxed.actorSerial event) actor ready (publications event ready)
    (openingAccepted_of_defaultLaw independent opens current.application.config law event ready
      (publications event ready))

/-- A complete native public run retains the ordinary-opening potential on
surviving support. Failed native branches are identified by actual focal default. -/
theorem publication_run_survives
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    (supported : origin ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      origin.environmentRecall.length).support)
    (bounded : origin.environmentRecall.length ≤ horizon)
    (inside : InBlock start finish origin.application.config)
    (law : outcomeLaw profile Config.defaulted origin.application.config = PMF.pure ∅)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon origin).support) :
    BlockDone finish final.application.config ∧
      (focal ∈ final.application.config.defaulted ∨
        (final.application.config.defaulted = ∅ ∧ canonicalLaw profile final.application.config =
          canonicalLaw profile origin.application.config)) := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  let stop := fun current : app.Execution => BlockDone finish current.application.config
  let holds := fun (remaining : Nat) (current : app.Execution) =>
    current ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler players
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + remaining ≤ horizon ∧
    (¬ stop current → InBlock start finish current.application.config) ∧
    (focal ∈ current.application.config.defaulted ∨
      canonicalLaw profile current.application.config =
        canonicalLaw profile origin.application.config)
  have preserved : ∀ remaining current, holds (remaining + 1) current → ¬ stop current →
      ∀ next ∈ (app.round scheduler players current).support, holds remaining next := by
    intro remaining current valid running next moved
    obtain ⟨currentSupport, currentBound, currentInside, potential⟩ := valid
    have path := reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      players current next moved
    have length := app.round_environmentRecall_length scheduler players current next moved
    refine ⟨?_, by omega, fun unfinished => (currentInside running).path (run.shaped relaxed)
      path unfinished, ?_⟩
    · rw [length, app.roundsFrom_succ]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨current, currentSupport, moved⟩
    · rcases potential with failed | same
      · exact Or.inl (Config.Step.path_defaulted_mono path failed)
      have currentLaw : outcomeLaw profile Config.defaulted current.application.config =
          PMF.pure ∅ :=
        (outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
          (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
          same).trans law
      have publications (event : (serviceGraph setup deps).EventId)
          (ready : current.application.config.cut.Ready event) :
          ((serviceGraph setup deps).outputLayout event).IsPublication := by
        obtain ⟨lower, upper⟩ := (run.shaped relaxed) _ (currentInside running) running event ready
        exact run.publications event lower upper
      rcases publication_round_clear_or_focal_default scheduler bound relaxed contract timely
          profile reference
          independent opens focal deviation current next currentSupport (by omega) currentLaw
          publications moved with failed | ⟨_clear, advanced⟩
      · exact Or.inl failed
      · exact Or.inr (advanced.trans same)
  have initial : holds (horizon - origin.environmentRecall.length) origin :=
    ⟨supported, by omega, fun _ => inside, Or.inr rfl⟩
  obtain ⟨_, _, _, _, result⟩ := app.runUntil_support_holds scheduler players stop holds preserved
    (horizon - origin.environmentRecall.length) origin initial final reached
  have done := runUntilHorizon_stop contract players stop
    (fun current terminal event _ => by rw [terminal]; exact Finset.mem_univ event)
    origin supported bounded final reached
  refine ⟨done, result.elim Or.inl (fun same => Or.inr ⟨?_, same⟩)⟩
  exact EventGraphRuntime.defaulted_eq_empty_of_outcomeLaw profile final.application.config
    ((outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
      (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
      same).trans law)

end Vegas



namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem failed_of_cast_failure {field : EventField Player L} {payload : L.Ty}
    (same : field = .publication payload) (value : field.Value)
    (failed : cast (congrArg EventField.Value same) value = .failure) :
    EventField.FailedValue field value := by
  cases same
  change value = .failure at failed
  rw [failed]
  rfl

/-- A completed publication of an active owner has a successful stored value. -/
private theorem publication_success_of_active
    {inputs : (serviceGraph setup deps).Inputs}
    {donor : (serviceGraph setup deps).Config} (reachable : donor.Reachable inputs)
    (event : (serviceGraph setup deps).EventId) (done : event ∈ donor.cut.completed)
    (owner : Player) (owned : (serviceGraph setup deps).actor? event = some owner)
    (active : owner ∉ donor.defaulted) (payload : L.Ty)
    (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload) :
    ∃ value, (⟨.inr event, outputEq⟩ :
      FieldRef (serviceGraph setup deps).layout (.publication payload)).get? donor.store =
        some (.success value) := by
  let field : FieldRef (serviceGraph setup deps).layout (.publication payload) :=
    ⟨.inr event, outputEq⟩
  obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp
    (field.get?_isSome donor.store ((donor.output_available event).mpr done))
  cases result with
  | success value => exact ⟨value, stored⟩
  | failure =>
    obtain ⟨raw, rawStored⟩ := Option.isSome_iff_exists.mp ((donor.output_available event).mpr done)
    have typed : cast (congrArg EventField.Value outputEq) raw = .failure := by
      change cast (congrArg Option (congrArg EventField.Value outputEq))
        (donor.outputs event) = some .failure at stored
      rw [rawStored, cast_option_some (congrArg EventField.Value outputEq) raw] at stored
      exact Option.some.inj stored
    have publication : ((serviceGraph setup deps).outputLayout event).IsPublication := by
      rw [outputEq]
      trivial
    exact (active (reachable.defaulted_of_failed_publication event owner owned publication
      ⟨raw, rawStored, failed_of_cast_failure outputEq raw typed⟩)).elim

end Vegas

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- First focal failure is a public stop. Up to that stop, the entire focal
traffic law depends on the ordinary-open source successor only through its
complete post-view, including in a public run with repeated owners. -/
theorem publication_first_failure_traffic_congr
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (left right : (serviceApplication setup deps duration leaks).Execution)
    (leftBoundary : PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start left)
    (rightBoundary : PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start right)
    (leftDonor rightDonor : (serviceGraph setup deps).Config)
    {leftInputs rightInputs : (serviceGraph setup deps).Inputs}
    (leftReach : leftDonor.Reachable leftInputs) (rightReach : rightDonor.Reachable rightInputs)
    (leftPrefix : leftDonor.cut.IsPrefix finish) (rightPrefix : rightDonor.cut.IsPrefix finish)
    (leftLaw : outcomeLaw profile Config.defaulted leftDonor = PMF.pure ∅)
    (rightLaw : outcomeLaw profile Config.defaulted rightDonor = PMF.pure ∅)
    (leftPotential : canonicalLaw profile left.application.config = canonicalLaw profile leftDonor)
    (rightPotential : canonicalLaw profile right.application.config =
      canonicalLaw profile rightDonor)
    (postViews : keyView focal (runKey leftDonor) = keyView focal (runKey rightDonor))
    (sameTraffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right) :
    ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config ∨
        focal ∈ current.application.config.defaulted) horizon left).map
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
    ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config ∨
        focal ∈ current.application.config.defaulted) horizon right).map
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
  let stop := fun current : app.Execution => BlockDone finish current.application.config ∨
    focal ∈ current.application.config.defaulted
  have lawOf {current donor : G.Config}
      (potential : canonicalLaw profile current = canonicalLaw profile donor)
      (law : outcomeLaw profile Config.defaulted donor = PMF.pure ∅) :
      outcomeLaw profile Config.defaulted current = PMF.pure ∅ :=
    (outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
      (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
      potential).trans law
  have decides : ∀ (config : G.Config) (event : G.EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef G.layout (.binding owner payload))
      (checks : List (GuardCheck G.layout payload))
      (outputEq : G.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
        .resolve owner payload binding checks),
      nodeView G event = .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : G.actor? event = some owner)
        (active : owner ∉ (G.playerObserve owner config).defaulted),
      effectiveOpening reference owner event actor (G.playerObserve owner config) active =
        PMF.pure (cast (congrArg EventField.Action outputEq.symm)
          (openingAccepted event config.store)) := by
    intro config event owner payload binding checks outputEq codeEq node actor active
    rw [effectiveOpening_of_resolve reference node actor]
    change PMF.pure (cast _ (openingAccepted event (G.playerStore owner config.store))) = _
    rw [openingAccepted_playerStore event actor]
  have observedStop (current other : app.Execution) (same : traffic current = traffic other) :
      stop current ↔ stop other := by
    have publics : current.application.publicView = other.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) same
    have cuts := cut_eq_of_publicView_eq publics
    have views : current.application.playerView focal = other.application.playerView focal :=
      congrArg (fun value => value.2.2.2.2.1) same
    have defaults := congrArg EventPlayerObservation.defaulted
      (State.playerView_observation_eq current.application other.application focal views)
    simp only [playerObserve_defaulted] at defaults
    change (BlockDone finish current.application.config ∨ _) ↔
      (BlockDone finish other.application.config ∨ _)
    simp only [BlockDone, cuts, defaults]
  let good := fun (origin : app.Execution) (donor : G.Config)
      (remaining : Nat) (current : app.Execution) =>
    current ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler players
      current.environmentRecall.length).support ∧
    current.environmentRecall.length + remaining ≤ horizon ∧
    Relation.ReflTransGen Config.Step origin.application.config current.application.config ∧
    (focal ∈ current.application.config.defaulted ∨
      canonicalLaw profile current.application.config = canonicalLaw profile donor)
  have goodRound (donor : G.Config)
      (donorLaw : outcomeLaw profile Config.defaulted donor = PMF.pure ∅)
      (origin : app.Execution)
      (originBoundary : PhaseBoundary scheduler players horizon start origin) :
      ∀ n current, good origin donor (n + 1) current → ¬ stop current →
        ∀ next ∈ (app.round scheduler players current).support, good origin donor n next := by
    intro n current valid running next moved
    obtain ⟨currentSupport, currentBound, currentPath, potential⟩ := valid
    have length := app.round_environmentRecall_length scheduler players current next moved
    refine ⟨?_, by omega, currentPath.trans (reactive_round_graph_steps
      (serviceTimeouts setup deps duration) leaks scheduler players current next moved), ?_⟩
    · rw [length, app.roundsFrom_succ]
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨current, currentSupport, moved⟩
    obtain potential | potential := potential
    · exact (running (Or.inr potential)).elim
    have currentLaw := lawOf potential donorLaw
    have readyPublic (event : G.EventId) (ready : current.application.config.cut.Ready event) :
        (G.outputLayout event).IsPublication := by
      have earlier : ∀ prior : G.EventId, prior.val < start →
          prior ∈ current.application.config.cut.completed := by
        exact fun prior lower => Config.Step.path_completed_mono currentPath
          (originBoundary.earlier prior lower)
      have currentInside : InBlock start finish current.application.config :=
        ⟨earlier, fun prior later done => running
          (Or.inl (run.done_of_later relaxed later done))⟩
      obtain ⟨lower, upper⟩ := (run.shaped relaxed) current.application.config currentInside
        (fun done => running (Or.inl done)) event ready
      exact run.publications event lower upper
    rcases publication_round_clear_or_focal_default scheduler bound relaxed contract timely
        profile reference independent opens focal deviation current next currentSupport (by omega)
        currentLaw readyPublic moved with failed | ⟨_clear, advanced⟩
    · exact Or.inl failed
    · exact Or.inr (advanced.trans potential)
  have leftPoint := leftBoundary.runPoint bound turns (effectiveOpening reference) focal deviation
    relaxed run
  have rightPoint := rightBoundary.runPoint bound turns (effectiveOpening reference) focal deviation
    relaxed run
  have leftStart : good left leftDonor (horizon - left.environmentRecall.length) left :=
    ⟨leftBoundary.supported, by have := leftBoundary.bounded; omega, .refl, Or.inr leftPotential⟩
  have rightStart : good right rightDonor (horizon - right.environmentRecall.length) right :=
    ⟨rightBoundary.supported, by have := rightBoundary.bounded; omega, .refl, Or.inr rightPotential⟩
  have agreeAt : ∀ (n : Nat) (current other : app.Execution),
      good left leftDonor (n + 1) current → good right rightDonor (n + 1) other →
      current.application.config.cut = other.application.config.cut →
      ¬ stop current → ¬ stop other →
      ∀ (event : G.EventId) (owner : Player) (payload : L.Ty)
        (binding : FieldRef G.layout (.binding owner payload))
        (checks : List (GuardCheck G.layout payload))
        (outputEq : G.outputLayout event = .publication payload)
        (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
          .resolve owner payload binding checks),
      nodeView G event = .resolve owner payload binding checks outputEq codeEq →
      current.application.config.cut.Ready event →
      owner ∉ current.application.config.defaulted → owner ∉ other.application.config.defaulted →
      (owner ≠ focal → openingAccepted event current.application.config.store =
        openingAccepted event other.application.config.store) ∧
      (openingAccepted event current.application.config.store = true ∨ owner = focal →
        binding.get? current.application.config.store =
          binding.get? other.application.config.store) := by
    intro n current other currentGood otherGood cuts running otherRunning event owner payload
      binding checks outputEq codeEq node ready _active _otherActive
    obtain ⟨currentSupport, currentBound, currentPath, currentBad | currentPotential⟩ := currentGood
    · exact (running (Or.inr currentBad)).elim
    obtain ⟨otherSupport, otherBound, _otherPath, otherBad | otherPotential⟩ := otherGood
    · exact (otherRunning (Or.inr otherBad)).elim
    have currentLaw := lawOf currentPotential leftLaw
    have otherLaw := lawOf otherPotential rightLaw
    have publication : (G.outputLayout event).IsPublication := by rw [outputEq]; trivial
    have accepted := openingAccepted_of_defaultLaw independent opens current.application.config
      currentLaw event ready publication
    have otherReady : other.application.config.cut.Ready event := by rwa [← cuts]
    have otherAccepted := openingAccepted_of_defaultLaw independent opens other.application.config
      otherLaw event otherReady publication
    refine ⟨fun _ => accepted.trans otherAccepted.symm, fun _ => ?_⟩
    have currentInside : InBlock start finish current.application.config :=
      ⟨fun prior below => Config.Step.path_completed_mono currentPath
        (leftBoundary.earlier prior below), fun prior later done => running
          (Or.inl (run.done_of_later relaxed later done))⟩
    have beforeFinish : event.val < finish := ((run.shaped relaxed) current.application.config
      currentInside (fun done => running (Or.inl done)) event ready).2
    have ownerActive : owner ∉ leftDonor.defaulted := by
      rw [EventGraphRuntime.defaulted_eq_empty_of_outcomeLaw profile leftDonor leftLaw]
      simp
    have ownerActiveOther : owner ∉ rightDonor.defaulted := by
      rw [EventGraphRuntime.defaulted_eq_empty_of_outcomeLaw profile rightDonor rightLaw]
      simp
    obtain ⟨value, stored⟩ := publication_success_of_active leftReach event
      ((leftPrefix.2 event).mpr beforeFinish) owner (nodeView_resolve_actor outputEq codeEq)
      ownerActive payload outputEq
    obtain ⟨otherValue, otherStored⟩ := publication_success_of_active rightReach event
      ((rightPrefix.2 event).mpr beforeFinish) owner (nodeView_resolve_actor outputEq codeEq)
      ownerActiveOther payload outputEq
    have values : otherValue = value := by
      have fields := store_visible_of_keyView focal postViews
        (fieldVisibleTo_of_publication focal publication)
      have typed := FieldRef.get?_congr
        (⟨.inr event, outputEq⟩ : FieldRef G.layout (.publication payload))
        leftDonor.store rightDonor.store fields
      rw [stored, otherStored] at typed
      exact (PublicationResult.success.inj (Option.some.inj typed)).symm
    have storedOther : (⟨.inr event, outputEq⟩ :
        FieldRef G.layout (.publication payload)).get? rightDonor.store =
        some (.success value) := by
      simpa only [values] using otherStored
    have reachableOf (execution : app.Execution)
        (support : execution ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler players
          execution.environmentRecall.length).support)
        (bounded : execution.environmentRecall.length ≤ horizon) :
        ∃ inputs, execution.application.config.Reachable inputs := by
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
        players _ bounded _ support
      rw [serviceInitialLaw_eq_inputs setup] at trace
      obtain ⟨inputs, _, valid⟩ := reactive_history_invariant (serviceTimeouts setup deps duration)
        leaks (setup.initialLaw.map setup.eventInputs) horizon scheduler trace
      exact ⟨inputs, valid.reachable⟩
    obtain ⟨inputs, currentReach⟩ := reachableOf current currentSupport (by omega)
    obtain ⟨otherInputs, otherReach⟩ := reachableOf other otherSupport (by omega)
    exact ((currentReach.ready_publication_of_canonicalLaw_eq profile profile leftDonor
      currentPotential event ready owner payload binding checks outputEq codeEq value
      stored).1).trans
      ((otherReach.ready_publication_of_canonicalLaw_eq profile profile rightDonor otherPotential
        event otherReady owner payload binding checks outputEq codeEq value storedOther).1).symm
  have lengths : left.environmentRecall.length = right.environmentRecall.length :=
    congrArg (fun value => value.2.2.1.length) sameTraffic
  obtain ⟨leftTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    players _ leftBoundary.bounded _ leftBoundary.supported
  obtain ⟨rightTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup deps) horizon scheduler
    players _ rightBoundary.bounded _ rightBoundary.supported
  have coupled := run_stopped_traffic_congr
    relaxed.actorSerial scheduler bound turns (effectiveOpening reference) decides focal deviation
    start finish (run.shaped relaxed) run.publications stop
    (fun _ done => Or.inl done) observedStop (good left leftDonor) (good right rightDonor)
    (goodRound leftDonor leftLaw left leftBoundary)
    (goodRound rightDonor rightLaw right rightBoundary)
    (horizon - left.environmentRecall.length) 0 0 left right
    (by simpa only [Nat.zero_add] using leftTrace)
    (by rw [lengths]; simpa only [Nat.zero_add] using rightTrace)
    leftPoint.inside rightPoint.inside leftPoint.submissions rightPoint.submissions
    (runTurnFacts_roundsFrom relaxed.actorSerial scheduler bound turns (effectiveOpening reference)
      focal deviation _ _ leftBoundary.supported)
    (runTurnFacts_roundsFrom relaxed.actorSerial scheduler bound turns (effectiveOpening reference)
      focal deviation _ _ rightBoundary.supported)
    leftStart (by rw [lengths]; exact rightStart) agreeAt sameTraffic
  change (app.runUntil scheduler players stop (horizon - left.environmentRecall.length) left).map
      traffic =
    (app.runUntil scheduler players stop (horizon - right.environmentRecall.length) right).map
      traffic
  rw [← lengths]
  exact coupled

/-- The original complete public phase has an observation-local surviving traffic law.
Actual focal-default continuations are erased, using their absorbing default fact. -/
theorem publication_surviving_traffic_congr
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (left right : (serviceApplication setup deps duration leaks).Execution)
    (leftBoundary : PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start left)
    (rightBoundary : PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start right)
    (leftDonor rightDonor : (serviceGraph setup deps).Config)
    {leftInputs rightInputs : (serviceGraph setup deps).Inputs}
    (leftReach : leftDonor.Reachable leftInputs) (rightReach : rightDonor.Reachable rightInputs)
    (leftPrefix : leftDonor.cut.IsPrefix finish) (rightPrefix : rightDonor.cut.IsPrefix finish)
    (leftLaw : outcomeLaw profile Config.defaulted leftDonor = PMF.pure ∅)
    (rightLaw : outcomeLaw profile Config.defaulted rightDonor = PMF.pure ∅)
    (leftPotential : canonicalLaw profile left.application.config = canonicalLaw profile leftDonor)
    (rightPotential : canonicalLaw profile right.application.config =
      canonicalLaw profile rightDonor)
    (postViews : keyView focal (runKey leftDonor) = keyView focal (runKey rightDonor))
    (sameTraffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right) :
    ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon left).map
      (fun final => if focal ∈ final.application.config.defaulted then none else
        some ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) =
    ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon right).map
      (fun final => if focal ∈ final.application.config.defaulted then none else
        some ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final)) := by
  classical
  let G := serviceGraph setup deps
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
  let Traffic := MessageNetwork Player app.Payload × List (MessageId Player × Bool) ×
    List app.EnvironmentEntry × List app.PlayerEntry × PlayerView G × PublicView G
  let erase := fun extra : Traffic =>
    if focal ∈ extra.2.2.2.2.1.observation.defaulted then none else some extra
  let read := fun final : app.Execution =>
    if focal ∈ final.application.config.defaulted then none else some (traffic final)
  have absorb (current : app.Execution) (failed : focal ∈ current.application.config.defaulted)
      (next : app.Execution) (moved : next ∈ (app.round scheduler players current).support) :
      focal ∈ next.application.config.defaulted :=
    Config.Step.path_defaulted_mono
      (reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler players
        current next moved) failed
  have erased := congrArg (PMF.map erase)
    (publication_first_failure_traffic_congr scheduler bound relaxed contract timely profile
        reference
      independent opens focal deviation run left right leftBoundary rightBoundary leftDonor
      rightDonor leftReach rightReach leftPrefix rightPrefix leftLaw rightLaw leftPotential
      rightPotential postViews sameTraffic)
  simp only [PMF.map_comp, Function.comp_def] at erased
  have stopped (origin : app.Execution) :=
    ReactiveApplication.runUntil_map_stop_or_absorbing scheduler players
      (fun current : app.Execution => BlockDone finish current.application.config)
      (fun current => focal ∈ current.application.config.defaulted) read absorb
      (fun current failed => by simp only [read, ite_eq_left failed])
      (horizon - origin.environmentRecall.length) origin
  exact (stopped left).trans (erased.trans (stopped right).symm)

/-- At a surviving complete public boundary the physical event table equals
its ordinary-open source donor. Chronological native order is not identified. -/
theorem publication_surviving_endpoint_key
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    (boundary : PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start origin)
    (donor : (serviceGraph setup deps).Config) (ordered : donor.cut.IsPrefix finish)
    (law : outcomeLaw profile Config.defaulted donor = PMF.pure ∅)
    (potential : canonicalLaw profile origin.application.config = canonicalLaw profile donor)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon origin).support)
    (survived : focal ∉ final.application.config.defaulted) :
    final.application.config.defaulted = ∅ ∧
      runKey final.application.config = runKey donor := by
  let G := serviceGraph setup deps
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  have originLaw : outcomeLaw profile Config.defaulted origin.application.config = PMF.pure ∅ :=
    (outcomeLaw_eq_of_canonicalLaw_eq Config.defaulted
      (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
      potential).trans law
  have originClear := EventGraphRuntime.defaulted_eq_empty_of_outcomeLaw profile _ originLaw
  have within : origin.application.config.cut.Within start finish := by
    refine ⟨boundary.earlier, fun event done => ?_⟩
    by_contra late
    obtain ⟨_, _, owner, _owned, inactive⟩ := boundary.later event
      (by have := run.nonempty; omega) done
    rw [originClear] at inactive
    simp at inactive
  have inside : InBlock start finish origin.application.config :=
    ⟨within.1, fun event late done => (Nat.not_lt.mpr late) (within.2 event done)⟩
  obtain ⟨done, failed | ⟨clear, same⟩⟩ := publication_run_survives scheduler bound relaxed
    contract timely profile
        reference independent opens focal deviation run origin boundary.supported
    boundary.bounded inside originLaw final reached
  · exact (survived failed).elim
  refine ⟨clear, Config.runKey_eq_of_canonicalLaw_eq profile profile
    final.application.config donor ?_ (same.trans potential)⟩
  have finalWithin := blockRun_within_of_clear (serviceTimeouts setup deps duration) leaks
    scheduler players (run.shaped relaxed)
    (horizon - origin.environmentRecall.length) origin final within reached clear
  exact EventOrder.Cut.ext (Finset.ext fun event =>
    ((finalWithin.isPrefix run.bounded done).2 event).trans (ordered.2 event).symm)

/-- A full ordinary-open source successor has an exact observation-local
channel of surviving native traffic. The hidden successor is retained jointly;
failure fibers may have zero survival probability. -/
theorem publication_surviving_joint
    {Seed Source View Next NextView : Type} {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (advance : Source → Next) (nextView : Next → NextView)
    (donor : Next → (serviceGraph setup deps).Config)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (noise : View → PMF (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)))
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun current =>
        (noise (observe current)).map fun extra => (current, extra))
    (boundary : ∀ seed ∈ prior.support, PhaseBoundary scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start (execution seed))
    (reachable : ∀ seed ∈ prior.support,
      ∃ inputs, (donor (advance (source seed))).Reachable inputs)
    (ordered : ∀ seed ∈ prior.support, (donor (advance (source seed))).cut.IsPrefix finish)
    (defaultLaw : ∀ seed ∈ prior.support,
      outcomeLaw profile Config.defaulted (donor (advance (source seed))) = PMF.pure ∅)
    (potential : ∀ seed ∈ prior.support,
      canonicalLaw profile (execution seed).application.config =
        canonicalLaw profile (donor (advance (source seed))))
    (reflects : ∀ left ∈ (prior.map source).support, ∀ right ∈ (prior.map source).support,
      nextView (advance left) = nextView (advance right) → observe left = observe right)
    (visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      nextView (advance (source left)) = nextView (advance (source right)) →
      keyView focal (runKey (donor (advance (source left)))) =
        keyView focal (runKey (donor (advance (source right))))) :
    ∃ nextNoise : NextView → PMF (Option (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps))),
      (prior.bind fun seed =>
        ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
            (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
          (fun current => BlockDone finish current.application.config) horizon (execution seed)).map
            fun final => (advance (source seed),
              if focal ∈ final.application.config.defaulted then none else
                some ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal final))) =
        ((prior.map source).map advance).bind fun next =>
          (nextNoise (nextView next)).map fun extra => (next, extra) := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
  let phase := fun seed => (app.runUntilHorizon scheduler players
    (fun current => BlockDone finish current.application.config) horizon (execution seed)).map
      fun final => if focal ∈ final.application.config.defaulted then none else some (traffic final)
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => traffic (execution seed)) observe noise factor (fun _ => PMF.pure ())
    (fun current _ => advance current) nextView (fun seed _ => phase seed)
    (fun left leftMember _ _ right rightMember _ _ same =>
      reflects left leftMember right rightMember same) (by
      intro left leftMember _ _ right rightMember _ _ same sameTraffic
      obtain ⟨leftInputs, leftReach⟩ := reachable left leftMember
      obtain ⟨rightInputs, rightReach⟩ := reachable right rightMember
      exact publication_surviving_traffic_congr scheduler bound relaxed contract timely profile
        reference
        independent opens focal deviation run (execution left) (execution right)
        (boundary left leftMember) (boundary right rightMember)
        (donor (advance (source left))) (donor (advance (source right))) leftReach rightReach
        (ordered left leftMember) (ordered right rightMember)
        (defaultLaw left leftMember) (defaultLaw right rightMember)
        (potential left leftMember) (potential right rightMember)
        (visible left leftMember right rightMember same) sameTraffic)
  refine ⟨nextNoise, ?_⟩
  simp only [PMF.pure_bind, PMF.pure_map] at law
  have mapped : (prior.map source).bind (fun current => PMF.pure (advance current)) =
      (prior.map source).map advance := PMF.bind_pure_comp advance (prior.map source)
  rw [mapped, PMF.map_comp] at law
  simpa only [phase, PMF.map_comp, Function.comp_def] using law

end Vegas
