/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedSupport
import Vegas.Game.SourceServiceCompiledExecution
import Interaction.ReactiveRecallEntries
import GameTheory.Protocol.TremblingPlans
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Legal shared timing at full-source decisions

At every unsent binding visit, earlier scheduled binding slots have zero
posterior probability: each would have submitted at its recorded legal input.
At the final visit only the current slot remains.
This uses actual own recall and original source-policy admission, rather than
requiring a normalized policy to be fully mixed in the original source game.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

private theorem posterior_previous {Player Index : Type}
    (app : ReactiveApplication Player) (timing : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (index : Index)
    (supported : index ∈ ((app.policyMixture timing family).posterior (past ++ [entry])).support) :
    index ∈ ((app.policyMixture timing family).posterior past).support := by
  rw [ReactiveApplication.Implementation.posterior_snoc] at supported
  obtain ⟨pair, conditional, same⟩ := PMF.support_map .. ▸ supported
  have original : pair ∈ (((app.policyMixture timing family).posterior past).bind fun value =>
      (family value past entry.beforeView).map fun response => (response, value)).support := by
    unfold fiberPosterior at conditional
    split at conditional
    · exact ((PMF.mem_support_filter_iff _).mp conditional).2
    · exact conditional
  obtain ⟨value, member, generated⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ original)
  obtain ⟨response, _, equal⟩ := PMF.support_map .. ▸ generated
  have valueEq : value = index := (congrArg Prod.snd equal).trans same
  exact valueEq ▸ member

private theorem posterior_prefix {Player Index : Type}
    (app : ReactiveApplication Player) (timing : PMF Index) (family : Index → app.Policy)
    (past suffix : List app.PlayerEntry) (index : Index)
    (supported : index ∈ ((app.policyMixture timing family).posterior (past ++ suffix)).support) :
    index ∈ ((app.policyMixture timing family).posterior past).support := by
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using supported
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc] at supported
      exact ih (posterior_previous app timing family (past ++ suffix) entry index supported)

private theorem posterior_action {Player Index : Type}
    (app : ReactiveApplication Player) (timing : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (index : Index)
    (possible : entry.action ∈ ((app.policyMixture timing family).policy
      past entry.beforeView).support)
    (supported : index ∈ ((app.policyMixture timing family).posterior (past ++ [entry])).support) :
    entry.action ∈ (family index past entry.beforeView).support := by
  let joint := ((app.policyMixture timing family).posterior past).bind fun value =>
    (family value past entry.beforeView).map fun response => (response, value)
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {entry.action}, pair ∈ joint.support := by
    rw [app.policyMixture_policy] at possible
    obtain ⟨value, prior, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ possible)
    refine ⟨(entry.action, value), rfl, ?_⟩
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨value, prior,
      PMF.support_map .. ▸ ⟨entry.action, produced, rfl⟩⟩
  rw [ReactiveApplication.Implementation.posterior_snoc] at supported
  change index ∈ ((fiberPosterior joint Prod.fst entry.action).map Prod.snd).support at supported
  rw [fiberPosterior_eq_filter_preimage _ _ meets] at supported
  obtain ⟨pair, conditional, same⟩ := PMF.support_map .. ▸ supported
  obtain ⟨observed, original⟩ := (PMF.mem_support_filter_iff _).mp conditional
  obtain ⟨value, _, generated⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ original)
  obtain ⟨response, produced, equal⟩ := PMF.support_map .. ▸ generated
  have valueEq : value = index := (congrArg Prod.snd equal).trans same
  have responseEq : response = entry.action := (congrArg Prod.fst equal).trans observed
  simpa only [valueEq, responseEq] using produced

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem recalled_binding_not_selected
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (payload : L.Ty) (binding : (graph setup).outputLayout event = .binding who payload)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (earlier : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (later : List (application setup leaks).PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ entry :: later)
    (granted : entry.beforeView.application.publicView.serviceGrant = some event)
    (selected : entry.action ∈ (sourceServiceOpportunity setup leaks profile who event
      earlier entry.beforeView).support) : False := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let horizon := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  let model := menu.information (initialLaw setup) horizon scheduler
  let history : (menu.protocol (initialLaw setup) horizon scheduler).History := ⟨_, trace⟩
  have observed : model.infoOf who trace =
      some (control.execution.recall who, control.execution.observe app who) := by
    change (menu.signals (initialLaw setup) horizon scheduler).infoOf who trace = _
    rw [menu.info]
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
    rfl
  have member : (some (earlier, entry.beforeView), entry.action) ∈ model.ownPlay who trace := by
    rw [menu.ownPlay_of_info_some (initialLaw setup) horizon scheduler who history _ _ observed,
      recalled]
    unfold ReactiveApplication.recallOwnPlay
    rw [app.ownPlayFrom_concat]
    apply List.mem_append_left
    simp only [List.nil_append, ReactiveApplication.ownPlayFrom, List.mem_append,
      List.mem_singleton]
    exact Or.inr trivial
  obtain ⟨site, siteEq, _⟩ := model.exists_informationSite_of_mem_ownPlay trace member
  obtain ⟨witness, _, _⟩ := site.2
  have acts := InformationModel.InformationSite.active model site witness
  cases current : witness.1.state with
  | none => rw [current] at acts; cases acts
  | some previous =>
      have acting : previous.actor = some who := by rw [current] at acts; exact acts
      have traced : (menu.protocol (initialLaw setup) horizon scheduler).Trace (some previous) :=
        current ▸ witness.1.trace
      have info := (menu.info (initialLaw setup) horizon scheduler who witness.1.trace).symm.trans
        (witness.2.trans siteEq)
      rw [current] at info
      change (if previous.actor = some who then
        some (previous.execution.recall who, previous.execution.observe app who)
        else none) = some (earlier, entry.beforeView) at info
      rw [ite_eq_left acting] at info
      have pastEq := congrArg Prod.fst (Option.some.inj info)
      have viewEq := congrArg Prod.snd (Option.some.inj info)
      dsimp only at pastEq viewEq
      have previousUnsent : (runtime setup).eventRecorded leaks
          (previous.execution.recall who) event = false := by
        rw [pastEq]
        rw [recalled, (runtime setup).eventRecorded_append] at unsent
        exact Bool.or_eq_false_iff.mp unsent |>.1
      have response := sourceServiceOpportunity_at_history setup leaks bounds values initialValues
        capacity rosters opportunities network profile permitted who previous traced acting event
        (by
          change (previous.execution.observe app who).application.publicView.serviceGrant = _
          rw [viewEq]
          exact granted) owned previousUnsent entry.action
        (by
          change entry.action ∈ (sourceServiceOpportunity setup leaks profile who event
            (previous.execution.recall who) (previous.execution.observe app who)).support
          rw [pastEq, viewEq]
          exact selected)
      have recorded := (runtime setup).eventRecorded_iff leaks (control.execution.recall who) event
      have contradiction := recorded.mpr ⟨entry, by rw [recalled]; simp, response.2 payload binding⟩
      rw [unsent] at contradiction
      cases contradiction

/-- At an actual unsent binding decision, every timing slot in the posterior
is current or future. An earlier slot would have submitted a binding, which
would still be recorded in the player's own recall. -/
theorem sourceServiceTimedMixture_binding_future
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (payload : L.Ty) (binding : (graph setup).outputLayout event = .binding who payload)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (timing : PMF (Fin ((rosters event).count who)))
    (witness : Fin ((rosters event).count who)) (positive : witness ∈ timing.support)
    (future : (control.execution.recall who).length ≤
      rosterOffset setup rosters who event + witness.val) :
    ∀ selected ∈ (((application setup leaks).policyMixture timing
      (sourceServiceTimedFamily setup leaks rosters profile who event)).posterior
        (control.execution.recall who)).support,
      (control.execution.recall who).length ≤
        rosterOffset setup rosters who event + selected.val := by
  let app := application setup leaks
  let family := sourceServiceTimedFamily setup leaks rosters profile who event
  let offset := rosterOffset setup rosters who event
  have witnessSupported := sourceServiceTimedPolicy_future_supported setup leaks bounds values
    capacity rosters opportunities network profile who control trace active event granted owned
      unsent timing witness positive future
  obtain ⟨past, suffix, recalled, count, legal⟩ := sourceService_unsubmitted_recall setup leaks
    bounds values capacity rosters opportunities network who control trace active
      event granted owned unsent
  intro selected selectedSupported
  by_contra notFuture
  have passed : offset + selected.val < (control.execution.recall who).length :=
    Nat.lt_of_not_ge notFuture
  have inside : selected.val < suffix.length := by
    have lengths := congrArg List.length recalled
    simp only [List.length_append, count] at lengths
    dsimp only [offset] at passed
    omega
  let before := suffix.take selected.val
  let entry := suffix[selected.val]
  let after := suffix.drop (selected.val + 1)
  have split : suffix = before ++ entry :: after := by
    have actual := List.take_append_drop selected.val suffix
    rw [List.drop_eq_getElem_cons inside] at actual
    exact actual.symm
  have pastLength : (past ++ before).length = offset + selected.val := by
    simp only [List.length_append, count, before, List.length_take,
      Nat.min_eq_left inside.le, offset]
  have afterSelected : selected ∈ ((app.policyMixture timing family).posterior
      ((past ++ before) ++ [entry])).support := by
    apply posterior_prefix app timing family _ after selected
    simpa only [recalled, split, List.append_assoc, List.singleton_append] using selectedSupported
  have beforeWitness : witness ∈ ((app.policyMixture timing family).posterior
      (past ++ before)).support := by
    apply posterior_prefix app timing family _ (entry :: after) witness
    simpa only [recalled, split, List.append_assoc] using witnessSupported
  have waiting : family witness (past ++ before) entry.beforeView =
      app.replayPolicy (past ++ before) entry.beforeView := by
    have unused : some (offset + witness.val) ≠ some (past ++ before).length := by
      rw [pastLength]
      intro equal
      have equal := Option.some.inj equal
      change (control.execution.recall who).length ≤ offset + witness.val at future
      omega
    exact ite_eq_right unused
  have possible : entry.action ∈ ((app.policyMixture timing family).policy
      (past ++ before) entry.beforeView).support := by
    apply app.policyMixture_action_support timing family _ _ witness _ beforeWitness
    rw [waiting]
    exact (legal before entry after split).1
  have selectedAction := posterior_action app timing family (past ++ before) entry selected
    possible afterSelected
  have opportunity : entry.action ∈ (sourceServiceOpportunity setup leaks profile who event
      (past ++ before) entry.beforeView).support := by
    simpa only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
      Option.map_some, pastLength, offset, ↓reduceIte] using selectedAction
  exact recalled_binding_not_selected setup leaks bounds values initialValues capacity rosters
    opportunities network profile permitted who control trace active event owned payload binding
    unsent (past ++ before) entry after (by rw [recalled, split, List.append_assoc])
    (legal before entry after split).2 opportunity

/-- At the actual final unsent binding opportunity, conditioning the shared
timing lottery leaves only the current slot. The complete physical response
law is exactly the existing source opportunity law. -/
theorem sourceServiceTimedMixture_binding_last
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (payload : L.Ty) (binding : (graph setup).outputLayout event = .binding who payload)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (timing : PMF (Fin ((rosters event).count who))) (full : FullSupport timing)
    (last : (control.execution.recall who).length + 1 =
      rosterOffset setup rosters who event + (rosters event).count who) :
    ((application setup leaks).policyMixture timing
      (sourceServiceTimedFamily setup leaks rosters profile who event)).policy
        (control.execution.recall who) (control.execution.observe (application setup leaks) who) =
      sourceServiceOpportunity setup leaks profile who event (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
  let app := application setup leaks
  let family := sourceServiceTimedFamily setup leaks rosters profile who event
  let offset := rosterOffset setup rosters who event
  have positive : 0 < (rosters event).count who :=
    List.count_pos_iff.mpr (opportunities event who payload binding)
  let current : Fin ((rosters event).count who) :=
    ⟨(rosters event).count who - 1, by omega⟩
  have currentTime : offset + current.val = (control.execution.recall who).length := by
    dsimp only [offset, current]
    omega
  have future := sourceServiceTimedMixture_binding_future setup leaks bounds values initialValues
    capacity rosters opportunities network profile permitted who control trace active event granted
      owned payload binding unsent timing current (full current) currentTime.ge
  have selectedNow : ∀ selected ∈ ((app.policyMixture timing family).posterior
      (control.execution.recall who)).support,
      offset + selected.val = (control.execution.recall who).length := by
    intro selected supported
    have lower := future selected supported
    have upper := selected.isLt
    dsimp only [offset] at currentTime ⊢
    omega
  rw [app.policyMixture_policy]
  trans ((app.policyMixture timing family).posterior (control.execution.recall who)).bind
    (fun _ => sourceServiceOpportunity setup leaks profile who event (control.execution.recall who)
      (control.execution.observe app who))
  · apply bind_congr_on_support _
    intro selected supported
    have chosen := selectedNow selected supported
    simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
      Option.map_some, chosen, offset, ↓reduceIte]
    rfl
  · exact PMF.bind_const _ _

/-- Shared positive timing is legal at every retained history. The final
binding visit is forced by its actual posterior, including histories that
have zero probability under the limiting final-slot policy. -/
theorem sourceServiceTimedPolicy_admissible
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, FullSupport (timing event who owned))
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) :
    (sourceServiceMenu setup leaks bounds rosters).Admissible (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing profile who) := by
  classical
  intro control trace active response supported
  let app := application setup leaks
  let past := control.execution.recall who
  let view := control.execution.observe app who
  have replay_covered (replay : response ∈ (app.replayPolicy past view).support)
      (optional : ¬ bindingRequired setup leaks rosters who past view) :
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
    change response ∈ sourceServiceActions setup leaks bounds rosters who past view
    rw [sourceServiceActions, ite_eq_right optional]
    exact bounds.replay_compiled (runtime setup) leaks who past view response replay
  change response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile who
    past view).support at supported
  cases grant : view.application.publicView.serviceGrant with
  | none =>
      simp only [sourceServiceTimedPolicy, grant] at supported
      exact replay_covered supported (by rintro ⟨event, _, same, _⟩; simp [grant] at same)
  | some event =>
      by_cases owned : (graph setup).actor? event = some who
      · by_cases recorded : (runtime setup).eventRecorded leaks past event = true
        · rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile who past view
            event grant recorded] at supported
          apply replay_covered supported
          rintro ⟨other, _, otherGrant, _, _, _, unsent, _⟩
          have same : other = event := Option.some.inj (otherGrant.symm.trans grant)
          subst other
          simp only [recorded, Bool.true_eq_false] at unsent
        · have unsent : (runtime setup).eventRecorded leaks past event = false :=
            Bool.eq_false_iff.mpr recorded
          simp only [sourceServiceTimedPolicy, grant, dite_eq_left owned] at supported
          by_cases required : bindingRequired setup leaks rosters who past view
          · obtain ⟨other, payload, otherGrant, binding, _, _, _, last⟩ := required
            have same : other = event := Option.some.inj (otherGrant.symm.trans grant)
            subst other
            have physical := sourceServiceTimedMixture_binding_last setup leaks bounds values
              initialValues capacity rosters opportunities network profile permitted who control
              trace active event grant owned payload binding unsent (timing event who owned)
              (full event who owned) last
            change response ∈ (((app.policyMixture (timing event who owned)
              (sourceServiceTimedFamily setup leaks rosters profile who event)).policy
                (control.execution.recall who) (control.execution.observe app who))).support
              at supported
            rw [physical] at supported
            exact (sourceServiceOpportunity_at_history setup leaks bounds values initialValues
              capacity rosters opportunities network profile permitted who control trace active
                event grant owned unsent response supported).1
          · rw [app.policyMixture_policy] at supported
            obtain ⟨slot, _, produced⟩ := Set.mem_iUnion₂.mp
              (PMF.support_bind .. ▸ supported)
            change response ∈ (app.scheduledPolicy (rosterOffset setup rosters who event)
              (some slot) (sourceServiceOpportunity setup leaks profile who event)
                app.replayPolicy past view).support at produced
            unfold ReactiveApplication.scheduledPolicy at produced
            split at produced
            · exact (sourceServiceOpportunity_at_history setup leaks bounds values initialValues
                capacity rosters opportunities network profile permitted who control trace active
                  event grant owned unsent response produced).1
            · exact replay_covered produced required
      · simp only [sourceServiceTimedPolicy, grant, dite_eq_right owned] at supported
        apply replay_covered supported
        rintro ⟨other, _, otherGrant, _, actor, _⟩
        have same : other = event := Option.some.inj (otherGrant.symm.trans grant)
        subst other
        exact owned actor

/-- Finite native strategies for shared positive timing. The source policy is
normalized with its original private-intention posterior, then represented in
the existing retained response menu. -/
def sourceServiceTimedProfile
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (original : BehavioralProfile setup.program) :
    GameTheory.Profile ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).behavioralSignature := fun who =>
  (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
    (sourceServiceTimedPolicy setup leaks rosters timing
      (normalizeDisclosureProfile setup.program []
        (Revelations.initial setup.context) original) who)

end Vegas
