/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveBindingLikelihood
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Source.ObservationRecall
import GameTheory.Math.Probability.ConditionalObservation

/-! # Conditional traffic after an actual resolution decision

An effective source disclosure emits either an evidence-free withholding
decision or the certified opening recovered from the actual binding table.
The joint source-successor and full focal traffic law factors through the
source successor view. This is the physical response step; no scheduler,
roster, inclusion law, posterior or equilibrium comparison is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem inert_submission_traffic_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (left right : (application setup leaks).Execution) (owner focal : Player)
    (material : WitnessedSubmission (graph setup))
    (leftInert : (application setup leaks).submit left.application owner material =
      left.application)
    (rightInert : (application setup leaks).submit right.application owner material =
      right.application)
    (emitted : (application setup leaks).packet left.application owner (left.network.known owner)
        material =
      (application setup leaks).packet right.application owner (right.network.known owner) material)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    (runtime setup).bindingTraffic leaks focal
        (left.respond (application setup leaks) owner ⟨some material⟩) =
      (runtime setup).bindingTraffic leaks focal
        (right.respond (application setup leaks) owner ⟨some material⟩) := by
  let app := application setup leaks
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun traffic => traffic.2.1) same
  have environments := congrArg (fun traffic => traffic.2.2.1) same
  have recalled := congrArg (fun traffic => traffic.2.2.2.1) same
  have views := congrArg (fun traffic => traffic.2.2.2.2.1) same
  have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments recalled views publics
  have observed : left.observe app focal = right.observe app focal := by
    have projected := congrArg (fun view : PlayerView (graph setup) =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView (graph setup))) views
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [networks]
    exact congrArg₂ (fun view evidence =>
      (⟨right.network.observe focal, view, evidence⟩ : app.PlayerView)) projected receipts
  have recallEq := app.respond_focal_recall_eq left right owner focal ⟨some material⟩
    networks observed recalled (by
      intro submission transmitted
      cases Option.some.inj transmitted
      simpa only [app, leftInert, rightInert] using emitted)
  have leftApplication : (left.respond app owner ⟨some material⟩).application =
      left.application := leftInert
  have rightApplication : (right.respond app owner ⟨some material⟩).application =
      right.application := rightInert
  unfold bindingTraffic
  rw [leftApplication, rightApplication, recallEq]
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext rfl (Prod.ext views publics))))
  change (left.network.submit owner (app.packet (app.submit left.application owner material) owner
    (left.network.known owner) material)).2 =
      (right.network.submit owner (app.packet (app.submit right.application owner material) owner
        (right.network.known owner) material)).2
  dsimp only [app]
  rw [leftInert, rightInert, emitted, networks]

private theorem normalized_opening_traffic_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (left right : (application setup leaks).Execution) (owner focal : Player)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftValid : left.application.candidates.lookup candidate = .openable raw)
    (rightValid : right.application.candidates.lookup candidate = .openable raw)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    let app := application setup leaks
    (runtime setup).bindingTraffic leaks focal (left.respond app owner
        ⟨some ((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
          (app.observePlayer left.application owner) (left.network.known owner))⟩) =
      (runtime setup).bindingTraffic leaks focal (right.respond app owner
        ⟨some ((disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
          (app.observePlayer right.application owner) (right.network.known owner))⟩) := by
  intro app
  let call : WitnessedSubmission (graph setup) :=
    disclosureSubmission (.opening event candidate raw)
  let material := call.normalizeReactive owner (app.observePlayer left.application owner)
    (left.network.known owner)
  have networks := congrArg Prod.fst same
  have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks publics
  have leftLocal : left.application.candidates.lookup (owner, candidate.2) = .openable raw := by
    simpa only [← owned, Prod.mk.eta] using leftValid
  have rightLocal : right.application.candidates.lookup (owner, candidate.2) = .openable raw := by
    simpa only [← owned, Prod.mk.eta] using rightValid
  have normalEq : material = call.normalizeReactive owner
      (app.observePlayer right.application owner) (right.network.known owner) := by
    simp only [material, call, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none, Submission.candidateAfter_opening,
      EvidenceRequest.normalize]
    change (⟨⟨.opening event candidate raw, none⟩,
      EvidenceRequest.canonical (left.network.known owner)
        ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
          (fun slot => left.application.candidates.lookup (owner, slot))
          (left.network.known owner))⟩ : WitnessedSubmission (graph setup)) = _
    change _ = (⟨⟨.opening event candidate raw, none⟩,
      EvidenceRequest.canonical (right.network.known owner)
        ((EvidenceRequest.owned ⟨candidate, raw⟩).resolve owner
          (fun slot => right.application.candidates.lookup (owner, slot))
          (right.network.known owner))⟩ : WitnessedSubmission (graph setup))
    simp only [EvidenceRequest.resolve, owned, leftLocal, rightLocal, and_self,
      ↓reduceIte, networks]
  have callEq : material.call = ⟨.opening event candidate raw, none⟩ := by
    simp only [material, call, disclosureSubmission, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none]
  have inert (execution : app.Execution) : app.submit execution.application owner material =
      execution.application := by
    change submitStep (material.call.register execution.application owner) owner
      material.call.packet = _
    rw [callEq]
    rfl
  have emitted : app.packet left.application owner (left.network.known owner) material =
      app.packet right.application owner (right.network.known owner) material := by
    have first := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
      left.application owner (left.network.known owner) call
    have second := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
      right.application owner (right.network.known owner) call
    change material.emit left.application owner (left.network.known owner) =
      call.emit left.application owner (left.network.known owner) at first
    change (call.normalizeReactive owner (app.observePlayer right.application owner)
      (right.network.known owner)).emit right.application owner (right.network.known owner) =
      call.emit right.application owner (right.network.known owner) at second
    change material.emit left.application owner (left.network.known owner) =
      material.emit right.application owner (right.network.known owner)
    rw [first, normalEq, second]
    have firstVerified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr leftValid
    have secondVerified := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr rightValid
    simp only [call, disclosureSubmission, WitnessedSubmission.emit, owned,
      firstVerified, secondVerified, and_self, ↓reduceIte, publics]
  change (runtime setup).bindingTraffic leaks focal (left.respond app owner ⟨some material⟩) = _
  rw [← normalEq]
  exact inert_submission_traffic_congr setup leaks left right owner focal material
    (inert left) (inert right) emitted same

/-- Equal effective source successor views give the same actual canonical
resolution response traffic. The original source choice need not be identified
from the packet; only the emitted effective decision is used in this law. -/
theorem source_resolution_decision_traffic_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (leftSource rightSource : Config Player L Γ)
    (left right : (application setup leaks).Execution)
    (leftAgrees : refs.Agrees leftSource.state left.application.config.store)
    (rightAgrees : refs.Agrees rightSource.state right.application.config.store)
    (leftBinding : left.application.BindingInvariant)
    (rightBinding : right.application.BindingInvariant)
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (event : (graph setup).EventId) (focal : Player)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (leftCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs leftSource.registry
          leftSource.revelations binding))
    (rightCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs rightSource.registry
          rightSource.revelations binding))
    (leftNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs leftSource.registry leftSource.revelations
        binding) outputEq leftCode)
    (rightNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs rightSource.registry rightSource.revelations
        binding) outputEq rightCode)
    (first second : Bool)
    (leftEffective : first = false ∨ ∃ value : L.Val payload,
      first = true ∧ disclosureResult published binding leftSource true = .success value)
    (rightEffective : second = false ∨ ∃ value : L.Val payload,
      second = true ∧ disclosureResult published binding rightSource true = .success value)
    (same : (revealSuccessor published binding leftSource first).view focal =
      (revealSuccessor published binding rightSource second).view focal)
    (traffic : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    (runtime setup).bindingTraffic leaks focal
        (left.respond (application setup leaks) owner
          ((runtime setup).canonicalServiceDecision leaks owner (left.recall owner)
            (left.observe (application setup leaks) owner) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) first))) =
      (runtime setup).bindingTraffic leaks focal
        (right.respond (application setup leaks) owner
          ((runtime setup).canonicalServiceDecision leaks owner (right.recall owner)
            (right.observe (application setup leaks) owner) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) second))) := by
  have result := congrArg
    (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
      view.1.cells.get .here) same
  change disclosureResult published binding leftSource first =
    disclosureResult published binding rightSource second at result
  rcases leftEffective with rfl | ⟨value, rfl, firstSuccess⟩
  · rcases rightEffective with rfl |
      ⟨value, rfl, secondSuccess⟩
    · rw [(runtime setup).canonicalServiceDecision_resolution_false leaks owner _ _ event
        owner payload (refs.get binding) _ outputEq leftCode leftNode,
        (runtime setup).canonicalServiceDecision_resolution_false leaks owner _ _ event
        owner payload (refs.get binding) _ outputEq rightCode rightNode]
      apply inert_submission_traffic_congr setup leaks left right
        owner focal (disclosureSubmission (.withhold event)) rfl rfl _ traffic
      have publics := congrArg (fun read => read.2.2.2.2.2) traffic
      dsimp only [bindingTraffic] at publics
      change (disclosureSubmission (.withhold event)).emit left.application
        owner (left.network.known owner) =
          (disclosureSubmission (.withhold event)).emit right.application
            owner (right.network.known owner)
      simp only [disclosureSubmission, WitnessedSubmission.emit, publics]
    · rw [secondSuccess, disclosureResult_false] at result
      cases result
  · rcases rightEffective with rfl |
      ⟨other, rfl, secondSuccess⟩
    · rw [firstSuccess, disclosureResult_false] at result
      cases result
    · rw [firstSuccess, secondSuccess] at result
      cases PublicationResult.success.inj result
      obtain ⟨candidate, firstAssociated, owned, firstValid, _firstOpening⟩ :=
        guarded_rosterOpening_success setup leaks published binding leftSource refs
          left leftAgrees leftBinding event
          outputEq leftCode leftNode value firstSuccess
      obtain ⟨other, secondAssociated, _owned, secondValid, _secondOpening⟩ :=
        guarded_rosterOpening_success setup leaks published binding rightSource refs
          right rightAgrees rightBinding event
          outputEq rightCode rightNode value secondSuccess
      have publics := congrArg (fun read => read.2.2.2.2.2) traffic
      have accepted := congrArg EventGraphRuntime.PublicView.accepted publics
      have candidateEq : candidate = other := Option.some.inj
        (firstAssociated.symm.trans
          ((congrFun accepted (refs.get binding).field).trans secondAssociated))
      subst other
      have leftNotBind who payload output code
          (impossible : nodeView (graph setup) event =
            .bind who payload output code) : False := by
        rw [leftNode] at impossible
        cases impossible
      have rightNotBind who payload output code
          (impossible : nodeView (graph setup) event =
            .bind who payload output code) : False := by
        rw [rightNode] at impossible
        cases impossible
      rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
          leftNotBind,
        (runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
          rightNotBind]
      have firstResolved := compiled_disclosure_result published binding leftSource refs
        left.application.config.store leftAgrees true
      have secondResolved := compiled_disclosure_result published binding rightSource refs
        right.application.config.store rightAgrees true
      rw [firstSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at firstResolved
      rw [secondSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at secondResolved
      rw [(runtime setup).serviceDecision_successful_opening leaks left
          leftRecall owner event payload (refs.get binding) _ outputEq
          leftCode leftNode candidate value firstAssociated owned firstValid
          firstResolved,
        (runtime setup).serviceDecision_successful_opening leaks right
          rightRecall owner event payload (refs.get binding) _ outputEq
          rightCode rightNode candidate value secondAssociated owned secondValid
          secondResolved]
      exact normalized_opening_traffic_congr setup leaks
        left right owner focal event candidate ⟨payload, value⟩
          owned firstValid secondValid traffic

/-- The actual effective resolution response preserves the joint source and
traffic law through its source successor. The preceding factorization is an
induction hypothesis; equality of the successor traffic channel is proved from
the real binding catalogue and canonical packet normalization. -/
theorem source_async_resolution_decision_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (focal : Player)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (valid : ∀ seed ∈ prior.support, (execution seed).application.BindingInvariant)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (codeEq : ∀ seed, cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding))
    (node : ∀ seed, nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs (source seed).registry
        (source seed).revelations binding) outputEq (codeEq seed))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra))
    (choice : Config Player L Γ → PMF Bool)
    (effective : ∀ seed ∈ prior.support, ∀ disclose ∈ (choice (source seed)).support,
      disclose = false ∨ ∃ value : L.Val payload,
        disclose = true ∧ disclosureResult published binding (source seed) true = .success value) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (source seed)).map fun disclose =>
        (revealSuccessor published binding (source seed) disclose,
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
                ((execution seed).observe (application setup leaks) owner) event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose))))) =
      ((prior.map source).bind fun config =>
        (choice config).map (revealSuccessor published binding config)).bind fun config =>
          (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  have updated := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun config => config.view focal) noise factor choice
    (revealSuccessor published binding) (fun config => config.view focal)
    (fun seed disclose => PMF.pure ((runtime setup).bindingTraffic leaks focal
      ((execution seed).respond (application setup leaks) owner
        ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
          ((execution seed).observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)))))
    (by
      intro left _ first _ right _ second _ same
      exact reveal_view_reflects focal published binding left right first second same)
    (by
      intro left leftSupport first firstSupport right rightSupport second secondSupport same traffic
      apply congrArg PMF.pure
      exact source_resolution_decision_traffic_congr setup leaks published binding refs
        (source left) (source right) (execution left) (execution right)
        (agree left leftSupport) (agree right rightSupport) (valid left leftSupport)
        (valid right rightSupport) (recalled left leftSupport) (recalled right rightSupport)
        event focal outputEq (codeEq left) (codeEq right) (node left) (node right) first second
        (effective left leftSupport first firstSupport)
        (effective right rightSupport second secondSupport) same traffic)
  obtain ⟨nextNoise, law⟩ := updated
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_map, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind] using law

end Vegas
