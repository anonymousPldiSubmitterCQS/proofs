Require Import SegmentQueue.lib.thread_queue.thread_queue.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
Require Import SegmentQueue.lib.util.future.
From iris.heap_lang Require Import notation.

Section impl.

Variable array_interface: infiniteArrayInterface.

Definition newSemaphore: val :=
  λ: "n", (ref "n", newThreadQueue array_interface #()).

Definition acquireSemaphore: val :=
  λ: "sem",
  let: "availablePermits" := Fst ("sem") in
  let: "e" := Fst (Snd ("sem")) in
  let: "p" := FAA "availablePermits" #(-1) in
  if: #0 < "p" then fillThreadQueueFuture #()
  else match: suspend array_interface "e" with
           InjR "v" => "v"
         | InjL "x" => "undefined"
       end.

Definition semaphoreResume: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #false #false "d"
                 (λ: <>, #()) #().

Definition releaseSemaphore: val :=
  λ: "sem",
  let: "availablePermits" := Fst ("sem") in
  let: "d" := Snd (Snd ("sem")) in
  let: "p" := FAA "availablePermits" #1 in
  if: #0 ≤ "p" then #()
  else semaphoreResume "d" ;; #().

Definition cancelSemaphoreFuture : val :=
  λ: "sem" "f",
  let: "availablePermits" := Fst ("sem") in
  let: "d" := Snd (Snd ("sem")) in
  tryCancelThreadQueueFuture' array_interface
                              #false #(Z.of_nat 300) #false #false
                              "d" (λ: <>, FAA "availablePermits" #1 < #0)
                              (λ: <>, #()) (λ: <>, releaseSemaphore "sem") "f".

End impl.

From SegmentQueue.util Require Import everything big_opL.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ}.
Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Let NSem := N .@ "Sem".
Let NTq := N .@ "Tq".
Notation iProp := (iProp Σ).

Definition semaphore_inv (R: iProp) (γtq: gname) (availablePermits: nat)
           (p: loc) : iProp :=
 ([∗] replicate availablePermits R) ∗
 ∃ enqueuedThreads, thread_queue_state γtq enqueuedThreads ∗
 p ↦ #(availablePermits - enqueuedThreads) ∗
 ⌜availablePermits = 0 ∨ enqueuedThreads = 0⌝.

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Let tqParams R :=
  @ThreadQueueParameters Σ false True R True (fun v => ⌜#v = #()⌝)%I False.

Let isThreadQueue R := is_thread_queue NTq NFuture (tqParams R) _ array_spec.

Definition is_semaphore_future R :=
  is_thread_queue_future NTq NFuture (tqParams R) _ array_spec.

Definition is_semaphore R γa γtq γe γd (s: val): iProp :=
  ∃ e d (p: loc), ⌜s = (#p, (e, d))%V⌝ ∧
  inv NSem (∃ availablePermits, semaphore_inv R γtq availablePermits p)
  ∗ isThreadQueue R γa γtq γe γd e d.

Theorem newSemaphore_spec (n: nat) R:
  {{{ inv_heap_inv ∗ [∗] replicate n R }}}
    newSemaphore array_interface #n
  {{{ γa γtq γe γd s, RET s; is_semaphore R γa γtq γe γd s }}}.
Proof.
  iIntros (Φ) "[#HHeap HR] HΦ". wp_lam. wp_bind (newThreadQueue _ _).
  iApply (newThreadQueue_spec with "HHeap").
  iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
  rewrite -wp_fupd. wp_alloc p as "Hp". wp_pures.
  iMod (inv_alloc NSem _ (∃ a, semaphore_inv R γtq a p) with "[-HΦ]") as "#HInv".
  { iExists _. iFrame "HR". iExists 0. rewrite Z.sub_0_r. iFrame. by iRight. }
  iApply "HΦ". iExists _, _, _. iSplitR; first done. by iFrame "HInv HTq".
Qed.

Lemma resumeSemaphore_spec R maxWait (wait: bool) γa γtq γe γd e d:
  {{{ isThreadQueue R γa γtq γe γd e d ∗ awakening_permit γtq }}}
    resume array_interface #(Z.of_nat maxWait) #true #false #wait d (λ: <>, #())%V #()
  {{{ RET #true; True }}}.
Proof.
  iIntros (Φ) "[#HTq HAwak] HΦ".
  iApply (resume_spec with "[] [HAwak]").
  5: { by iFrame "HTq HAwak". }
  by solve_ndisj. done. done.
  { simpl. iIntros (Ψ) "!> [% _] HΨ". wp_pures. by iApply "HΨ". }
  iIntros "!>" (r) "Hr". simpl. destruct r; first by iApply "HΦ".
  iDestruct "Hr" as "[% _]". lia.
Qed.

Theorem releaseSemaphore_spec R γa γtq γe γd s:
  {{{ is_semaphore R γa γtq γe γd s ∗ R }}}
    releaseSemaphore array_interface s
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HIsSem HR] HΦ". wp_lam.
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_pures. wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  destruct (decide (0 ≤ availablePermits - enqueuedThreads)%Z) as [HGe|HLt].
  - assert (enqueuedThreads = 0) as -> by lia. rewrite Z.sub_0_r.
    wp_faa. iMod ("HClose" with "[-HΦ]") as "_".
    { iExists (S availablePermits). iFrame "HR HRs". iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      replace (availablePermits + 1)%Z with (Z.of_nat (S availablePermits))
        by lia.
      by rewrite Z.sub_0_r. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    by iApply "HΦ".
  - iMod (thread_queue_register_for_dequeue' with "HTq [HR] HState")
      as "[HState HAwak]"; [by solve_ndisj|lia|by iFrame|].
    wp_faa. iMod ("HClose" with "[-HΦ HAwak]") as "_".
    { iExists availablePermits. iFrame "HRs". iExists (enqueuedThreads - 1).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      by replace (availablePermits - enqueuedThreads + 1)%Z with
          (availablePermits - (enqueuedThreads - 1)%nat)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_lam. wp_pures. wp_apply (resumeSemaphore_spec with "[$]"). iIntros "_".
    wp_pures. by iApply "HΦ".
Qed.

Theorem acquireSemaphore_spec R γa γtq γe γd s:
  {{{ is_semaphore R γa γtq γe γd s }}}
    acquireSemaphore array_interface s
  {{{ γf v, RET v; is_semaphore_future R γtq γa γf v ∗
                   thread_queue_future_cancellation_permit γf }}}.
Proof.
  iIntros (Φ) "#HIsSem HΦ". wp_lam.
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_pures. wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  destruct (decide (0 < availablePermits - enqueuedThreads)%Z) as [HGe|HLt].
  - assert (enqueuedThreads = 0) as -> by lia. rewrite Z.sub_0_r.
    destruct availablePermits as [|availablePermits']=> /=; first lia.
    iDestruct "HRs" as "[HR HRs]".
    wp_faa. iMod ("HClose" with "[-HΦ HR]") as "_".
    { iExists availablePermits'. iFrame "HRs". iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      replace (S availablePermits' + -1)%Z with (Z.of_nat availablePermits')
        by lia.
      by rewrite Z.sub_0_r. }
    iModIntro. wp_pures. iApply (fillThreadQueueFuture_spec with "[HR]").
    2: {
      iIntros "!>" (γf v') "(HFuture & HCancPermit & _)".
      iApply "HΦ". iFrame.
    }
    rewrite /V'. iExists _. iSplitR; first done. simpl.
    iSplitR; first done. iFrame.
  - iMod (thread_queue_append' with "HTq [] HState")
      as "[HState HSus]"=> /=; [by solve_ndisj|done|].
    wp_faa. iMod ("HClose" with "[-HΦ HSus]") as "_".
    { iExists availablePermits. iFrame "HRs". iExists (S enqueuedThreads).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      by replace (availablePermits - enqueuedThreads + -1)%Z with
          (availablePermits - S enqueuedThreads)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_apply (suspend_spec with "[$]")=> /=. iIntros (v) "[(_ & _ & %)|Hv]".
    done.
    iDestruct "Hv" as (γf v') "(-> & HFuture & HCancPermit)". wp_pures.
    iApply "HΦ". iFrame.
Qed.

Theorem cancelSemaphoreFuture_spec R γa γtq γe γd s γf f:
  is_semaphore R γa γtq γe γd s -∗
  is_semaphore_future R γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf >>>
    cancelSemaphoreFuture array_interface s f @ ⊤ ∖ ↑NFuture ∖ ↑N
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf
      else (∃ v, ▷ future_is_completed γf v) ∗
           thread_queue_future_cancellation_permit γf, RET #r >>>.
Proof.
  iIntros "#HIsSem #HFuture" (Φ) "AU".
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_lam. wp_pures. wp_lam.
  wp_pures. awp_apply (try_cancel_thread_queue_future with "HTq HFuture");
              first by solve_ndisj.
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj.
  iIntros "HCancPermit". iAaccIntro with "HCancPermit". by iIntros "$ !> $ !>".
  iIntros (r) "Hr". iExists r. destruct r.
  2: { iDestruct "Hr" as "[$ $]". iIntros "!> HΦ !>". by wp_pures. }
  iDestruct "Hr" as "[#HFutureCancelled Hr]". iFrame "HFutureCancelled".
  rewrite /is_semaphore_future /is_thread_queue_future.
  iDestruct "Hr" as (i f' s ->) "Hr"=> /=.
  iDestruct "Hr" as "(#H↦~ & #HTh & HToken)". iIntros "!> HΦ !>". wp_pures.
  wp_lam. wp_pures. wp_apply derefCellPointer_spec.
  by iDestruct "HTq" as "(_ & $ & _)". iIntros (ℓ) "#H↦". wp_pures.
  wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(>HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  iMod (register_cancellation with "HTq HToken HState")
       as "[HCancToken HState]"; first by solve_ndisj.
  destruct (decide (availablePermits - enqueuedThreads < 0)%Z) as [HLt|HGe].
  - assert (availablePermits = 0) as -> by lia.
    destruct enqueuedThreads as [|enqueuedThreads']=>/=; first lia.
    iDestruct "HState" as "(HState & HCancHandle & #HInhabited)".
    wp_faa.
    iMod ("HClose" with "[-HΦ HCancToken HCancHandle]") as "_".
    { iExists 0. iSplitR; simpl; first done. iExists enqueuedThreads'.
      rewrite Nat.sub_0_r. iFrame "HState". iSplitL; last by iLeft.
      by replace (0%nat - S enqueuedThreads' + 1)%Z
        with (0%nat - enqueuedThreads')%Z by lia. }
    iModIntro. wp_pures. wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markCancelled_spec with "HTq HInhabited H↦ HCancToken HTh")
              without "HΦ HCancHandle".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> [HΦ HCancHandle]". wp_pures.
    iAssert (▷ cell_cancellation_handle _ _ _ _ _ _)%I
            with "[HCancHandle]" as "HCancHandle"; first done.
    awp_apply (onCancelledCell_spec with "[] H↦~") without "Hv HΦ".
    by iDestruct "HTq" as "(_ & $ & _)".
    iAaccIntro with "HCancHandle". by iIntros "$".
    iIntros "#HCancelled !> [Hv HΦ]". wp_pures.
    iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (x ->) "(#HInhabited' & HAwak & %)"; simplify_eq.
    wp_pures. wp_apply (resumeSemaphore_spec with "[$]"). iIntros "_".
    by wp_pures.
  - rewrite bool_decide_true; last lia. assert (enqueuedThreads = 0) as -> by lia.
    simpl. iDestruct "HState" as "(HState & HR & #HInhabited)".
    wp_faa.
    iMod ("HClose" with "[-HΦ HCancToken]") as "_".
    { iExists (S availablePermits). iFrame "HR HRs". iExists 0.
      iFrame "HState". iSplitL; last by iRight.
      by replace (availablePermits - 0%nat + 1)%Z
        with (S availablePermits - 0%nat)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markRefused_spec with "HTq HInhabited H↦ HCancToken HTh [//]")
              without "HΦ".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> HΦ". iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (? ->) "[_ >%]". simplify_eq. by wp_pures.
Qed.

End proof.

Section client.

Variable array_interface: infiniteArrayInterface.

(* a workaround: this version of Iris doesn't support later credits, and we need
   'awaitThreadQueueFuture' to make at least one execution step. *)
Definition awaitThreadQueueFuture': val :=
  λ: "f", let: "x" := awaitThreadQueueFuture "f" in #();; "x".

Definition useSemaphore: expr :=
  let: "l" := ref #0 in
  let: "s" := newSemaphore array_interface #(1%nat) in
  let: "doneMarker" := ref #false in
  Fork (
      awaitThreadQueueFuture' (acquireSemaphore array_interface "s") ;;
      "l" <- !"l" + #1 ;;
      releaseSemaphore array_interface "s" ;;
      "doneMarker" <- #true
  ) ;;
  awaitThreadQueueFuture' (acquireSemaphore array_interface "s") ;;
  "l" <- !"l" + #1 ;;
  releaseSemaphore array_interface "s" ;;
  (rec: "wait" "_" := (!"doneMarker" = #true) || "wait" #()) #() ;;
  !"l".

Notation threadState := (optionUR (csumR (exclR unitO) (agreeR unitO))).

Notation clientStateR := (authUR (prodUR threadState threadState)).

Class clientStateG Σ := ClientStateG {clientState_inG :> inG Σ clientStateR;}.
Definition clientStateΣ : gFunctors := #[GFunctor clientStateR].
Global Instance subG_clientStateR {Σ} : subG clientStateΣ Σ → clientStateG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ} `{clientStateG Σ}.
Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Notation iProp := (iProp Σ).

Variable array_spec: infiniteArraySpec _ array_interface.

Definition weFinished γ := own γ (◯ (Some (Cinr (to_agree ())), None)).
Definition parallelFinished γ := own γ (◯ (None, Some (Cinr (to_agree ())))).
Definition ourToken γ := own γ (◯ (Some (Cinl (Excl ())), None)).
Definition parallelToken γ := own γ (◯ (None, Some (Cinl (Excl ())))).

Definition useSemaphore_inv_l γ l: iProp :=
  (
    l ↦{1/2} #2 ∗ own γ (● (Some (Cinr (to_agree ())), Some (Cinr (to_agree ())))) ∨
    l ↦{1/2} #1 ∗ own γ (● (Some (Cinr (to_agree ())), Some (Cinl (Excl ())))) ∨
    l ↦{1/2} #1 ∗ own γ (● (Some (Cinl (Excl ())), Some (Cinr (to_agree ())))) ∨
    l ↦{1/2} #0 ∗ own γ (● (Some (Cinl (Excl ())), Some (Cinl (Excl ()))))
  ).

Definition useSemaphore_inv_doneMarker γ doneMarker: iProp :=
  doneMarker ↦ #false ∨ doneMarker ↦ #true ∧ parallelFinished γ.

Theorem awaitSemaphoreFuture R γa γtq γe γd s γf v:
  {{{ is_semaphore N NFuture array_interface array_spec R γa γtq γe γd s
      ∗ is_semaphore_future N NFuture array_interface array_spec R γtq γa γf v
      ∗ thread_queue_future_cancellation_permit γf
  }}}
    awaitThreadQueueFuture' v
  {{{ RET (InjRV #()); R }}}.
Proof.
  iIntros (Φ) "(#HIsSem & #HFuture & HCancPermit) HΦ".
  iDestruct "HIsSem" as (b c d) "(H1 & H2 & HTq)". rewrite /awaitThreadQueueFuture'.
  awp_apply await_thread_future without "HΦ"; [|done|done|].
  by solve_ndisj.
  iAaccIntro with "HCancPermit".
  { iIntros ">H !>". by iFrame. }
  simpl. iIntros (?) "(-> & R & _)". iModIntro. iIntros "HΦ".
  wp_pures. iApply ("HΦ" with "R").
Qed.

Lemma finishLocalWork γ (e: threadState):
  own γ (● (Some (Cinl (Excl ())), e)) -∗ own γ (◯ (Some (Cinl (Excl ())), None)) ==∗
  own γ (● (Some (Cinr (to_agree ())), e)) ∗ weFinished γ.
Proof.
  iIntros "H1 H2". iMod (own_update_2 with "H1 H2") as "[$ $]"; last done.
  apply auth_update, prod_local_update; last done; simpl.
  etransitivity.
  by apply delete_option_local_update, Cinl_exclusive, excl_exclusive.
  by apply alloc_option_local_update.
Qed.

Lemma finishParallelWork γ (e: threadState):
  own γ (● (e, Some (Cinl (Excl ())))) -∗ own γ (◯ (None, Some (Cinl (Excl ())))) ==∗
  own γ (● (e, Some (Cinr (to_agree ())))) ∗ parallelFinished γ.
Proof.
  iIntros "H1 H2". iMod (own_update_2 with "H1 H2") as "[$ $]"; last done.
  apply auth_update, prod_local_update; first done; simpl.
  etransitivity.
  by apply delete_option_local_update, Cinl_exclusive, excl_exclusive.
  by apply alloc_option_local_update.
Qed.

Lemma CinlCinr_included {A B: cmraT} (a: A) (b: B): Some (Cinl a) ≼ Some (Cinr b) -> False.
Proof.
  intros contra. apply Some_included in contra. destruct contra as [contra|contra].
  by inversion contra.
  apply csum_included in contra.
  destruct contra as [contra|[(? & ? & (_ & contra & _))|(? & ? & (contra & _ & _))]];
    by inversion contra.
Qed.

Lemma CinrCinl_included {A: cmraT} {B: cmraT} (a: A) (b: B): Some (Cinr a) ≼ Some (Cinl b) -> False.
Proof.
  intros contra. apply Some_included in contra. destruct contra as [contra|contra].
  by inversion contra.
  apply csum_included in contra.
  destruct contra as [contra|[(? & ? & (contra & _ & _))|(? & ? & (_ & contra & _))]];
    by inversion contra.
Qed.

Theorem useSemaphore_proof:
  {{{ inv_heap_inv }}} useSemaphore {{{ RET #2; True }}}.
Proof.
  iIntros (Φ) "HHeapInv HPost". rewrite /useSemaphore. wp_alloc l as "Hl". wp_pures.
  wp_bind (newSemaphore _ _).
  iMod (own_alloc (
            ● (Some (Cinl (Excl ())), Some (Cinl (Excl ()))) ⋅
            (◯ (None, Some (Cinl (Excl ()))) ⋅ ◯ (Some (Cinl (Excl ())), None))))
    as (γ) "(H● & HParallel & HOur)"; first by apply auth_both_valid.
  iDestruct "Hl" as "[Hl Hl']".
  wp_apply (newSemaphore_spec N NFuture _ array_spec 1 (∃ n, l ↦{1/2} #n)%I with "[HHeapInv Hl']").
  { iFrame "HHeapInv". simpl. iSplitL; last done. iExists 0. done. }
  iIntros (γa γtq γe γd s) "#HIsSem". wp_pures.
  wp_alloc doneMarker as "HDone".
  iMod (inv_alloc N _ (useSemaphore_inv_l γ l) with "[H● Hl]") as "#HInv".
  { iRight. iRight. iRight. iFrame. }
  iMod (inv_alloc N _ (useSemaphore_inv_doneMarker γ doneMarker) with "[HDone]") as "#HInvDone";
    first by iFrame.
  wp_pures. wp_apply (wp_fork with "[HParallel]").
  - iModIntro. wp_bind (acquireSemaphore _ _).
    iApply (acquireSemaphore_spec with "[$]").
    iIntros "!>" (γf v) "[#HFuture HCancPermit]".
    wp_apply (awaitSemaphoreFuture with "[HCancPermit]").
    by iFrame "HIsSem HFuture HCancPermit".
    iIntros "HR". iDestruct "HR" as (n) "Hl". wp_pures.
    wp_bind (!#l)%E.
    iInv "HInv" as "[(_ & >H●)|[(>Hl' & >H●)|[(_ & >H●)|(>Hl' & >H●)]]]".
    all: try by iDestruct (own_valid_2 with "H● HParallel") as
          %[[_ Hr%CinlCinr_included]%pair_included _]%auth_both_valid.
    * iDestruct (mapsto_agree with "Hl Hl'") as %->.
      wp_load. iModIntro. iSplitL "H● Hl'".
      { iRight. iLeft. by iFrame. }
      wp_pures. wp_bind (#l <- _)%E.
      iInv "HInv" as "[(_ & >H●)|[(>Hl' & >H●)|[(_ & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HParallel") as
            %[[_ Hr%CinlCinr_included]%pair_included _]%auth_both_valid.
      2: by iDestruct (mapsto_agree with "Hl Hl'") as %HEq.
      iCombine "Hl" "Hl'" as "Hl".
      wp_store.
      iDestruct "Hl" as "[Hl Hl']".
      iMod (finishParallelWork with "H● HParallel") as "[H● #HParallelFinished]".
      iSplitL "Hl H●".
      { iLeft. by iFrame. }
      iModIntro. wp_pures.
      wp_apply (releaseSemaphore_spec with "[Hl']").
      2: by iFrame "HIsSem"; iExists 2; iFrame "Hl'".
      1: by solve_ndisj.
      iIntros "_". wp_pures.
      iInv "HInvDone" as "[HDone|[HDone _]]"; wp_store; (iSplitL; [iRight; by iFrame|done]).
    * iDestruct (mapsto_agree with "Hl Hl'") as %->.
      wp_load. iModIntro. iSplitL "H● Hl'".
      { iRight. iRight. iRight. by iFrame. }
      wp_pures. wp_bind (#l <- _)%E.
      iInv "HInv" as "[(_ & >H●)|[(>Hl' & >H●)|[(_ & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HParallel") as
            %[[_ Hr%CinlCinr_included]%pair_included _]%auth_both_valid.
      1: by iDestruct (mapsto_agree with "Hl Hl'") as %HEq.
      iCombine "Hl" "Hl'" as "Hl".
      wp_store.
      iDestruct "Hl" as "[Hl Hl']".
      iMod (finishParallelWork with "H● HParallel") as "[H● #HParallelFinished]".
      iSplitL "Hl H●".
      { iRight. iRight. iLeft. by iFrame. }
      iModIntro. wp_pures.
      wp_apply (releaseSemaphore_spec with "[Hl']").
      2: by iFrame "HIsSem"; iExists 1; iFrame "Hl'".
      1: by solve_ndisj.
      iIntros "_". wp_pures.
      iInv "HInvDone" as "[HDone|[HDone _]]"; wp_store; (iSplitL; [iRight; by iFrame|done]).
  - wp_pures. wp_bind (acquireSemaphore _ _).
    iApply (acquireSemaphore_spec with "[$]").
    iIntros "!>" (γf v) "[#HFuture HCancPermit]".
    wp_apply (awaitSemaphoreFuture with "[HCancPermit]").
    by iFrame "HIsSem HFuture HCancPermit".
    iIntros "HR". iDestruct "HR" as (n) "Hl". wp_pures.
    wp_bind (!#l)%E.
    iInv "HInv" as "[(>Hl' & >H●)|[(>Hl' & >H●)|[(>Hl' & >H●)|(>Hl' & >H●)]]]".
    all: try by iDestruct (own_valid_2 with "H● HOur") as
          %[[Hr%CinlCinr_included _]%pair_included _]%auth_both_valid.
    * iDestruct (mapsto_agree with "Hl Hl'") as %->.
      wp_load. iModIntro. iSplitL "H● Hl'".
      { iRight. iRight. iLeft. by iFrame. }
      wp_pures. wp_bind (#l <- _)%E.
      iInv "HInv" as "[(>Hl' & >H●)|[(>Hl' & >H●)|[(>Hl' & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HOur") as
            %[[Hr%CinlCinr_included _]%pair_included _]%auth_both_valid.
      2: by iDestruct (mapsto_agree with "Hl Hl'") as %HEq.
      iCombine "Hl" "Hl'" as "Hl".
      wp_store.
      iDestruct "Hl" as "[Hl Hl']".
      iMod (finishLocalWork with "H● HOur") as "[H● #HWorkFinished]".
      iSplitL "Hl H●".
      { iLeft. by iFrame. }
      iModIntro. wp_pures.
      wp_apply (releaseSemaphore_spec with "[Hl']").
      2: by iFrame "HIsSem"; iExists 2; iFrame "Hl'".
      1: by solve_ndisj.
      iIntros "_". wp_pures.
      iLöb as "IH". wp_bind (!#doneMarker)%E.
      iInv "HInvDone" as "[HDone|[HDone #HTheyFinished]]" "HClose".
      { wp_load. iMod ("HClose" with "[$]") as "_". iModIntro.
        wp_pures. iApply ("IH" with "HPost"). }
      wp_load. iMod ("HClose" with "[HDone]") as "_"; first by iRight; iFrame.
      iModIntro. wp_pures. iClear "IH".
      iInv "HInv" as "[(>Hl' & >H●)|[(>Hl' & >H●)|[(>Hl' & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HWorkFinished") as
            %[[Hr%CinrCinl_included _]%pair_included _]%auth_both_valid.
      all: try by iDestruct (own_valid_2 with "H● HTheyFinished") as
            %[[_ Hr%CinrCinl_included]%pair_included _]%auth_both_valid.
      wp_load.
      iSplitR "HPost".
      { iLeft. iFrame. done. }
      by iApply "HPost".
    * iDestruct (mapsto_agree with "Hl Hl'") as %->.
      wp_load. iModIntro. iSplitL "H● Hl'".
      { iRight. iRight. iRight. by iFrame. }
      wp_pures. wp_bind (#l <- _)%E.
      iInv "HInv" as "[(>Hl' & >H●)|[(>Hl' & >H●)|[(>Hl' & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HOur") as
            %[[Hr%CinlCinr_included _]%pair_included _]%auth_both_valid.
      1: by iDestruct (mapsto_agree with "Hl Hl'") as %HEq.
      iCombine "Hl" "Hl'" as "Hl".
      wp_store.
      iDestruct "Hl" as "[Hl Hl']".
      iMod (finishLocalWork with "H● HOur") as "[H● #HWorkFinished]".
      iSplitL "Hl H●".
      { iRight. iLeft. by iFrame. }
      iModIntro. wp_pures.
      wp_apply (releaseSemaphore_spec with "[Hl']").
      2: by iFrame "HIsSem"; iExists 1; iFrame "Hl'".
      1: by solve_ndisj.
      iIntros "_". wp_pures.
      iLöb as "IH". wp_bind (!#doneMarker)%E.
      iInv "HInvDone" as "[HDone|[HDone #HTheyFinished]]" "HClose".
      { wp_load. iMod ("HClose" with "[$]") as "_". iModIntro.
        wp_pures. iApply ("IH" with "HPost"). }
      wp_load. iMod ("HClose" with "[HDone]") as "_"; first by iRight; iFrame.
      iModIntro. wp_pures. iClear "IH".
      iInv "HInv" as "[(>Hl' & >H●)|[(>Hl' & >H●)|[(>Hl' & >H●)|(>Hl' & >H●)]]]".
      all: try by iDestruct (own_valid_2 with "H● HWorkFinished") as
            %[[Hr%CinrCinl_included _]%pair_included _]%auth_both_valid.
      all: try by iDestruct (own_valid_2 with "H● HTheyFinished") as
            %[[_ Hr%CinrCinl_included]%pair_included _]%auth_both_valid.
      wp_load.
      iSplitR "HPost".
      { iLeft. iFrame. done. }
      by iApply "HPost".
Qed.

End client.
