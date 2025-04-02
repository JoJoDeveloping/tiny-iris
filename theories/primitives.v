From simplesl Require Import lang heapprop.

Local Lemma help1 (h1 h2 : state) : h2 ∖ h1 ⊆ h2.
Proof.
  rewrite map_subseteq_spec. intros k v [H1 H2]%lookup_difference_Some. done.
Qed.


Section pointsto.

  Local Program Definition heapProp_pointsto_def (ℓ : loc) (v : val) : heapProp :=
    {| heapProp_holds σ := σ !! ℓ = Some v |}.
  Next Obligation.
    intros P Q σ1 σ2 Hσ Hlu. eapply lookup_weaken. 2: done. done.
  Qed.
  Local Definition heapProp_pointsto_aux : seal (@heapProp_pointsto_def). Proof. by eexists. Qed.
  Definition pointsto := unseal heapProp_pointsto_aux.
  Local Definition heapProp_pointsto_unseal:
    @pointsto = @heapProp_pointsto_def := seal_eq heapProp_pointsto_aux.

End pointsto.


Notation "l ↦ v" := (pointsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.


Section schu.

  Local Program Definition heapProp_schu_def (e : expr) (P : expr → heapProp) : heapProp :=
    {| heapProp_holds σ := ∀ σ', σ ##ₘ σ' → ∃ e' σ'', σ'' ##ₘ σ' ∧ ctx_step e (σ' ∪ σ) e' (σ' ∪ σ'') ∧ P e' σ'' |}.
  Next Obligation.
    intros e P σ1 σ2 H1 Hσ σ' Hdisj.
    destruct (H1 (σ' ∪ (σ2 ∖ σ1))) as (e'&σ''&[Hresdj1 Hresdj2]%map_disjoint_union_r&Hctx&HP).
    { eapply map_disjoint_union_r. split; first by eapply map_disjoint_weaken_l.
      by eapply map_disjoint_difference_r. }
    exists e', (σ'' ∪ (σ2 ∖ σ1)). split_and!.
    - eapply map_disjoint_union_l. split; first done.
      eapply map_disjoint_weaken_l. 1: exact Hdisj. apply help1.
    - rewrite -map_union_assoc in Hctx.
      rewrite (map_union_comm _ σ1) in Hctx.
      2: by eapply map_disjoint_difference_l.
      rewrite map_difference_union // in Hctx.
      rewrite (map_union_comm σ'' _) //.
      rewrite map_union_assoc //.
    - eapply heapProp_closed. 1: exact HP. eapply map_union_subseteq_l.
  Qed.
  Local Definition heapProp_schu_aux : seal (@heapProp_schu_def). Proof. by eexists. Qed.
  Definition schu := unseal heapProp_schu_aux.
  Local Definition heapProp_schu_unseal:
    @schu = @heapProp_schu_def := seal_eq heapProp_schu_aux.

  Ltac unseal := try heapprop.unseal; rewrite ?heapProp_schu_unseal ?heapProp_pointsto_unseal /=.

  Lemma schu_wand e P Q : 
    (∀ e', P e' -∗ Q e') -∗
    schu e P -∗ schu e Q.
  Proof.
    rewrite /bi_wand /bi_emp_valid /bi_entails /bi_forall /bi_wand /=. unseal. econstructor.
    intros σ _ σ1 Hσ1 Hforall σ2 [Hσ2a Hσ2b]%map_disjoint_union_l Hupd1 σ3 [[Hσ3a Hσ3b]%map_disjoint_union_l Hσ3c]%map_disjoint_union_l.
    odestruct (Hupd1 (σ3 ∪ σ1 ∪ σ) _) as (e'&σ'&[[Hσ'a Hσ'b]%map_disjoint_union_r Hσ'c]%map_disjoint_union_r&Hctx&HP).
    1: repeat (try done; apply map_disjoint_union_r; split).
    exists e', (σ1 ∪ σ ∪ σ'). split_and!.
    - repeat (try done; apply map_disjoint_union_l; split).
    - rewrite (map_union_comm σ σ1) // !map_union_assoc //.
    - ospecialize (Hforall e' _ _ HP). 1: done. eapply heapProp_closed.
      1: exact Hforall. eapply map_union_mono_r.
      1: by eapply map_disjoint_union_l. eapply map_union_subseteq_l.
  Qed.

  Lemma schu_pure e e' Q : 
    pure_step e e' →
    Q e' ⊢ schu e Q.
  Proof.
    intros Hpure.
    rewrite /bi_entails /=. unseal. econstructor.
    intros σ Hschu σ' Hσ'.
    specialize (Hpure (σ' ∪ σ)) as Hctx.
    exists e', σ. done.
  Qed.

  Lemma schu_lift e K Q :
    schu e Q ⊢ schu (fill K e) (λ e', ∃ e'', ⌜e' = fill K e''⌝ ∗ Q e'').
  Proof.
    rewrite /bi_emp_valid /bi_entails /bi_sep /bi_exist /bi_pure /=. unseal. econstructor.
    intros σ Hschu σ' Hσ'.
    odestruct (Hschu σ' Hσ') as (e''&σ''&Hσ''&Hctx&HQ).
    exists (fill K e''), σ''. split_and!.
    - done.
    - by eapply ctx_step_fill.
    - exists e'', ∅, σ''. split_and!; try done.
      + rewrite map_empty_union //.
      + eapply map_disjoint_empty_l.
  Qed.

  Lemma schu_read ℓ v :
    ℓ ↦ v ⊢ schu (Load (Loc ℓ)) (λ e', ⌜e' = of_val v⌝ ∗ ℓ ↦ v).
  Proof.
    rewrite /bi_emp_valid /bi_entails /bi_sep /bi_exist /bi_pure /=. unseal. econstructor.
    intros σ Hσ σ' Hσ'.
    exists (of_val v), σ. split_and!.
    - done.
    - eapply ctx_step_base_step. econstructor.
      eapply lookup_union_Some_r. 2: apply Hσ.
      done.
    - exists ∅, σ. split_and!; try done.
      + rewrite map_empty_union //.
      + eapply map_disjoint_empty_l.
  Qed.

  Lemma schu_write ℓ v v' :
    ℓ ↦ v ⊢ schu (Store (Loc ℓ) (of_val v')) (λ e', ⌜e' = of_val v⌝ ∗ ℓ ↦ v').
  Proof.
    rewrite /bi_emp_valid /bi_entails /bi_sep /bi_exist /bi_pure /=. unseal. econstructor.
    intros σ Hσ σ' Hσ'.
    assert (σ' !! ℓ = None) as Hσ'N.
    { eapply map_disjoint_Some_l; first done. apply Hσ. }
    exists (of_val v), (<[ ℓ := v']> σ). split_and!.
    - eapply map_disjoint_insert_l. done.
    - eapply ctx_step_base_step. rewrite -insert_union_r //.
      econstructor.
      eapply lookup_union_Some_r. 2: apply Hσ.
      done.
    - exists ∅, (<[ ℓ := v']> σ). split_and!; try done.
      + rewrite map_empty_union //.
      + eapply map_disjoint_empty_l.
      + apply lookup_insert.
  Qed.

  Lemma schu_alloc v : 
    ⊢ schu (New (of_val v)) (λ e', ∃ ℓ, ⌜e' = Loc ℓ⌝ ∗ ℓ ↦ v).
  Proof.
    rewrite /bi_emp_valid /bi_entails /bi_sep /bi_exist /bi_pure /=. unseal. econstructor.
    intros σ _ σ' Hσ'.
    pose (fresh (dom (σ' ∪ σ))) as ℓ.
    pose proof (is_fresh (dom (σ' ∪ σ))) as Hfresh. fold ℓ in Hfresh.
    eapply not_elem_of_dom in Hfresh. eapply lookup_union_None in Hfresh as [Hf1 Hf2].
    exists (Loc ℓ), (<[ ℓ := v ]> σ). split_and!.
    - eapply map_disjoint_insert_l. done.
    - eapply ctx_step_base_step. rewrite -insert_union_r //.
      econstructor. eapply is_fresh.
    - exists ℓ,  ∅, (<[ ℓ := v]> σ). split_and!; try done.
      + rewrite map_empty_union //.
      + eapply map_disjoint_empty_l.
      + apply lookup_insert.
  Qed.

  Lemma schu_elim e Q σ σ' :
    schu e Q σ → 
    σ ##ₘ σ' → 
    ∃ e' σ'', σ'' ##ₘ σ' ∧ ctx_step e (σ' ∪ σ) e' (σ' ∪ σ'') ∧ Q e' σ''.
  Proof.
    unseal. intros H Hdisj. by eapply H.
  Qed.

End schu.

Notation "e  ⇝  e' , Q" := (schu e (λ e', Q)) (at level 20) : bi_scope.
