From simplesl Require Import lang heapprop primitives weakestpre.

Section wpbigstep.
  Local Lemma help1 (h1 h2 : state) : h2 ∖ h1 ⊆ h2.
  Proof.
    rewrite map_subseteq_spec. intros k v [H1 H2]%lookup_difference_Some. done.
  Qed.

  Program Definition wpbigstep (e : expr) (Q : val → heapProp) : heapProp :=
    {| heapProp_holds σ := ∀ σ2, σ ##ₘ σ2 → ∃ v' σ', σ' ##ₘ σ2 ∧ ctx_steps e (σ ∪ σ2) (of_val v') (σ' ∪ σ2) ∧ Q v' σ' |}.
  Next Obligation.
    intros e Q h1 h2 H Hincl hf Hfdisj.
    odestruct (H (hf ∪ (h2 ∖ h1)) _) as (v'&h'&[Hd1 Hd2]%map_disjoint_union_r&Hsteps&HQ).
    { eapply map_disjoint_union_r. split; last by eapply map_disjoint_difference_r.
      eapply map_disjoint_weaken_l; done. }
    exists v', ((h2 ∖ h1) ∪ h'). split_and!.
    - eapply map_disjoint_union_l. split; last done. eapply map_disjoint_weaken_l. 2: eapply help1. done.
    - rewrite !(map_union_comm hf _) in Hsteps. 2: eapply map_disjoint_weaken_r; last by eapply help1. 2: done.
      rewrite (map_union_comm _ h'). 2: done. rewrite !map_union_assoc in Hsteps.
      rewrite map_difference_union in Hsteps; last done. apply Hsteps.
    - eapply heapProp_closed. 1: exact HQ. eapply map_union_subseteq_r. done.
  Qed.

  Lemma wp_tobigstep e Q : wp e Q ⊢ wpbigstep e Q.
  Proof.
    iIntros "H".
    iApply (wp_iter e _ (λ e, wpbigstep e Q)%I with "[] H"). clear e.
    iIntros "!> %e [(%v&->&Hv)|Hschu]"; iStopProof; rewrite /bi_entails /heapPropI /=; econstructor.
    - intros σ HQ σ' Hσ'. exists v, σ. unfold ctx_steps. done.
    - intros σ Hframe σ' Hσ'.
      odestruct (schu_elim _ _ _ σ' Hframe Hσ') as (e''&σ''&Hdisj1&Hctx&Hmid).
      destruct (Hmid σ' Hdisj1) as (v'&σ'''&Hdisj2&Hctx'&HQ).
      exists v', σ'''. split_and!. 1, 3: done.
      eapply rtc_l; last done. simpl. by rewrite !(map_union_comm _ σ').
  Qed.
End wpbigstep.

Lemma wp_soundness e Q : (⊢ wp e (λ v, ⌜Q v⌝))%I → ∀ σ, ∃ v σ', ctx_steps e σ (of_val v) σ' ∧ Q v.
Proof.
  rewrite wp_tobigstep /bi_emp_valid /bi_entails /bi_emp /bi_pure /heapPropI /heapProp_emp. unseal.
  intros [H] σ. specialize (H σ).
  odestruct (H _ ∅ _) as (v'&σ''&HH1&HH2&HH3). 1: done.
  1: eapply map_disjoint_empty_r.
  rewrite !map_union_empty in HH2.
  exists v', σ''. split; first exact HH2. apply HH3.
Qed.

Lemma wp_safe e Q : (⊢ wp e Q)%I → ∀ σ, ∃ v σ', ctx_steps e σ (of_val v) σ'.
Proof.
  intros H σ.
  odestruct (wp_soundness e (λ _, True) _ σ) as (v&σ'&Hc&_); last by eexists _, _.
  iStartProof. iPoseProof H as "H".
  iApply (wp_wand with "[] H"). iIntros "%x _". done.
Qed.