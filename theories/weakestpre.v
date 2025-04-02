From simplesl Require Import lang heapprop primitives.
Require Import iris.bi.lib.fixpoint.

Section wp.

  Definition wpre (Q : val → heapProp) (wp : expr → heapProp) (e : expr) : heapProp :=
    ((∃ v, ⌜e = of_val v⌝ ∗ Q v) ∨ (e ⇝ e', wp e'))%I.

  Instance wpre_mono Q : @BiMonoPred _ (leibnizO expr) (wpre Q).
  Proof.
    econstructor; last first.
    { intros Φ _. econstructor. cbv in H. subst x. done. }
    intros Φ Ψ _ _. iIntros "#H %x [(%v&->&HH)|H2]".
    - iLeft. iExists v. iFrame. done.
    - iRight. iApply (schu_wand with "[] H2").
      iApply "H".
  Qed.

  Local Definition wp' (e : expr) (Q : val → heapProp) : heapProp :=
    @bi_least_fixpoint _ (leibnizO expr) (wpre Q) e.
  Local Definition wp_aux : seal (@wp'). Proof. by eexists. Qed.
  Definition wp := unseal wp_aux.
  Local Definition wp_unseal':
    @wp = @wp' := seal_eq wp_aux.

  Lemma wp_unfold e Q : wp e Q ≡ wpre Q (λ e, wp e Q) e.
  Proof. rewrite wp_unseal' {1}/wp' least_fixpoint_unfold //. Qed.

  Lemma wp_iter e Q (P : expr → heapProp) :
    □ (∀ e, wpre Q P e -∗ P e) -∗ wp e Q -∗ P e.
  Proof.
    rewrite wp_unseal'.
    iIntros "H". iRevert (e). iRevert "H". 
    unshelve iApply (@least_fixpoint_iter _ (leibnizO expr) (wpre Q) P _).
  Qed.

  Lemma wp_wand e P Q : (∀ v, P v -∗ Q v) -∗ wp e P -∗ wp e Q.
  Proof.
    iIntros "Hwand Hwp". iRevert "Hwand".
    iApply (wp_iter e P (λ e, (∀ v, P v -∗ Q v) -∗ wp e Q)%I with "[] Hwp").
    clear e. iIntros "!> %e [(%v&->&HH)|H2] Hwand"; rewrite wp_unfold.
    - iLeft. iExists v. iSplit; first done.
      iApply ("Hwand" with "HH").
    - iRight. iApply (schu_wand with "[Hwand] H2").
      iIntros (e') "H". iApply ("H" with "Hwand").
  Qed.

  Lemma wp_bind e K Q : wp e (λ v, wp (fill K (of_val v)) Q) -∗ wp (fill K e) Q.
  Proof.
    iIntros "Hwp".
    iApply (wp_iter e _ (λ e, wp (fill K e) Q)%I with "[] Hwp").
    clear e. iIntros "!> %e [(%v&->&HH)|H2]"; rewrite wp_unfold.
    - done.
    - iRight. iApply (schu_wand with "[] [H2]"). 2: iApply schu_lift; iApply "H2".
      iIntros (e') "(%e''&->&HH)". done.
  Qed.

  Lemma wp_value v Q : Q v -∗ wp (of_val v) Q.
  Proof.
    iIntros "H". rewrite wp_unfold. iLeft. iExists v.
    iFrame. done.
  Qed.

  Lemma wp_pure_step e e' Q :
    pure_step e e' →
    wp e' Q -∗
    wp e  Q.
  Proof.
    iIntros (Hstep) "Hwp". rewrite (wp_unfold e).
    iRight. iApply schu_pure; done.
  Qed.

  Lemma wp_load ℓ v Q :
    (ℓ ↦ v ∗ (ℓ ↦ v -∗ Q v)) -∗
    wp (Load (Loc ℓ)) Q.
  Proof.
    iIntros "[Hℓ Hacc]". rewrite wp_unfold.
    iRight. iApply (schu_wand with "[Hacc] [Hℓ]"); last first.
    - iApply schu_read. iFrame.
    - iIntros (e') "[-> Hℓ]". iApply wp_value. iApply "Hacc". iApply "Hℓ".
  Qed.

  Lemma wp_store ℓ v v' Q :
    (ℓ ↦ v ∗ (ℓ ↦ v' -∗ Q v)) -∗
    wp (Store (Loc ℓ) (of_val v')) Q.
  Proof.
    iIntros "[Hℓ Hacc]". rewrite wp_unfold.
    iRight. iApply (schu_wand with "[Hacc] [Hℓ]"); last first.
    - iApply schu_write. iFrame.
    - iIntros (e') "[-> Hℓ]". iApply wp_value. iApply "Hacc". iApply "Hℓ".
  Qed.

  Lemma wp_new v Q :
    (∀ ℓ, ℓ ↦ v -∗ Q (LocV ℓ)) -∗ wp (New (of_val v)) Q.
  Proof.
    iIntros "H". rewrite wp_unfold.
    iRight. iApply (schu_wand with "[H] []"); last first.
    - iApply schu_alloc.
    - iIntros (e') "(%ℓ&->&Hℓ)". iApply (wp_value (LocV _)). iApply "H". iApply "Hℓ".
  Qed.

  Lemma wp_frame P e Q :
    (P ∗ wp e Q) -∗
    wp e (λ v, P ∗ Q v).
  Proof.
    iIntros "(HP&Hwp)".
    iApply (wp_wand with "[HP] Hwp").
    iIntros (v) "$". iFrame.
  Qed.

End wp.