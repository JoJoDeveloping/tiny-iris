From stdpp Require Import gmap.
From iris.bi Require Export interface.
From iris.proofmode Require Export tactics.
From simplesl Require Export lang.
From iris.prelude Require Import options.

Record heapProp := HeapProp {
  heapProp_holds :> gmap loc val → Prop;
  heapProp_closed σ1 σ2 : heapProp_holds σ1 → σ1 ⊆ σ2 → heapProp_holds σ2;
}.
Global Arguments heapProp_holds : simpl never.

Section ofe.
  Inductive heapProp_equiv' (P Q : heapProp) : Prop :=
    { heapProp_in_equiv : ∀ σ, P σ ↔ Q σ }.
  Local Instance heapProp_equiv : Equiv heapProp := heapProp_equiv'.
  Local Instance heapProp_equivalence : Equivalence (≡@{heapProp}).
  Proof. split; repeat destruct 1; constructor; naive_solver. Qed.
  Canonical Structure heapPropO := discreteO heapProp.
End ofe.

(** logical entailement *)
Inductive heapProp_entails (P Q : heapProp) : Prop :=
  { heapProp_in_entails : ∀ σ, P σ → Q σ }.

(** logical connectives *)
Local Program Definition heapProp_pure_def (φ : Prop) : heapProp :=
  {| heapProp_holds _ := φ |}.
Solve Obligations with done.
Local Definition heapProp_pure_aux : seal (@heapProp_pure_def). Proof. by eexists. Qed.
Definition heapProp_pure := unseal heapProp_pure_aux.
Local Definition heapProp_pure_unseal :
  @heapProp_pure = @heapProp_pure_def := seal_eq heapProp_pure_aux.

Definition heapProp_emp : heapProp := heapProp_pure True.

Local Program Definition heapProp_and_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := P σ ∧ Q σ |}.
Solve Obligations with naive_solver eauto using heapProp_closed.
Local Definition heapProp_and_aux : seal (@heapProp_and_def). Proof. by eexists. Qed.
Definition heapProp_and := unseal heapProp_and_aux.
Local Definition heapProp_and_unseal:
  @heapProp_and = @heapProp_and_def := seal_eq heapProp_and_aux.

Local Program Definition heapProp_or_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := P σ ∨ Q σ |}.
Solve Obligations with naive_solver eauto using heapProp_closed.
Local Definition heapProp_or_aux : seal (@heapProp_or_def). Proof. by eexists. Qed.
Definition heapProp_or := unseal heapProp_or_aux.
Local Definition heapProp_or_unseal:
  @heapProp_or = @heapProp_or_def := seal_eq heapProp_or_aux.

Local Program Definition heapProp_impl_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ σ', σ ⊆ σ' → P σ' → Q σ' |}.
Next Obligation. intros P Q σ1 σ2 HPQ ? σ' ?; simpl in *. apply HPQ. by etrans. Qed.
Local Definition heapProp_impl_aux : seal (@heapProp_impl_def). Proof. by eexists. Qed.
Definition heapProp_impl := unseal heapProp_impl_aux.
Local Definition heapProp_impl_unseal :
  @heapProp_impl = @heapProp_impl_def := seal_eq heapProp_impl_aux.

Local Program Definition heapProp_forall_def {A} (Ψ : A → heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ a, Ψ a σ |}.
Solve Obligations with naive_solver eauto using heapProp_closed.
Local Definition heapProp_forall_aux : seal (@heapProp_forall_def). Proof. by eexists. Qed.
Definition heapProp_forall {A} := unseal heapProp_forall_aux A.
Local Definition heapProp_forall_unseal :
  @heapProp_forall = @heapProp_forall_def := seal_eq heapProp_forall_aux.

Local Program Definition heapProp_exist_def {A} (Ψ : A → heapProp) : heapProp :=
  {| heapProp_holds σ := ∃ a, Ψ a σ |}.
Solve Obligations with naive_solver eauto using heapProp_closed.
Local Definition heapProp_exist_aux : seal (@heapProp_exist_def). Proof. by eexists. Qed.
Definition heapProp_exist {A} := unseal heapProp_exist_aux A.
Local Definition heapProp_exist_unseal :
  @heapProp_exist = @heapProp_exist_def := seal_eq heapProp_exist_aux.

Local Program Definition heapProp_sep_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := ∃ σ1 σ2, σ = σ1 ∪ σ2 ∧ σ1 ##ₘ σ2 ∧ P σ1 ∧ Q σ2 |}.
Next Obligation.
  intros P Q σ1 σ2 (σ11 & σ12 & -> & ? & ? & ?) ?.
  assert (σ11 ⊆ σ2) by (by etrans; [apply map_union_subseteq_l|]).
  exists σ11, (σ2 ∖ σ11). split_and!; [| |done|].
  - by rewrite map_difference_union.
  - by apply map_disjoint_difference_r.
  - eapply heapProp_closed; [done|].
    apply map_union_reflecting_l with σ11; [done|..].
    + by apply map_disjoint_difference_r.
    + by rewrite map_difference_union.
Qed.
Local Definition heapProp_sep_aux : seal (@heapProp_sep_def). Proof. by eexists. Qed.
Definition heapProp_sep := unseal heapProp_sep_aux.
Local Definition heapProp_sep_unseal:
  @heapProp_sep = @heapProp_sep_def := seal_eq heapProp_sep_aux.

Local Program Definition heapProp_wand_def (P Q : heapProp) : heapProp :=
  {| heapProp_holds σ := ∀ σ', σ ##ₘ σ' → P σ' → Q (σ ∪ σ') |}.
Next Obligation.
  intros P Q σ1 σ2 HPQ ? σ' ??; simpl in *.
  apply heapProp_closed with (σ1 ∪ σ'); [by eauto using map_disjoint_weaken_l|].
  by apply map_union_mono_r.
Qed.
Local Definition heapProp_wand_aux : seal (@heapProp_wand_def). Proof. by eexists. Qed.
Definition heapProp_wand := unseal heapProp_wand_aux.
Local Definition heapProp_wand_unseal:
  @heapProp_wand = @heapProp_wand_def := seal_eq heapProp_wand_aux.

Local Definition heapProp_persistently_def (P : heapProp) : heapProp :=
  heapProp_pure (heapProp_entails heapProp_emp P).
Local Definition heapProp_persistently_aux : seal (@heapProp_persistently_def).
Proof. by eexists. Qed.
Definition heapProp_persistently := unseal heapProp_persistently_aux.
Local Definition heapProp_persistently_unseal:
  @heapProp_persistently = @heapProp_persistently_def := seal_eq heapProp_persistently_aux.

(** Iris's [bi] class requires the presence of a later modality, but for non
step-indexed logics, it can be defined as the identity. *)
Definition heapProp_later (P : heapProp) : heapProp := P.

Local Definition heapProp_unseal :=
  (heapProp_pure_unseal, heapProp_and_unseal,
   heapProp_or_unseal, heapProp_impl_unseal, heapProp_forall_unseal,
   heapProp_exist_unseal, heapProp_sep_unseal, heapProp_wand_unseal,
   heapProp_persistently_unseal).
Ltac unseal := rewrite !heapProp_unseal /=.

Section mixins.
  (** Enable [simpl] locally, which is useful for proofs in the model. *)
  Local Arguments heapProp_holds !_ _ /.

  Lemma heapProp_bi_mixin :
    BiMixin
      heapProp_entails heapProp_emp heapProp_pure heapProp_and heapProp_or
      heapProp_impl (@heapProp_forall) (@heapProp_exist)
      heapProp_sep heapProp_wand.
  Proof.
    split.
    - (* [PreOrder heapProp_entails] *)
      split; repeat destruct 1; constructor; naive_solver.
    - (* [P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P)] *)
      intros P Q; split.
      + intros [HPQ]; split; split; naive_solver.
      + intros [[HPQ] [HQP]]; split; naive_solver.
    - (* [Proper (iff ==> dist n) bi_pure] *)
      unseal=> n φ1 φ2 Hφ; split; naive_solver.
    - (* [NonExpansive2 bi_and] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_or] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_impl] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> ? x; by apply HΦ.
    - (* [Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A)] *)
      unseal=> A n Φ1 Φ2 HΦ; split=> σ /=; split=> -[x ?]; exists x; by apply HΦ.
    - (* [NonExpansive2 bi_sep] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [NonExpansive2 bi_wand] *)
      unseal=> n P1 P2 [HP] Q1 Q2 [HQ]; split; naive_solver.
    - (* [φ → P ⊢ ⌜ φ ⌝] *)
      unseal=> φ P ?; by split.
    - (* [(φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P] *)
      unseal=> φ P HP; split=> σ ?. by apply HP.
    - (* [P ∧ Q ⊢ P] *)
      unseal=> P Q; split=> σ [??]; done.
    - (* [P ∧ Q ⊢ Q] *)
      unseal=> P Q; split=> σ [??]; done.
    - (* [(P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R] *)
      unseal=> P Q R [HPQ] [HPR]; split=> σ; split; auto.
    - (* [P ⊢ P ∨ Q] *)
      unseal=> P Q; split=> σ; by left.
    - (* [Q ⊢ P ∨ Q] *)
      unseal=> P Q; split=> σ; by right.
    - (* [(P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R] *)
      unseal=> P Q R [HPQ] [HQR]; split=> σ [?|?]; auto.
    - (* [(P ∧ Q ⊢ R) → P ⊢ Q → R] *)
      unseal=> P Q R HPQR; split=> σ ? σ' ??. apply HPQR.
      split; eauto using heapProp_closed.
    - (* [(P ⊢ Q → R) → P ∧ Q ⊢ R] *)
      unseal=> P Q R HPQR; split=> σ [??]. by eapply HPQR.
    - (* [(∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a] *)
      unseal=> A P Ψ HPΨ; split=> σ ? a. by apply HPΨ.
    - (* [(∀ a, Ψ a) ⊢ Ψ a] *)
      unseal=> A Ψ a; split=> σ ?; done.
    - (* [Ψ a ⊢ ∃ a, Ψ a] *)
      unseal=> A Ψ a; split=> σ ?. by exists a.
    - (* [(∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q] *)
      unseal=> A Φ Q HΦQ; split=> σ [a ?]. by apply (HΦQ a).
    - (* [(P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'] *)
      unseal=> P P' Q Q' [HPQ] [HP'Q']; split; naive_solver.
    - (* [P ⊢ emp ∗ P] *)
      unfold heapProp_emp; unseal=> P; split=> σ ? /=.
      eexists ∅, σ. rewrite left_id_L.
      split_and!; done || apply map_disjoint_empty_l.
    - (* [emp ∗ P ⊢ P] *)
      unfold heapProp_emp; unseal=> P; split; intros ? (?&σ&->&?&_&?).
      eapply heapProp_closed; [done|]. by apply map_union_subseteq_r.
    - (* [P ∗ Q ⊢ Q ∗ P] *)
      unseal=> P Q; split; intros ? (σ1&σ2&->&?&?&?).
      exists σ2, σ1. by rewrite map_union_comm.
    - (* [(P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R)] *)
      unseal=> P Q R; split; intros ? (?&σ3&->&?&(σ1&σ2&->&?&?&?)&?).
      exists σ1, (σ2 ∪ σ3). split_and!; [by rewrite assoc_L|solve_map_disjoint|done|].
      exists σ2, σ3; split_and!; [done|solve_map_disjoint|done..].
    - (* [(P ∗ Q ⊢ R) → P ⊢ Q -∗ R] *)
      unseal=> P Q R [HPQR]; split=> σ1 ? σ2 ??. apply HPQR. by exists σ1, σ2.
    - (* [(P ⊢ Q -∗ R) → P ∗ Q ⊢ R] *)
      unseal=> P Q R [HPQR]; split; intros ? (σ1&σ2&->&?&?&?). by apply HPQR.
  Qed.

  Lemma heapProp_bi_persistently_mixin :
    BiPersistentlyMixin
      heapProp_entails heapProp_emp heapProp_and
      (@heapProp_exist) heapProp_sep heapProp_persistently.
  Proof.
    eapply bi_persistently_mixin_discrete, heapProp_bi_mixin; [done|..].
    - (* The "existential property" [(emp ⊢ ∃ x, Φ x) → ∃ x, emp ⊢ Φ x]. For an
      affine BI the proof relies on there being a smallest resource/the unit
      (here the empty heap [∅]). *)
      unfold heapProp_emp. unseal. intros A Φ [H].
      destruct (H ∅) as [x ?]; [done|]. exists x. split=> σ _.
      eapply heapProp_closed; [done|]. by apply map_empty_subseteq.
    - by rewrite heapProp_persistently_unseal.
  Qed.

  Lemma heapProp_bi_later_mixin :
    BiLaterMixin
      heapProp_entails heapProp_pure heapProp_or heapProp_impl
      (@heapProp_forall) (@heapProp_exist)
      heapProp_sep heapProp_persistently heapProp_later.
  Proof. eapply bi_later_mixin_id; [done|apply heapProp_bi_mixin]. Qed.
End mixins.

Canonical Structure heapPropI : bi :=
  {| bi_ofe_mixin := ofe_mixin_of heapProp;
     bi_bi_mixin := heapProp_bi_mixin;
     bi_bi_persistently_mixin := heapProp_bi_persistently_mixin;
     bi_bi_later_mixin := heapProp_bi_later_mixin |}.

Global Instance heapProp_pure_forall : BiPureForall heapPropI.
Proof. intros A φ. rewrite /bi_forall /bi_pure /=. unseal. by split. Qed.

Global Instance heapProp_affine : BiAffine heapPropI.
Proof. exact: bi.True_intro. Qed.

Lemma heapProp_proofmode_test {A} (P Q Q' R : heapProp) (Φ Ψ : A → heapProp) :
  P ∗ Q ∗ Q' -∗ (* [Q'] is not used, to demonstrate affinity *)
  □ R -∗
  □ (R -∗ ∃ x, Φ x) -∗
  ∃ x, Φ x ∗ Φ x ∗ P ∗ Q.
Proof.
  iIntros "(HP & HQ & HQ') #HR #HRΦ".
  iDestruct ("HRΦ" with "HR") as (x) "#HΦ".
  iExists x. iFrame. by iSplitL.
Qed.
