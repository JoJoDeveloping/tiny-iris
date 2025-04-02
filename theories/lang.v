From stdpp Require Export strings ssreflect.
From stdpp Require Import gmap options.

Section lang.

  Definition loc := nat.

  Inductive expr := 
    Lam (x : string) (e : expr)
  | App (e1 : expr) (e2 : expr)
  | Var (x : string)
  | Num (z : Z)
  | Add (e1 e2 : expr)
  | New (e : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr)
  | Loc (n : loc).

  Inductive val :=
    LamV (x : string) (e : expr)
  | NumV (z : Z)
  | LocV (n : loc).

  Definition of_val (v : val) : expr := match v with
    LamV x e => Lam x e
  | NumV n => Num n
  | LocV l => Loc l end.

  Definition to_val (e : expr) : option val := match e with
    Lam x e => Some $ LamV x e
  | Num n => Some $ NumV n
  | Loc l => Some $ LocV l
  | _ => None end.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by destruct v. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. destruct e=>//=; by intros [= <-]. Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. intros [] []; simpl; congruence. Qed.

  Inductive ectx :=
  | EmptyCtx
  | AppLCtx (K : ectx) (e2 : val)
  | AppRCtx (e1 : expr) (K : ectx)
  | AddLCtx (K : ectx) (e2 : val)
  | AddRCtx (e1 : expr) (K : ectx)
  | NewCtx (K : ectx) 
  | LoadCtx (K : ectx) 
  | StoreLCtx (K : ectx) (e2 : val)
  | StoreRCtx (e1 : expr) (K : ectx).

  Fixpoint fill (K : ectx) (e : expr) : expr := match K with
    EmptyCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | AddLCtx K v2 => Add (fill K e) (of_val v2)
  | AddRCtx e1 K => Add e1 (fill K e)
  | NewCtx K => New (fill K e)
  | LoadCtx K => Load (fill K e)
  | StoreLCtx K v2 => Store (fill K e) (of_val v2)
  | StoreRCtx e1 K => Store e1 (fill K e) end.

  Fixpoint ectx_comp (K1 K2 : ectx) : ectx := match K1 with
    EmptyCtx => K2
  | AppLCtx K v2 => AppLCtx (ectx_comp K K2) v2
  | AppRCtx e1 K => AppRCtx e1 (ectx_comp K K2)
  | AddLCtx K v2 => AddLCtx (ectx_comp K K2) v2
  | AddRCtx e1 K => AddRCtx e1 (ectx_comp K K2)
  | NewCtx K => NewCtx (ectx_comp K K2)
  | LoadCtx K => LoadCtx (ectx_comp K K2)
  | StoreLCtx K v2 => StoreLCtx (ectx_comp K K2) v2
  | StoreRCtx e1 K => StoreRCtx e1 (ectx_comp K K2) end.

  Lemma fill_comp K1 K2 e :
    fill K1 (fill K2 e) = fill (ectx_comp K1 K2) e.
  Proof. induction K1; simpl; by f_equal. Qed.

  Fixpoint subst (e : expr) (x : string) (e' : expr) : expr := match e with 
  | Lam y e => if decide (x = y) then Lam y e else Lam y (subst e x e')
  | App e1 e2 => App (subst e1 x e') (subst e2 x e')
  | Var y => if decide (x = y) then e' else Var y
  | Num z => Num z
  | Add e1 e2 => Add (subst e1 x e') (subst e2 x e')
  | New e => New (subst e x e')
  | Load e => Load (subst e x e')
  | Store e1 e2 => Store (subst e1 x e') (subst e2 x e')
  | Loc n => Loc n end.

  Definition state := (gmap nat val).

  Inductive base_step : expr → state → expr → state → Prop :=
    BetaS x e v h : base_step (App (Lam x e) (of_val v)) h (subst e x (of_val v)) h
  | PlusS n1 n2 h : base_step (Add (Num n1) (Num n2)) h (Num (n1 + n2)) h
  | NewS l v h : l ∉ dom h → base_step (New (of_val v)) h (Loc l) (<[ l := v ]> h)
  | LoadS l v h : h !! l = Some v → base_step (Load (Loc l)) h (of_val v) h
  | StoreS l v v' h : h !! l = Some v' → base_step (Store (Loc l) (of_val v)) h (of_val v') (<[ l := v]> h).

  Inductive ctx_step : expr → state → expr → state → Prop :=
    Ctx K e1 h1 e2 h2 : base_step e1 h1 e2 h2 → ctx_step (fill K e1) h1 (fill K e2) h2.

  Lemma ctx_step_fill K e1 h1 e2 h2 : ctx_step e1 h1 e2 h2 → ctx_step (fill K e1) h1 (fill K e2) h2.
  Proof.
    intros [K' e1' h1' e2' h2' HH].
    rewrite !fill_comp. econstructor. done.
  Qed.

  Lemma ctx_step_base_step e1 h1 e2 h2 : base_step e1 h1 e2 h2 → ctx_step e1 h1 e2 h2.
  Proof.
    eapply (Ctx EmptyCtx).
  Qed.

  Definition ctx_steps e1 h1 e2 h2 := rtc (λ p1 p2, ctx_step (fst p1) (snd p1) (fst p2) (snd p2)) (e1, h1) (e2, h2).

  Definition pure_step e e' := ∀ h, ctx_step e h e' h.

End lang.