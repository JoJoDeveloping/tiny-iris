From stdpp Require Export strings ssreflect.
From stdpp Require Import gmap options.

Section lang.

  Definition loc := nat.

  Inductive op := Add | Sub | Mul | Eq | Le.

  Inductive expr := 
    Lam (x : string) (e : expr)
  | App (e1 : expr) (e2 : expr)
  | Var (x : string)
  | Num (z : Z)
  | Op (e1 : expr) (op : op) (e2 : expr)
  | If (e1 e2 e3 : expr)
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
  | OpLCtx (K : ectx) (op : op) (e2 : val)
  | OpRCtx (e1 : expr) (op : op) (K : ectx)
  | IfCtx (K : ectx) (e2 e3 : expr)
  | NewCtx (K : ectx) 
  | LoadCtx (K : ectx) 
  | StoreLCtx (K : ectx) (e2 : val)
  | StoreRCtx (e1 : expr) (K : ectx).

  Fixpoint fill (K : ectx) (e : expr) : expr := match K with
    EmptyCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | OpLCtx K op v2 => Op (fill K e) op (of_val v2)
  | OpRCtx e1 op K => Op e1 op (fill K e)
  | IfCtx K e2 e3 => If (fill K e) e2 e3
  | NewCtx K => New (fill K e)
  | LoadCtx K => Load (fill K e)
  | StoreLCtx K v2 => Store (fill K e) (of_val v2)
  | StoreRCtx e1 K => Store e1 (fill K e) end.

  Fixpoint ectx_comp (K1 K2 : ectx) : ectx := match K1 with
    EmptyCtx => K2
  | AppLCtx K v2 => AppLCtx (ectx_comp K K2) v2
  | AppRCtx e1 K => AppRCtx e1 (ectx_comp K K2)
  | OpLCtx K op v2 => OpLCtx (ectx_comp K K2) op v2
  | OpRCtx e1 op K => OpRCtx e1 op (ectx_comp K K2)
  | IfCtx K e2 e3 => IfCtx (ectx_comp K K2) e2 e3
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
  | Op e1 op e2 => Op (subst e1 x e') op (subst e2 x e')
  | If e1 e2 e3 => If (subst e1 x e') (subst e2 x e') (subst e3 x e')
  | New e => New (subst e x e')
  | Load e => Load (subst e x e')
  | Store e1 e2 => Store (subst e1 x e') (subst e2 x e')
  | Loc n => Loc n end.

  Definition eval_op (n1 : Z) (op : op) (n2 : Z) : Z := match op with
    Add => n1 + n2
  | Sub => n1 - n2
  | Mul => n1 * n2
  | Eq => if bool_decide (n1 = n2) then 1 else 0
  | Le => if bool_decide (n1 ≤ n2) then 1 else 0 end%Z.

  Definition state := (gmap nat val).

  Inductive base_step : expr → state → expr → state → Prop :=
    BetaS x e v h : base_step (App (Lam x e) (of_val v)) h (subst e x (of_val v)) h
  | OpS n1 op n2 h : base_step (Op (Num n1) op (Num n2)) h (Num (eval_op n1 op n2)) h
  | IfTrueS n e2 e3 h : n ≠ 0%Z → base_step (If (Num n) e2 e3) h e2 h
  | IfFalseS e2 e3 h : base_step (If (Num 0%Z) e2 e3) h e3 h
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