import LambdaEnv.Syntax

namespace LambdaEnv

open Relation

inductive SigmaStep : Trm V → Trm V → Prop where
  | ass (L M N : Trm V) :
      SigmaStep (.comp (.comp L M) N) (.comp L (.comp M N))
  | idLeft (M : Trm V) :
      SigmaStep (.comp .id M) M
  | idRight (M : Trm V) :
      SigmaStep (.comp M .id) M
  | distExt (L : Trm V) (x : V) (M N : Trm V) :
      SigmaStep (.comp (.ext L x M) N) (.ext (.comp L N) x (.comp M N))
  | varRef (x : V) (M N : Trm V) :
      SigmaStep (.comp (.var x) (.ext M x N)) M
  | varSkip (M : Trm V) (x : V) (N : Trm V) (y : V) :
      x ≠ y → SigmaStep (.comp (.var y) (.ext M x N)) (.comp (.var y) N)
  | distApp (M₁ M₂ N : Trm V) :
      SigmaStep (.comp (.app M₁ M₂) N) (.app (.comp M₁ N) (.comp M₂ N))
  | appLeft (L : Trm V) :
      SigmaStep M N → SigmaStep (.app M L) (.app N L)
  | appRight (L : Trm V) :
      SigmaStep M N → SigmaStep (.app L M) (.app L N)
  | lam (x : V) :
      SigmaStep M N → SigmaStep (.lam x M) (.lam x N)
  | compLeft (L : Trm V) :
      SigmaStep M N → SigmaStep (.comp M L) (.comp N L)
  | compRight (L : Trm V) :
      SigmaStep M N → SigmaStep (.comp L M) (.comp L N)
  | extLeft (x : V) (L : Trm V) :
      SigmaStep M N → SigmaStep (.ext M x L) (.ext N x L)
  | extRight (L : Trm V) (x : V) :
      SigmaStep M N → SigmaStep (.ext L x M) (.ext L x N)

inductive SigmaRootStep : Trm V → Trm V → Prop where
  | ass (L M N : Trm V) :
      SigmaRootStep (.comp (.comp L M) N) (.comp L (.comp M N))
  | idLeft (M : Trm V) :
      SigmaRootStep (.comp .id M) M
  | idRight (M : Trm V) :
      SigmaRootStep (.comp M .id) M
  | distExt (L : Trm V) (x : V) (M N : Trm V) :
      SigmaRootStep (.comp (.ext L x M) N) (.ext (.comp L N) x (.comp M N))
  | varRef (x : V) (M N : Trm V) :
      SigmaRootStep (.comp (.var x) (.ext M x N)) M
  | varSkip (M : Trm V) (x : V) (N : Trm V) (y : V) :
      x ≠ y → SigmaRootStep (.comp (.var y) (.ext M x N)) (.comp (.var y) N)
  | distApp (M₁ M₂ N : Trm V) :
      SigmaRootStep (.comp (.app M₁ M₂) N) (.app (.comp M₁ N) (.comp M₂ N))

theorem SigmaRootStep.toSigmaStep {M N : Trm V} (h : SigmaRootStep M N) :
    SigmaStep M N := by
  induction h with
  | ass L M N => exact SigmaStep.ass L M N
  | idLeft M => exact SigmaStep.idLeft M
  | idRight M => exact SigmaStep.idRight M
  | distExt L x M N => exact SigmaStep.distExt L x M N
  | varRef x M N => exact SigmaStep.varRef x M N
  | varSkip M x N y hne => exact SigmaStep.varSkip M x N y hne
  | distApp M₁ M₂ N => exact SigmaStep.distApp M₁ M₂ N

private theorem ass_length_decrease (l m n : Nat) (hl : 0 < l) (hn : 0 < n) :
    l * (m * (n + 1) + 1) < l * (m + 1) * (n + 1) := by
  have hinner : m * (n + 1) + 1 < (m + 1) * (n + 1) := by
    calc
      m * (n + 1) + 1 < m * (n + 1) + (n + 1) := by omega
      _ = (m + 1) * (n + 1) := by ring
  calc
    l * (m * (n + 1) + 1) < l * ((m + 1) * (n + 1)) :=
      Nat.mul_lt_mul_of_pos_left hinner hl
    _ = l * (m + 1) * (n + 1) := by ring

private theorem dist_length_decrease (a b c : Nat) (hc : 0 < c) :
    a * (c + 1) + b * (c + 1) + 1 < (a + b + 1) * (c + 1) := by
  calc
    a * (c + 1) + b * (c + 1) + 1
        < a * (c + 1) + b * (c + 1) + (c + 1) := by omega
    _ = (a + b + 1) * (c + 1) := by ring

theorem SigmaStep.length_decreases {M N : Trm V} (h : SigmaStep M N) :
    Trm.length N < Trm.length M := by
  induction h with
  | ass L M N =>
      simpa [Trm.length] using
        ass_length_decrease (Trm.length L) (Trm.length M) (Trm.length N)
          (Trm.length_pos L) (Trm.length_pos N)
  | idLeft =>
      simp [Trm.length]
  | idRight M =>
      dsimp [Trm.length]
      nlinarith [Trm.length_pos M]
  | distExt L x M N =>
      simpa [Trm.length] using
        dist_length_decrease (Trm.length L) (Trm.length M) (Trm.length N)
          (Trm.length_pos N)
  | varRef x M N =>
      simp [Trm.length]
      nlinarith [Trm.length_pos N]
  | varSkip M x N y hne =>
      simp [Trm.length]
  | distApp M₁ M₂ N =>
      simpa [Trm.length] using
        dist_length_decrease (Trm.length M₁) (Trm.length M₂) (Trm.length N)
          (Trm.length_pos N)
  | appLeft L h ih =>
      simp [Trm.length]
      omega
  | appRight L h ih =>
      simp [Trm.length]
      omega
  | lam x h ih =>
      simp [Trm.length]
      nlinarith
  | compLeft L h ih =>
      simpa [Trm.length] using
        Nat.mul_lt_mul_of_pos_right ih (Nat.succ_pos (Trm.length L))
  | compRight L h ih =>
      simpa [Trm.length] using
        Nat.mul_lt_mul_of_pos_left (Nat.succ_lt_succ ih) (Trm.length_pos L)
  | extLeft x L h ih =>
      simp [Trm.length]
      omega
  | extRight L x h ih =>
      simp [Trm.length]
      omega

def Terminating (r : α → α → Prop) : Prop :=
  WellFounded fun N M => r M N

theorem SigmaStep.terminating : Terminating (@SigmaStep V) := by
  unfold Terminating
  refine (InvImage.wf Trm.length Nat.lt_wfRel.wf).mono ?_
  intro N M h
  exact SigmaStep.length_decreases h

def SigmaSteps : Trm V → Trm V → Prop :=
  Relation.ReflTransGen SigmaStep

theorem SigmaStep.toSteps {M N : Trm V} (h : SigmaStep M N) :
    SigmaSteps M N :=
  Relation.ReflTransGen.single h

theorem SigmaSteps.app_left {M N L : Trm V} (h : SigmaSteps M N) :
    SigmaSteps (.app M L) (.app N L) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.appLeft L hNP))

theorem SigmaSteps.app_right {M N L : Trm V} (h : SigmaSteps M N) :
    SigmaSteps (.app L M) (.app L N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.appRight L hNP))

theorem SigmaSteps.lam {M N : Trm V} (x : V) (h : SigmaSteps M N) :
    SigmaSteps (.lam x M) (.lam x N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.lam x hNP))

theorem SigmaSteps.comp_left {M N L : Trm V} (h : SigmaSteps M N) :
    SigmaSteps (.comp M L) (.comp N L) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.compLeft L hNP))

theorem SigmaSteps.comp_right {M N L : Trm V} (h : SigmaSteps M N) :
    SigmaSteps (.comp L M) (.comp L N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.compRight L hNP))

theorem SigmaSteps.ext_left {M N L : Trm V} (x : V) (h : SigmaSteps M N) :
    SigmaSteps (.ext M x L) (.ext N x L) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.extLeft x L hNP))

theorem SigmaSteps.ext_right {M N L : Trm V} (x : V) (h : SigmaSteps M N) :
    SigmaSteps (.ext L x M) (.ext L x N) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hMN hNP ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (SigmaStep.extRight L x hNP))

inductive BetaStep : Trm V → Trm V → Prop where
  | beta1 (x : V) (M N L : Trm V) :
      BetaStep (.app (.comp (.lam x M) N) L) (.comp M (.ext L x N))
  | beta2 (x : V) (M N : Trm V) :
      BetaStep (.app (.lam x M) N) (.comp M (.ext N x .id))
  | appLeft (L : Trm V) :
      BetaStep M N → BetaStep (.app M L) (.app N L)
  | appRight (L : Trm V) :
      BetaStep M N → BetaStep (.app L M) (.app L N)
  | lam (x : V) :
      BetaStep M N → BetaStep (.lam x M) (.lam x N)
  | compLeft (L : Trm V) :
      BetaStep M N → BetaStep (.comp M L) (.comp N L)
  | compRight (L : Trm V) :
      BetaStep M N → BetaStep (.comp L M) (.comp L N)
  | extLeft (x : V) (L : Trm V) :
      BetaStep M N → BetaStep (.ext M x L) (.ext N x L)
  | extRight (L : Trm V) (x : V) :
      BetaStep M N → BetaStep (.ext L x M) (.ext L x N)

def BetaSteps : Trm V → Trm V → Prop :=
  Relation.ReflTransGen BetaStep

inductive WeakStep : Trm V → Trm V → Prop where
  | ass (L M N : Trm V) :
      WeakStep (.comp (.comp L M) N) (.comp L (.comp M N))
  | idLeft (M : Trm V) :
      WeakStep (.comp .id M) M
  | idRight (M : Trm V) :
      WeakStep (.comp M .id) M
  | distExt (L : Trm V) (x : V) (M N : Trm V) :
      WeakStep (.comp (.ext L x M) N) (.ext (.comp L N) x (.comp M N))
  | varRef (x : V) (M N : Trm V) :
      WeakStep (.comp (.var x) (.ext M x N)) M
  | varSkip (M : Trm V) (x : V) (N : Trm V) (y : V) :
      x ≠ y → WeakStep (.comp (.var y) (.ext M x N)) (.comp (.var y) N)
  | distApp (M₁ M₂ N : Trm V) :
      WeakStep (.comp (.app M₁ M₂) N) (.app (.comp M₁ N) (.comp M₂ N))
  | beta1 (x : V) (M N L : Trm V) :
      WeakStep (.app (.comp (.lam x M) N) L) (.comp M (.ext L x N))
  | beta2 (x : V) (M N : Trm V) :
      WeakStep (.app (.lam x M) N) (.comp M (.ext N x .id))
  | appLeft (L : Trm V) :
      WeakStep M N → WeakStep (.app M L) (.app N L)
  | appRight (L : Trm V) :
      WeakStep M N → WeakStep (.app L M) (.app L N)
  | lam (x : V) :
      WeakStep M N → WeakStep (.lam x M) (.lam x N)
  | compLeft (L : Trm V) :
      WeakStep M N → WeakStep (.comp M L) (.comp N L)
  | compRight (L : Trm V) :
      WeakStep M N → WeakStep (.comp L M) (.comp L N)
  | extLeft (x : V) (L : Trm V) :
      WeakStep M N → WeakStep (.ext M x L) (.ext N x L)
  | extRight (L : Trm V) (x : V) :
      WeakStep M N → WeakStep (.ext L x M) (.ext L x N)

def WeakSteps : Trm V → Trm V → Prop :=
  Relation.ReflTransGen WeakStep

theorem SigmaStep.toWeakStep {M N : Trm V} (h : SigmaStep M N) :
    WeakStep M N := by
  induction h with
  | ass L M N => exact WeakStep.ass L M N
  | idLeft M => exact WeakStep.idLeft M
  | idRight M => exact WeakStep.idRight M
  | distExt L x M N => exact WeakStep.distExt L x M N
  | varRef x M N => exact WeakStep.varRef x M N
  | varSkip M x N y hne => exact WeakStep.varSkip M x N y hne
  | distApp M₁ M₂ N => exact WeakStep.distApp M₁ M₂ N
  | appLeft L h ih => exact WeakStep.appLeft L ih
  | appRight L h ih => exact WeakStep.appRight L ih
  | lam x h ih => exact WeakStep.lam x ih
  | compLeft L h ih => exact WeakStep.compLeft L ih
  | compRight L h ih => exact WeakStep.compRight L ih
  | extLeft x L h ih => exact WeakStep.extLeft x L ih
  | extRight L x h ih => exact WeakStep.extRight L x ih

theorem BetaStep.toWeakStep {M N : Trm V} (h : BetaStep M N) :
    WeakStep M N := by
  induction h with
  | beta1 x M N L => exact WeakStep.beta1 x M N L
  | beta2 x M N => exact WeakStep.beta2 x M N
  | appLeft L h ih => exact WeakStep.appLeft L ih
  | appRight L h ih => exact WeakStep.appRight L ih
  | lam x h ih => exact WeakStep.lam x ih
  | compLeft L h ih => exact WeakStep.compLeft L ih
  | compRight L h ih => exact WeakStep.compRight L ih
  | extLeft x L h ih => exact WeakStep.extLeft x L ih
  | extRight L x h ih => exact WeakStep.extRight L x ih

theorem WeakStep.sigma_or_beta {M N : Trm V} (h : WeakStep M N) :
    SigmaStep M N ∨ BetaStep M N := by
  induction h with
  | ass L M N => exact Or.inl (SigmaStep.ass L M N)
  | idLeft M => exact Or.inl (SigmaStep.idLeft M)
  | idRight M => exact Or.inl (SigmaStep.idRight M)
  | distExt L x M N => exact Or.inl (SigmaStep.distExt L x M N)
  | varRef x M N => exact Or.inl (SigmaStep.varRef x M N)
  | varSkip M x N y hne => exact Or.inl (SigmaStep.varSkip M x N y hne)
  | distApp M₁ M₂ N => exact Or.inl (SigmaStep.distApp M₁ M₂ N)
  | beta1 x M N L => exact Or.inr (BetaStep.beta1 x M N L)
  | beta2 x M N => exact Or.inr (BetaStep.beta2 x M N)
  | appLeft L h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.appLeft L hs))
        (fun hb => Or.inr (BetaStep.appLeft L hb))
  | appRight L h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.appRight L hs))
        (fun hb => Or.inr (BetaStep.appRight L hb))
  | lam x h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.lam x hs))
        (fun hb => Or.inr (BetaStep.lam x hb))
  | compLeft L h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.compLeft L hs))
        (fun hb => Or.inr (BetaStep.compLeft L hb))
  | compRight L h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.compRight L hs))
        (fun hb => Or.inr (BetaStep.compRight L hb))
  | extLeft x L h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.extLeft x L hs))
        (fun hb => Or.inr (BetaStep.extLeft x L hb))
  | extRight L x h ih =>
      exact ih.elim (fun hs => Or.inl (SigmaStep.extRight L x hs))
        (fun hb => Or.inr (BetaStep.extRight L x hb))

theorem SigmaSteps.toWeakSteps {M N : Trm V} (h : SigmaSteps M N) :
    WeakSteps M N :=
  (Relation.ReflTransGen.mono (r := SigmaStep) (p := WeakStep)
    (fun _ _ hs => SigmaStep.toWeakStep hs)) M N h

theorem BetaSteps.toWeakSteps {M N : Trm V} (h : BetaSteps M N) :
    WeakSteps M N :=
  (Relation.ReflTransGen.mono (r := BetaStep) (p := WeakStep)
    (fun _ _ hb => BetaStep.toWeakStep hb)) M N h

end LambdaEnv
