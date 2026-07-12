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

theorem SigmaSteps.refl (M : Trm V) : SigmaSteps M M :=
  Relation.ReflTransGen.refl

theorem SigmaSteps.trans {M N L : Trm V} (hMN : SigmaSteps M N) (hNL : SigmaSteps N L) :
    SigmaSteps M L :=
  Relation.ReflTransGen.trans hMN hNL

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

theorem SigmaSteps.comp_idRight_in_compRight (L M : Trm V) :
    SigmaSteps (.comp L (.comp M .id)) (.comp L M) :=
  SigmaStep.toSteps (SigmaStep.compRight L (SigmaStep.idRight M))

theorem SigmaSteps.ext_comp_idRight (L M : Trm V) (x : V) :
    SigmaSteps (.ext (.comp L .id) x (.comp M .id)) (.ext L x M) := by
  exact SigmaSteps.trans
    (SigmaStep.toSteps (SigmaStep.extLeft x (.comp M .id) (SigmaStep.idRight L)))
    (SigmaStep.toSteps (SigmaStep.extRight L x (SigmaStep.idRight M)))

theorem SigmaSteps.app_comp_idRight (M₁ M₂ : Trm V) :
    SigmaSteps (.app (.comp M₁ .id) (.comp M₂ .id)) (.app M₁ M₂) := by
  exact SigmaSteps.trans
    (SigmaStep.toSteps (SigmaStep.appLeft (.comp M₂ .id) (SigmaStep.idRight M₁)))
    (SigmaStep.toSteps (SigmaStep.appRight M₁ (SigmaStep.idRight M₂)))

def Joinable (r : α → α → Prop) (M N : α) : Prop :=
  ∃ L, Relation.ReflTransGen r M L ∧ Relation.ReflTransGen r N L

namespace Joinable

theorem intro {r : α → α → Prop} {M N L : α}
    (hM : Relation.ReflTransGen r M L) (hN : Relation.ReflTransGen r N L) :
    Joinable r M N :=
  ⟨L, hM, hN⟩

theorem refl {r : α → α → Prop} (M : α) : Joinable r M M :=
  ⟨M, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem symm {r : α → α → Prop} {M N : α} (h : Joinable r M N) :
    Joinable r N M := by
  rcases h with ⟨L, hM, hN⟩
  exact ⟨L, hN, hM⟩

end Joinable

def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ M N₁ N₂, r M N₁ → r M N₂ → Joinable r N₁ N₂

theorem locallyConfluent_of_local_peaks
    (h : ∀ M N₁ N₂, SigmaStep (V := V) M N₁ → SigmaStep M N₂ →
      Joinable SigmaStep N₁ N₂) :
    LocallyConfluent (@SigmaStep V) := by
  intro M N₁ N₂ h₁ h₂
  exact h M N₁ N₂ h₁ h₂

theorem SigmaJoin.steps {M N L : Trm V} (hM : SigmaSteps M L) (hN : SigmaSteps N L) :
    Joinable SigmaStep M N :=
  Joinable.intro hM hN

theorem SigmaJoin.refl (M : Trm V) : Joinable SigmaStep M M :=
  Joinable.refl M

theorem SigmaJoin.symm {M N : Trm V} (h : Joinable SigmaStep M N) :
    Joinable SigmaStep N M :=
  Joinable.symm h

theorem SigmaJoin.step_left {M N : Trm V} (h : SigmaStep M N) :
    Joinable SigmaStep M N :=
  SigmaJoin.steps (SigmaStep.toSteps h) (SigmaSteps.refl N)

theorem SigmaJoin.step_right {M N : Trm V} (h : SigmaStep N M) :
    Joinable SigmaStep M N :=
  SigmaJoin.symm (SigmaJoin.step_left h)

theorem SigmaStep.no_id {P : Prop} {N : Trm V} (h : SigmaStep .id N) : P := by
  cases h

theorem SigmaStep.no_var {P : Prop} {x : V} {N : Trm V} (h : SigmaStep (.var x) N) : P := by
  cases h

theorem SigmaStep.ext_cases {M : Trm V} {x : V} {N P : Trm V}
    (h : SigmaStep (.ext M x N) P) :
    (∃ M', SigmaStep M M' ∧ P = .ext M' x N) ∨
      (∃ N', SigmaStep N N' ∧ P = .ext M x N') := by
  cases h with
  | extLeft _ _ hM =>
      exact Or.inl ⟨_, hM, rfl⟩
  | extRight _ _ hN =>
      exact Or.inr ⟨_, hN, rfl⟩

theorem SigmaJoin.app_left {M N L : Trm V} (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.app M L) (.app N L) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.app_left hM) (SigmaSteps.app_left hN)

theorem SigmaJoin.app_right {M N L : Trm V} (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.app L M) (.app L N) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.app_right hM) (SigmaSteps.app_right hN)

theorem SigmaJoin.lam {M N : Trm V} (x : V) (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.lam x M) (.lam x N) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.lam x hM) (SigmaSteps.lam x hN)

theorem SigmaJoin.comp_left {M N L : Trm V} (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.comp M L) (.comp N L) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.comp_left hM) (SigmaSteps.comp_left hN)

theorem SigmaJoin.comp_right {M N L : Trm V} (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.comp L M) (.comp L N) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.comp_right hM) (SigmaSteps.comp_right hN)

theorem SigmaJoin.ext_left {M N L : Trm V} (x : V) (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.ext M x L) (.ext N x L) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.ext_left x hM) (SigmaSteps.ext_left x hN)

theorem SigmaJoin.ext_right {M N L : Trm V} (x : V) (h : Joinable SigmaStep M N) :
    Joinable SigmaStep (.ext L x M) (.ext L x N) := by
  rcases h with ⟨P, hM, hN⟩
  exact SigmaJoin.steps (SigmaSteps.ext_right x hM) (SigmaSteps.ext_right x hN)

theorem SigmaLocalPeak.app_left_right {M M' N N' : Trm V}
    (left : SigmaStep M M') (right : SigmaStep N N') :
    Joinable SigmaStep (.app M' N) (.app M N') := by
  exact SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.appRight M' right))
    (SigmaStep.toSteps (SigmaStep.appLeft N' left))

theorem SigmaLocalPeak.comp_left_right {M M' N N' : Trm V}
    (left : SigmaStep M M') (right : SigmaStep N N') :
    Joinable SigmaStep (.comp M' N) (.comp M N') := by
  exact SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.compRight M' right))
    (SigmaStep.toSteps (SigmaStep.compLeft N' left))

theorem SigmaLocalPeak.ext_left_right {M M' N N' : Trm V} (x : V)
    (left : SigmaStep M M') (right : SigmaStep N N') :
    Joinable SigmaStep (.ext M' x N) (.ext M x N') := by
  exact SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.extRight M' x right))
    (SigmaStep.toSteps (SigmaStep.extLeft x N' left))

theorem SigmaRootStep.local_peak_joinable {M N₁ N₂ : Trm V}
    (left : SigmaRootStep M N₁) (right : SigmaRootStep M N₂) :
    Joinable SigmaStep N₁ N₂ := by
  cases left <;> cases right <;> first
    | exact SigmaJoin.refl _
    | exact SigmaJoin.steps (SigmaSteps.comp_idRight_in_compRight _ _) (SigmaSteps.refl _)
    | exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.comp_idRight_in_compRight _ _)
    | exact SigmaJoin.steps (SigmaSteps.ext_comp_idRight _ _ _) (SigmaSteps.refl _)
    | exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.ext_comp_idRight _ _ _)
    | exact SigmaJoin.steps (SigmaSteps.app_comp_idRight _ _) (SigmaSteps.refl _)
    | exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.app_comp_idRight _ _)
    | aesop (add safe
        [SigmaJoin.step_left, SigmaJoin.step_right, SigmaStep.ass, SigmaStep.idLeft,
          SigmaStep.idRight, SigmaStep.distExt, SigmaStep.varRef, SigmaStep.varSkip,
          SigmaStep.distApp])

theorem SigmaLocalPeak.id {N₁ N₂ : Trm V}
    (left : SigmaStep (.id : Trm V) N₁) (_right : SigmaStep .id N₂) :
    Joinable SigmaStep N₁ N₂ :=
  SigmaStep.no_id left

theorem SigmaLocalPeak.var {x : V} {N₁ N₂ : Trm V}
    (left : SigmaStep (.var x) N₁) (_right : SigmaStep (.var x) N₂) :
    Joinable SigmaStep N₁ N₂ :=
  SigmaStep.no_var left

theorem SigmaLocalPeak.lam {x : V} {M N₁ N₂ : Trm V}
    (bodyPeak : ∀ {P Q : Trm V}, SigmaStep M P → SigmaStep M Q → Joinable SigmaStep P Q)
    (left : SigmaStep (.lam x M) N₁) (right : SigmaStep (.lam x M) N₂) :
    Joinable SigmaStep N₁ N₂ := by
  cases left with
  | lam _ leftBody =>
      cases right with
      | lam _ rightBody =>
          exact SigmaJoin.lam x (bodyPeak leftBody rightBody)

theorem SigmaLocalPeak.app {M N U W : Trm V}
    (leftPeak : ∀ {P Q : Trm V}, SigmaStep M P → SigmaStep M Q → Joinable SigmaStep P Q)
    (rightPeak : ∀ {P Q : Trm V}, SigmaStep N P → SigmaStep N Q → Joinable SigmaStep P Q)
    (left : SigmaStep (.app M N) U) (right : SigmaStep (.app M N) W) :
    Joinable SigmaStep U W := by
  cases left with
  | appLeft _ leftApp =>
      cases right with
      | appLeft _ rightApp =>
          exact SigmaJoin.app_left (leftPeak leftApp rightApp)
      | appRight _ rightApp =>
          exact SigmaLocalPeak.app_left_right leftApp rightApp
  | appRight _ leftApp =>
      cases right with
      | appLeft _ rightApp =>
          exact SigmaJoin.symm (SigmaLocalPeak.app_left_right rightApp leftApp)
      | appRight _ rightApp =>
          exact SigmaJoin.app_right (rightPeak leftApp rightApp)

theorem SigmaLocalPeak.ext {M N U W : Trm V} {x : V}
    (leftPeak : ∀ {P Q : Trm V}, SigmaStep M P → SigmaStep M Q → Joinable SigmaStep P Q)
    (rightPeak : ∀ {P Q : Trm V}, SigmaStep N P → SigmaStep N Q → Joinable SigmaStep P Q)
    (left : SigmaStep (.ext M x N) U) (right : SigmaStep (.ext M x N) W) :
    Joinable SigmaStep U W := by
  cases left with
  | extLeft _ _ leftExt =>
      cases right with
      | extLeft _ _ rightExt =>
          exact SigmaJoin.ext_left x (leftPeak leftExt rightExt)
      | extRight _ _ rightExt =>
          exact SigmaLocalPeak.ext_left_right x leftExt rightExt
  | extRight _ _ leftExt =>
      cases right with
      | extLeft _ _ rightExt =>
          exact SigmaJoin.symm (SigmaLocalPeak.ext_left_right x rightExt leftExt)
      | extRight _ _ rightExt =>
          exact SigmaJoin.ext_right x (rightPeak leftExt rightExt)

theorem SigmaLocalPeak.ass_left {L L' M N : Trm V} (h : SigmaStep L L') :
    Joinable SigmaStep (.comp L (.comp M N)) (.comp (.comp L' M) N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.compLeft (.comp M N) h))
    (SigmaStep.toSteps (SigmaStep.ass L' M N))

theorem SigmaLocalPeak.ass_mid {L M M' N : Trm V} (h : SigmaStep M M') :
    Joinable SigmaStep (.comp L (.comp M N)) (.comp (.comp L M') N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.compRight L (SigmaStep.compLeft N h)))
    (SigmaStep.toSteps (SigmaStep.ass L M' N))

theorem SigmaLocalPeak.ass_right {L M N N' : Trm V} (h : SigmaStep N N') :
    Joinable SigmaStep (.comp L (.comp M N)) (.comp (.comp L M) N') :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.compRight L (SigmaStep.compRight M h)))
    (SigmaStep.toSteps (SigmaStep.ass L M N'))

theorem SigmaLocalPeak.idLeft_arg {M M' : Trm V} (h : SigmaStep M M') :
    Joinable SigmaStep M (.comp .id M') :=
  SigmaJoin.steps (SigmaStep.toSteps h)
    (SigmaStep.toSteps (SigmaStep.idLeft M'))

theorem SigmaLocalPeak.idRight_arg {M M' : Trm V} (h : SigmaStep M M') :
    Joinable SigmaStep M (.comp M' .id) :=
  SigmaJoin.steps (SigmaStep.toSteps h)
    (SigmaStep.toSteps (SigmaStep.idRight M'))

theorem SigmaLocalPeak.distExt_left {L L' M N : Trm V} {x : V}
    (h : SigmaStep L L') :
    Joinable SigmaStep
      (.ext (.comp L N) x (.comp M N))
      (.comp (.ext L' x M) N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.extLeft x (.comp M N) (SigmaStep.compLeft N h)))
    (SigmaStep.toSteps (SigmaStep.distExt L' x M N))

theorem SigmaLocalPeak.distExt_mid {L M M' N : Trm V} {x : V}
    (h : SigmaStep M M') :
    Joinable SigmaStep
      (.ext (.comp L N) x (.comp M N))
      (.comp (.ext L x M') N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.extRight (.comp L N) x (SigmaStep.compLeft N h)))
    (SigmaStep.toSteps (SigmaStep.distExt L x M' N))

theorem SigmaLocalPeak.distExt_right {L M N N' : Trm V} {x : V}
    (h : SigmaStep N N') :
    Joinable SigmaStep
      (.ext (.comp L N) x (.comp M N))
      (.comp (.ext L x M) N') := by
  exact SigmaJoin.steps
    (SigmaSteps.trans
      (SigmaStep.toSteps
        (SigmaStep.extLeft x (.comp M N) (SigmaStep.compRight L h)))
      (SigmaStep.toSteps
        (SigmaStep.extRight (.comp L N') x (SigmaStep.compRight M h))))
    (SigmaStep.toSteps (SigmaStep.distExt L x M N'))

theorem SigmaLocalPeak.varRef_left {x : V} {M M' N : Trm V}
    (h : SigmaStep M M') :
    Joinable SigmaStep M (.comp (.var x) (.ext M' x N)) :=
  SigmaJoin.steps (SigmaStep.toSteps h)
    (SigmaStep.toSteps (SigmaStep.varRef x M' N))

theorem SigmaLocalPeak.varRef_right {x : V} {M N N' : Trm V}
    (_h : SigmaStep N N') :
    Joinable SigmaStep M (.comp (.var x) (.ext M x N')) :=
  SigmaJoin.steps (SigmaSteps.refl M)
    (SigmaStep.toSteps (SigmaStep.varRef x M N'))

theorem SigmaLocalPeak.varSkip_left {x y : V} {M M' N : Trm V}
    (hne : x ≠ y) (_h : SigmaStep M M') :
    Joinable SigmaStep (.comp (.var y) N) (.comp (.var y) (.ext M' x N)) :=
  SigmaJoin.steps (SigmaSteps.refl (.comp (.var y) N))
    (SigmaStep.toSteps (SigmaStep.varSkip M' x N y hne))

theorem SigmaLocalPeak.varSkip_right {x y : V} {M N N' : Trm V}
    (hne : x ≠ y) (h : SigmaStep N N') :
    Joinable SigmaStep (.comp (.var y) N) (.comp (.var y) (.ext M x N')) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.compRight (.var y) h))
    (SigmaStep.toSteps (SigmaStep.varSkip M x N' y hne))

theorem SigmaLocalPeak.distApp_left {M₁ M₁' M₂ N : Trm V}
    (h : SigmaStep M₁ M₁') :
    Joinable SigmaStep
      (.app (.comp M₁ N) (.comp M₂ N))
      (.comp (.app M₁' M₂) N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.appLeft (.comp M₂ N) (SigmaStep.compLeft N h)))
    (SigmaStep.toSteps (SigmaStep.distApp M₁' M₂ N))

theorem SigmaLocalPeak.distApp_mid {M₁ M₂ M₂' N : Trm V}
    (h : SigmaStep M₂ M₂') :
    Joinable SigmaStep
      (.app (.comp M₁ N) (.comp M₂ N))
      (.comp (.app M₁ M₂') N) :=
  SigmaJoin.steps
    (SigmaStep.toSteps (SigmaStep.appRight (.comp M₁ N) (SigmaStep.compLeft N h)))
    (SigmaStep.toSteps (SigmaStep.distApp M₁ M₂' N))

theorem SigmaLocalPeak.distApp_right {M₁ M₂ N N' : Trm V}
    (h : SigmaStep N N') :
    Joinable SigmaStep
      (.app (.comp M₁ N) (.comp M₂ N))
      (.comp (.app M₁ M₂) N') := by
  exact SigmaJoin.steps
    (SigmaSteps.trans
      (SigmaStep.toSteps
        (SigmaStep.appLeft (.comp M₂ N) (SigmaStep.compRight M₁ h)))
      (SigmaStep.toSteps
        (SigmaStep.appRight (.comp M₁ N') (SigmaStep.compRight M₂ h))))
    (SigmaStep.toSteps (SigmaStep.distApp M₁ M₂ N'))

theorem SigmaLocalPeak.varRef_inner {x : V} {M N MN : Trm V}
    (h : SigmaStep (.ext M x N) MN) :
    Joinable SigmaStep M (.comp (.var x) MN) := by
  cases SigmaStep.ext_cases h with
  | inl hleft =>
      rcases hleft with ⟨M', hM, rfl⟩
      exact SigmaLocalPeak.varRef_left hM
  | inr hright =>
      rcases hright with ⟨N', hN, rfl⟩
      exact SigmaLocalPeak.varRef_right hN

theorem SigmaLocalPeak.varSkip_inner {x y : V} {M N MN : Trm V}
    (hne : x ≠ y) (h : SigmaStep (.ext M x N) MN) :
    Joinable SigmaStep (.comp (.var y) N) (.comp (.var y) MN) := by
  cases SigmaStep.ext_cases h with
  | inl hleft =>
      rcases hleft with ⟨M', hM, rfl⟩
      exact SigmaLocalPeak.varSkip_left hne hM
  | inr hright =>
      rcases hright with ⟨N', hN, rfl⟩
      exact SigmaLocalPeak.varSkip_right hne hN

theorem SigmaLocalPeak.idLeft {M P : Trm V}
    (step : SigmaStep (.comp .id M) P) :
    Joinable SigmaStep M P := by
  cases step with
  | idLeft _ => exact SigmaJoin.refl _
  | idRight _ => exact SigmaJoin.refl _
  | compLeft _ h => exact SigmaStep.no_id h
  | compRight _ h => exact SigmaLocalPeak.idLeft_arg h

theorem SigmaLocalPeak.idRight {M P : Trm V}
    (step : SigmaStep (.comp M .id) P) :
    Joinable SigmaStep M P := by
  cases step with
  | ass L M N =>
      exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.comp_idRight_in_compRight L M)
  | idLeft _ => exact SigmaJoin.refl _
  | idRight _ => exact SigmaJoin.refl _
  | distExt L x M N =>
      exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.ext_comp_idRight L M x)
  | distApp M₁ M₂ N =>
      exact SigmaJoin.steps (SigmaSteps.refl _) (SigmaSteps.app_comp_idRight M₁ M₂)
  | compLeft _ h => exact SigmaLocalPeak.idRight_arg h
  | compRight _ h => exact SigmaStep.no_id h

theorem SigmaLocalPeak.varRef {x : V} {M N P : Trm V}
    (step : SigmaStep (.comp (.var x) (.ext M x N)) P) :
    Joinable SigmaStep M P := by
  cases step with
  | varRef _ _ _ => exact SigmaJoin.refl _
  | varSkip _ _ _ _ hne => contradiction
  | compLeft _ h => exact SigmaStep.no_var h
  | compRight _ h => exact SigmaLocalPeak.varRef_inner h

theorem SigmaLocalPeak.varSkip {x y : V} {M N P : Trm V}
    (hne : x ≠ y) (step : SigmaStep (.comp (.var y) (.ext M x N)) P) :
    Joinable SigmaStep (.comp (.var y) N) P := by
  cases step with
  | varRef _ _ _ => contradiction
  | varSkip _ _ _ _ _ => exact SigmaJoin.refl _
  | compLeft _ h => exact SigmaStep.no_var h
  | compRight _ h => exact SigmaLocalPeak.varSkip_inner hne h

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
