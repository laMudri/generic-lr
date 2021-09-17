{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

module Generic.Linear.Example.LnL where

  open import Data.Hand
  open import Data.LTree
  open import Data.LTree.Automation
  open import Data.LTree.Vector
  open import Data.Product
  open import Data.Unit
  open import Level using (Level; Lift)
  open import Proposition
  open import Relation.Binary.PropositionalEquality
  open import Relation.Unary
  open import Relation.Unary.Bunched
  open import Size

  open import Generic.Linear.Example.ZeroOneMany renaming (u01ω to Ann)

  data Frag : Set where
    lin int : Frag

  infixr 5 _t⊗_ _t⊸_ _t×_ _t→_

  data Ty : Frag → Set where
    ι : Ty lin
    tI : Ty lin
    _t⊗_ : (A B : Ty lin) → Ty lin
    _t⊸_ : (A B : Ty lin) → Ty lin
    tF : Ty int → Ty lin

    t1 : Ty int
    _t×_ : (X Y : Ty int) → Ty int
    _t→_ : (X Y : Ty int) → Ty int
    tG : Ty lin → Ty int

  ΣTy : Set
  ΣTy = ∃ Ty

  t! : Ty lin → Ty lin
  t! A = tF (tG A)

  open import Generic.Linear.Syntax ΣTy Ann public

  open import Generic.Linear.Syntax.Term ΣTy rawPoSemiring public
  open import Generic.Linear.Syntax.Interpretation ΣTy rawPoSemiring public
  open import Generic.Linear.Renaming ΣTy poSemiring public

  data `LnL : Set where
    `Ii : `LnL
    `Ie : (C : Ty lin) → `LnL
    `⊗i : (A B : Ty lin) → `LnL
    `⊗e : (A B C : Ty lin) → `LnL
    `⊸i `⊸e : (A B : Ty lin) → `LnL
    `Fi : (X : Ty int) → `LnL
    `Fe : (X : Ty int) (C : Ty lin) → `LnL

    `1i : `LnL
    `×i : (X Y : Ty int) → `LnL
    `×e : (i : Hand) (X Y : Ty int) → `LnL
    `→i `→e : (X Y : Ty int) → `LnL
    `Gi `Ge : (A : Ty lin) → `LnL

  flags : PremisesFlags
  flags = record noPremisesFlags
    { Has-⊤ = ⊤ᴾ; Has-∧ = ⊤ᴾ; Has-ℑ = ⊤ᴾ; Has-✴ = ⊤ᴾ; Has-· = ⊤ᴾ; Has-□ = ⊤ᴾ }

  LnL : System flags
  LnL = `LnL ▹ λ where
    `Ii → `ℑ =⇒ lin , tI
    (`Ie C) → ⟨ []ᶜ `⊢ lin , tI ⟩ `✴ ⟨ []ᶜ `⊢ lin , C ⟩ =⇒ lin , C
    (`⊗i A B) → ⟨ []ᶜ `⊢ lin , A ⟩ `✴ ⟨ []ᶜ `⊢ lin , B ⟩ =⇒ lin , A t⊗ B
    (`⊗e A B C) →
      ⟨ []ᶜ `⊢ lin , A t⊗ B ⟩ `✴
      ⟨ [ u1 , lin , A ]ᶜ ++ᶜ [ u1 , lin , B ]ᶜ `⊢ lin , C ⟩
      =⇒ lin , C
    (`⊸i A B) → ⟨ [ u1 , lin , A ]ᶜ `⊢ lin , B ⟩ =⇒ lin , A t⊸ B
    (`⊸e A B) → ⟨ []ᶜ `⊢ lin , A t⊸ B ⟩ `✴ ⟨ []ᶜ `⊢ lin , A ⟩ =⇒ lin , B
    (`Fi X) → `□ ⟨ []ᶜ `⊢ int , X ⟩ =⇒ lin , tF X
    (`Fe X C) →
      ⟨ []ᶜ `⊢ lin , tF X ⟩ `✴ ⟨ [ uω , int , X ]ᶜ `⊢ lin , C ⟩ =⇒ lin , C

    `1i → `□ `⊤ =⇒ int , t1
    (`×i X Y) → `□ (⟨ []ᶜ `⊢ int , X ⟩ `∧ ⟨ []ᶜ `⊢ int , Y ⟩) =⇒ int , X t× Y
    (`×e i X Y) → `□ ⟨ []ᶜ `⊢ int , X t× Y ⟩ =⇒ int , [ X > i < Y ]
    (`→i X Y) → `□ ⟨ [ uω , int , X ]ᶜ `⊢ int , Y ⟩ =⇒ int , X t→ Y
    (`→e X Y) → `□ (⟨ []ᶜ `⊢ int , X t→ Y ⟩ `∧ ⟨ []ᶜ `⊢ int , X ⟩) =⇒ int , Y
    (`Gi A) → `□ ⟨ []ᶜ `⊢ lin , A ⟩ =⇒ int , tG A
    (`Ge A) → `□ ⟨ []ᶜ `⊢ int , tG A ⟩ =⇒ lin , A

  Term = [ LnL , ∞ ]_⊢_
  open WithScope (Scope Term)

  open import Generic.Linear.Example.UsageCheck ΣTy public
  open WithPoSemiring poSemiring public
  open WithInverses flags record
    { 0#⁻¹ = u0⁻¹ ; +⁻¹ = +⁻¹ ; 1#⁻¹ = u1⁻¹ ; *⁻¹ = *⁻¹ ; rep = rep }
    public

  module V where

    open import Generic.Linear.Syntax.Term ΣTy U.0-rawPoSemiring public
    open import Generic.Linear.Syntax.Interpretation ΣTy U.0-rawPoSemiring
      public
    open import Generic.Linear.Variable ΣTy U.0-rawPoSemiring public
    open import Generic.Linear.Renaming ΣTy U.0-poSemiring public

  pattern uvar i = V.`var (V.lvar i refl _)
  pattern uIi = V.`con (`Ii , refl , ℑ⟨ _ ⟩)
  pattern uIe C s t = V.`con (`Ie C , refl , s ✴⟨ _ ⟩ t)
  pattern u⊗i s t = V.`con (`⊗i _ _ , refl , s ✴⟨ _ ⟩ t)
  pattern u⊗e C s t = V.`con (`⊗e _ _ C , refl , s ✴⟨ _ ⟩ t)
  pattern u⊸i t = V.`con (`⊸i _ _ , refl , t)
  pattern u⊸e s t = V.`con (`⊸e _ _ , refl , s ✴⟨ _ ⟩ t)
  pattern uFi s = V.`con (`Fi _ , refl , □⟨ _ , _ , _ ⟩ s)
  pattern uFe C s t = V.`con (`Fe _ C , refl , s ✴⟨ _ ⟩ t)

  pattern u1i = V.`con (`1i , refl , □⟨ _ , _ , _ ⟩ tt)
  pattern u×i s t = V.`con (`×i _ _ , refl , □⟨ _ , _ , _ ⟩ (s , t))
  pattern u×e i s = V.`con (`×e i _ _ , refl , □⟨ _ , _ , _ ⟩ s)
  pattern u→i t = V.`con (`→i _ _ , refl , □⟨ _ , _ , _ ⟩ t)
  pattern u→e s t = V.`con (`→e _ _ , refl , □⟨ _ , _ , _ ⟩ (s , t))
  pattern uGi s = V.`con (`Gi _ , refl , □⟨ _ , _ , _ ⟩ s)
  pattern uGe s = V.`con (`Ge _ , refl , □⟨ _ , _ , _ ⟩ s)

  private
    myCojoin : (A : Ty lin) → Term []ᶜ (lin , t! A t⊸ t! (t! A))
    myCojoin A = let #0 = ↙ (↘ here) in elab-unique LnL
      (u⊸i (uFe _ (uvar #0) (uFi (uGi (uFi (uvar (# 1)))))))
      []

    myCopure : (A : Ty lin) → Term []ᶜ (lin , t! A t⊸ A)
    myCopure A = let #0 = ↙ (↘ here) in elab-unique LnL
      (u⊸i (uFe _ (uvar #0) (uGe (uvar (# 1)))))
      []

  {-
  -- Establish the invariant that in the intuitionistic fragment, all
  -- annotations are duplicable (i.e, either uω or u0).

  open import Algebra.Relational using (_◇_; _,_; middle; fst; snd)
  open import Data.LTree.Matrix

  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Environment ΣTy rawPoSemiring renaming
    (var to ivar)
  open import Generic.Linear.Renaming.Properties ΣTy poSemiring
  open import Generic.Linear.Semantics ΣTy poSemiring

  private
    variable
      t : Level
      S : Ctx → Set t
      T : Ctx → Set t

  data IntDup (T : Ctx → Set t) : OpenFam t where
    lin : ∀ {A} → ∀[ T ⇒ IntDup T (lin , A) ]
    int : ∀ {X} → ∀[ Dupᶜ T ⇒ IntDup T (int , X) ]

  map-□ : ∀[ S ⇒ T ] → ∀[ Dupᶜ S ⇒ Dupᶜ T ]
  map-□ f (□⟨ str , sp0 , sp+ ⟩ s) = □⟨ str , sp0 , sp+ ⟩ f s

  map-IntDup : ∀[ S ⇒ T ] → ∀ {A} → ∀[ IntDup S A ⇒ IntDup T A ]
  map-IntDup f (lin s) = lin (f s)
  map-IntDup f (int s) = int (map-□ (λ {Γ} → f {Γ}) s)

  th^IntDup : Thinnable T → ∀ {A} → Thinnable (IntDup T A)
  th^IntDup th^T (lin t) th = lin (th^T t th)
  th^IntDup th^T (int (□⟨ str , sp0 , sp+ ⟩ t)) th =
    let th′ , str′ = nat^Th (str , th) in
    int
    (□⟨ str′
      , ≤*-trans (unrowL₂ (*ᴹ-mono (rowL₂ sp0) ≤ᴹ-refl))
          (unrowL₂ (0ᴹ-*ᴹ (th .M)))
      , ≤*-trans (unrowL₂ (*ᴹ-mono (rowL₂ sp+) ≤ᴹ-refl))
        (unrowL₂ (+ᴹ-*ᴹ _ _ (th .M)))
      ⟩ th^T t th′)

  open Semantics

  IntDupSem : Semantics LnL (λ A → IntDup (LVar A) A) (IntDup λ _ → ⊤)
  IntDupSem .th^𝓥 = th^IntDup th^LVar
  IntDupSem .var = map-IntDup (λ _ → tt)
  IntDupSem .alg (`Ii , refl , t) = lin tt
  IntDupSem .alg (`Ie C , refl , t) = lin tt
  IntDupSem .alg (`⊗i A B , refl , t) = lin tt
  IntDupSem .alg (`⊗e A B C , refl , t) = lin tt
  IntDupSem .alg (`⊸i A B , refl , t) = lin tt
  IntDupSem .alg (`⊸e A B , refl , t) = lin tt
  IntDupSem .alg (`Fi X , refl , t) = lin tt
  IntDupSem .alg (`Fe X C , refl , t) = lin tt
  IntDupSem .alg {x = Γ} (`1i , refl , t) = int (map-□ (λ _ → tt) {Γ} t)
  IntDupSem .alg (`×i X Y , refl , t) =
    int (map-□ {S = Kripke _ _ _ _ ∩ Kripke _ _ _ _} (λ _ → tt) t)
  IntDupSem .alg (`×e i X Y , refl , t) =
    int (map-□ {S = Kripke _ _ _ _} (λ _ → tt) t)
  IntDupSem .alg (`→i X Y , refl , t) =
    int (map-□ {S = Kripke _ _ _ _} (λ _ → tt) t)
  IntDupSem .alg (`→e X Y , refl , t) =
    int (map-□ {S = Kripke _ _ _ _ ∩ Kripke _ _ _ _} (λ _ → tt) t)
  IntDupSem .alg (`Gi A , refl , t) =
    int (map-□ {S = Kripke _ _ _ _} (λ _ → tt) t)
  IntDupSem .alg (`Ge A , refl , t) = lin tt
  -}
