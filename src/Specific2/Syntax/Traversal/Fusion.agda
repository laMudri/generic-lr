{-# OPTIONS --safe --without-K --postfix-projections #-}

module Specific2.Syntax.Traversal.Fusion where

  open import Algebra.Skew
  open import Algebra.Skew.Construct.Vector
  open import Data.LTree
  open import Data.LTree.Vector
  open import Level using (0ℓ)
  open import Relation.Binary.PropositionalEquality
  open import Specific2.Syntax.Traversal as Trav using ()

  import Specific2.Syntax.Prelude as Pre

  module Identity {algebra : SkewSemiring 0ℓ 0ℓ} where

    open Pre algebra hiding (1ᴹ)
    open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_
    open import Specific2.Syntax.Traversal.IdHom algebra

    module _ {T} (K : Kit T) where

      open Kit K

      id-DeployedEnv : ∀ {PΓ} → DeployedEnv′ T PΓ PΓ
      id-DeployedEnv .linMap = 1ᴹ
      id-DeployedEnv .env .act j = vr (equip-var j ⊴*-refl)
      id-DeployedEnv .compat .get .get i = ⊴-refl

      trav-id : ∀ {PΓ A} (s : Tm PΓ A) → travD′ K id-DeployedEnv s ≡ s
      trav-id {A = A} (var x) = {!!}
      trav-id (app s t sp) = {!!}
      trav-id (lam s) = {!!}
      trav-id (unm s t sp) = {!!}
      trav-id (uni sp) = {!!}
      trav-id (prm s t sp) = {!!}
      trav-id (ten s t sp) = {!!}
      trav-id (exf s sp) = {!!}
      trav-id (cse s t u sp) = {!!}
      trav-id (inl s sp) = {!!}
      trav-id (inr s sp) = {!!}
      trav-id top = {!!}
      trav-id (prl s) = {!!}
      trav-id (prr s) = {!!}
      trav-id (wth s t) = {!!}
      trav-id (bam s t sp) = {!!}
      trav-id (bng s sp) = {!!}

  module Composition
    {X Y Z : SkewSemiring 0ℓ 0ℓ}
    (f : SkewSemiringMor X Y) (g : SkewSemiringMor Y Z)
    where

    private
      module X where
        open Pre X public
        open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_ public
          hiding (ctx→sctx)
        open import Generic.Linear.Syntax Ty Ann public
      module Y where
        open Pre Y public
        open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_ public
          hiding (ctx→sctx)
        open import Generic.Linear.Syntax Ty Ann public
      module Z where
        open Pre Z public
        open import Specific2.Syntax Ann _⊴_ 0# _+_ 1# _*_ public
          hiding (ctx→sctx)
        open import Generic.Linear.Syntax Ty Ann public

      module f where
        open import Specific2.Syntax.Traversal f public
      module g where
        open import Specific2.Syntax.Traversal g public
      module f>>g where
        open import Specific2.Syntax.Traversal (>>-SkewSemiringMor f g) public

    -- record >>Kit {S T U} (J : f.Kit S) (K : g.Kit T) (L : f>>g.Kit U)
    --              : Set where
    --   field

    module _ {S T} (J : f.Kit S) (K : g.Kit T)
             {PΓ : X.Ctx} {QΔ : Y.Ctx} {RΘ : Z.Ctx} where

      open Trav.DeployedEnv
      open Trav.Compat
      open Trav
      open SkewLeftSemimoduleMor

      >>-DeployedEnv : f.DeployedEnv S QΔ PΓ → g.DeployedEnv T RΘ QΔ →
                       f>>g.DeployedEnv {!!} RΘ PΓ
      >>-DeployedEnv ρ σ .linMap =
        vv-SkewLeftSemimoduleMor (ρ .linMap) (σ .linMap)
      >>-DeployedEnv ρ σ .env .act j =
        let ρj = ρ .env .act j in
        let foo = g.travD K σ (f.Kit.tm J (f.Kit.psh J (ρ .compat .get) {!ρ!})) in
        {!!}
      >>-DeployedEnv ρ σ .compat .get =
        Z.⊴*-trans (σ .compat .get) (σ .linMap .hom-mono (ρ .compat .get))
