{-# OPTIONS --safe --without-K #-}

-- Functional vectors indexed by tree sizes

module Data.LTree.Vector where

  open import Data.LTree
  open import Data.Product using (_×_; _,_)
  open import Function.Base using (id; _∘_)
  open import Level using (Level; _⊔_)
  open import Relation.Binary using (REL)
  open import Relation.Unary using (Pred)

  private
    variable
      a b c r : Level
      A : Set a
      B : Set b
      C : Set c
      s t : LTree

  infixr 5 _++_

  Vector : Set a → LTree → Set a
  Vector A s = Ptr s → A

  lift₀ : A → ∀ {s} → Vector A s
  lift₀ x _ = x

  lift₁ : (A → B) → ∀ {s} → Vector A s → Vector B s
  lift₁ f u i = f (u i)

  lift₂ : (A → B → C) → ∀ {s} → Vector A s → Vector B s → Vector C s
  lift₂ f u v i = f (u i) (v i)

  record Lift₁ (R : Pred A r) {s} (u : Vector A s) : Set r where
    constructor mk
    field get : ∀ i → R (u i)
  open Lift₁ public

  record Lift₂ (R : REL A B r) {s} (u : Vector A s) (v : Vector B s)
               : Set r where
    constructor mk
    field get : ∀ i → R (u i) (v i)
  open Lift₂ public

  [_] : A → Vector A [-]
  [ x ] _ = x

  [] : Vector A ε
  [] (there () _)

  _++_ : Vector A s → Vector A t → Vector A (s <+> t)
  (u ++ v) (go-left i) = u i
  (u ++ v) (go-right j) = v j

  un[-] : Vector A [-] → A
  un[-] v = v here

  un++ : Vector A (s <+> t) → Vector A s × Vector A t
  un++ v = v ∘ there left , v ∘ there right

  module _ (b : A → B) (e : B) (a : B → B → B) where

    fold : Vector A s → B
    fold {[-]} u = b (u here)
    fold {ε} u = e
    fold {s <+> t} u = a (fold (u ∘ go-left)) (fold (u ∘ go-right))
