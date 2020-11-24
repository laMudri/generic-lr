{-# OPTIONS --safe --without-K #-}

module Data.LTree.Automation where

  open import Data.LTree

  open import Data.Fin as F using (Fin; zero; suc; splitAt)
  open import Data.Nat as N
  open import Data.Sum as ⊎
  open import Function.Base
  open import Relation.Nullary.Decidable

  size : LTree → ℕ
  size [-] = 1
  size ε = 0
  size (s <+> t) = size s + size t

  Fin→Ptr : ∀ {t} → Fin (size t) → Ptr t
  Fin→Ptr {[-]} i = here
  Fin→Ptr {s <+> t} i = case splitAt (size s) i of λ where
    (inj₁ j) → ↙ (Fin→Ptr j)
    (inj₂ k) → ↘ (Fin→Ptr k)

  infix 10 #_

  #_ : ∀ {t} (m : ℕ) {m< : True (m <? size t)} → Ptr t
  #_ m {m<} = Fin→Ptr (F.#_ m {m<n = m<})
