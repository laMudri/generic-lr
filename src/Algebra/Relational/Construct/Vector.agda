{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Relational.Construct.Vector where

  open import Algebra.Po
  open import Algebra.PoToRel
  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector hiding ([_])
  open import Data.Wrap
  open import Function.Base using (_∘_)

  open _↘_↙_

  Vector-fRelLeftSemimodule :
    ∀ {c ℓ} (R : FRelSemiring c ℓ) → LTree → FRelLeftSemimodule R c ℓ
  Vector-fRelLeftSemimodule R s = record
    { Carrierₘ = Vector Carrier s
    ; _≤ₘ_ = Liftₙ _≤_
    ; _≤0ₘ = Liftₙ _≤0
    ; _≤[_+ₘ_] = Liftₙ _≤[_+_]
    ; _≤[_*ₘ_] = λ v r u → Liftₙ _≤[ r *_] v u
    ; isProset = record
      { refl = λ { .get i → refl }
      ; trans = λ { uu vv .get i → trans (uu .get i) (vv .get i) }
      }
    ; 0ₘ-mono = λ { uu u0 .get i → 0-mono (uu .get i) (u0 .get i) }
    ; +ₘ-mono = λ { ww uu vv wuv .get i →
      +-mono (ww .get i) (uu .get i) (vv .get i) (wuv .get i) }
    ; *ₘ-mono = λ { vv rr uu vru .get i →
      *-mono (vv .get i) rr (uu .get i) (vru .get i) }
    ; isFRelLeftSemimodule = record
      { isRelLeftSemimodule = record
        { +ₘ-isCommutativeRelMonoid = record
          { isRelMonoid = record
            { isLeftSkewRelMonoid = record
              { identityˡ→ = λ { (u0 , wuv) .get i →
                +-identityˡ→ (u0 .get i , wuv .get i) }
              ; identityʳ← = λ { (mk wu) →
                let f i = +-identityʳ← (wu i) in
                mk (fst ∘ f) , mk (snd ∘ f) }
              ; assoc→ = λ { (mk u+v , mk uv+w) →
                let f i = +-assoc→ (u+v i , uv+w i) in
                mk (fst ∘ f) , mk (snd ∘ f) }
              }
            ; isRightSkewRelMonoid = record
              { identityˡ← = λ { (mk wv) →
                let f i = +-identityˡ← (wv i) in
                mk (fst ∘ f) , mk (snd ∘ f) }
              ; identityʳ→ = λ { (wuv , v0) .get i →
                +-identityʳ→ (wuv .get i , v0 .get i) }
              ; assoc← = λ { (mk u+vw , mk v+w) →
                let f i = +-assoc← (u+vw i , v+w i) in
                mk (fst ∘ f) , mk (snd ∘ f) }
              }
            }
          ; comm = λ { wuv .get i → +-comm (wuv .get i) }
          }
        ; *ₘ-identity→ = λ (r1 , vru) → mk λ i → *-identityˡ→ (r1 , vru .get i)
        ; *ₘ-identity← = λ vu →
          1-func .holds , mk λ i →
            let r1 , vru = *-identityˡ← (vu .get i) in
            *-mono refl (1-func .unique r1) refl vru
        ; *ₘ-assoc→ = λ (r*s , rsu) →
          let lemma = λ i → *-assoc→ (r*s , rsu .get i) in
          (mk λ i → lemma i .fst) , (mk λ i → lemma i .snd)
        ; *ₘ-assoc← = λ (ruv , ru) →
          let lemma = λ i → *-assoc← (ruv .get i , ru .get i) in
          *-func _ _ .holds , mk λ i →
            *-mono refl (*-func _ _ .unique (lemma i .fst)) refl (lemma i .snd)
        ; *ₘ-annihilˡ→ = λ (r0 , ru) → mk λ i → annihilˡ→ (r0 , (ru .get i))
        ; *ₘ-annihilˡ← = λ u0 →
          0-func .holds , mk λ i →
            let r0 , ru = annihilˡ← (u0 .get i) in
            *-mono refl (0-func .unique r0) refl ru
        ; *ₘ-annihilʳ→ = λ (ru , u0) →
          mk λ i → annihilʳ→ (ru .get i , u0 .get i)
        ; *ₘ-annihilʳ← = λ u0 →
          let lemma = λ i → annihilʳ← (u0 .get i) in
          (mk λ i → lemma i .fst) , (mk λ i → lemma i .snd)
        ; *ₘ-distribˡ→ = λ (rs , rsu) →
          let lemma = λ i → distribˡ→ (rs , rsu .get i) in
          (mk λ i → lemma i .lprf)
            ↘, (mk λ i → lemma i .centre) ,↙
          (mk λ i → lemma i .rprf)
        ; *ₘ-distribˡ← = λ (ru ↘, rusu ,↙ su) →
          let lemma = λ i → distribˡ← (ru .get i ↘, rusu .get i ,↙ su .get i) in
          +-func _ _ .holds , mk λ i →
            *-mono refl (+-func _ _ .unique (lemma i .fst)) refl (lemma i .snd)
        ; *ₘ-distribʳ→ = λ (ruv , uv) →
          let lemma = λ i → distribʳ→ (ruv .get i , uv .get i) in
          (mk λ i → lemma i .lprf)
            ↘, (mk λ i → lemma i .centre) ,↙
          (mk λ i → lemma i .rprf)
        ; *ₘ-distribʳ← = λ (ru ↘, rurv ,↙ rv) →
          let lemma = λ i → distribʳ← (ru .get i ↘, rurv .get i ,↙ rv .get i) in
          (mk λ i → lemma i .fst) , (mk λ i → lemma i .snd)
        }
      ; 0ₘ-func = λ where
        .witness i → 0-func .witness
        .holds .get i → 0-func .holds
        .unique u0 .get i → 0-func .unique (u0 .get i)
      ; +ₘ-func = λ u v → λ where
        .witness i → +-func (u i) (v i) .witness
        .holds .get i → +-func _ _ .holds
        .unique uv .get i → +-func _ _ .unique (uv .get i)
      ; *ₘ-func = λ r u → λ where
        .witness i → *-func r (u i) .witness
        .holds .get i → *-func _ _ .holds
        .unique ru .get i → *-func _ _ .unique (ru .get i)
      }
    } where open FRelSemiring R
