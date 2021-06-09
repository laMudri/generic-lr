{-# OPTIONS --without-K --safe --postfix-projections #-}

module Algebra.Relational.Construct.Vector where

  open import Algebra.Relational
  open import Data.LTree
  open import Data.LTree.Vector hiding ([_])
  open import Data.Wrap
  open import Function.Base using (_∘_)

  Vector-relLeftSemimodule :
    ∀ {c ℓ} (R : RelSemiring c ℓ) → LTree → RelLeftSemimodule R c ℓ
  Vector-relLeftSemimodule R s = record
    { Carrierₘ = Vector Carrier s
    ; _≤ₘ_ = Lift₂ _≤_
    ; _≤0ₘ = Wrap λ v → ∀ i → v i ≤0
    ; _≤[_+ₘ_] = Wrap λ w u v → ∀ i → w i ≤[ u i + v i ]
    ; _≤[_*ₘ_] = Wrap λ v r u → ∀ i → v i ≤[ r * u i ]
    ; isProset = record
      { refl = λ { .get i → refl }
      ; trans = λ { uu vv .get i → trans (uu .get i) (vv .get i) }
      }
    ; 0ₘ-mono = λ { uu u0 .get i → 0-mono (uu .get i) (u0 .get i) }
    ; +ₘ-mono = λ { ww uu vv wuv .get i →
      +-mono (ww .get i) (uu .get i) (vv .get i) (wuv .get i) }
    ; *ₘ-mono = λ { vv rr uu vru .get i →
      *-mono (vv .get i) rr (uu .get i) (vru .get i) }
    ; isRelLeftSemimodule = record
      { +ₘ-isCommutativeRelMonoid = record
        { isRelMonoid = record
          { isLeftSkewRelMonoid = record
            { identityˡ→ = λ { (u0 , wuv) .get i →
              +-identityˡ→ (u0 .get i , wuv .get i) }
            ; identityʳ← = λ { (mk wu) →
              let f i = +-identityʳ← (wu i) in
              [ fst ∘ f ] , [ snd ∘ f ] }
            ; assoc→ = λ { ([ u+v ] , [ uv+w ]) →
              let f i = +-assoc→ (u+v i , uv+w i) in
              [ fst ∘ f ] , [ snd ∘ f ] }
            }
          ; isRightSkewRelMonoid = record
            { identityˡ← = λ { (mk wv) →
              let f i = +-identityˡ← (wv i) in
              [ fst ∘ f ] , [ snd ∘ f ] }
            ; identityʳ→ = λ { (wuv , v0) .get i →
              +-identityʳ→ (wuv .get i , v0 .get i) }
            ; assoc← = λ { ([ u+vw ] , [ v+w ]) →
              let f i = +-assoc← (u+vw i , v+w i) in
              [ fst ∘ f ] , [ snd ∘ f ] }
            }
          }
        ; comm = λ { wuv .get i → +-comm (wuv .get i) }
        }
      ; *ₘ-identity→ = λ { (r1 , vru) .get i → *-identityˡ→ (r1 , vru .get i) }
      ; *ₘ-identity← = λ { (mk vu) → {!!} , {![ (λ i → *-identityˡ← (vu i) .snd) ]!} }
      ; *ₘ-assoc→ = {!!}
      ; *ₘ-assoc← = {!!}
      ; *ₘ-annihilˡ→ = {!!}
      ; *ₘ-annihilˡ← = {!!}
      ; *ₘ-annihilʳ→ = {!!}
      ; *ₘ-annihilʳ← = {!!}
      ; *ₘ-distribˡ→ = {!!}
      ; *ₘ-distribˡ← = {!!}
      ; *ₘ-distribʳ→ = {!!}
      ; *ₘ-distribʳ← = {!!}
      }
    } where open RelSemiring R
