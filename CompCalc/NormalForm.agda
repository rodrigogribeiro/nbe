open import Data.List hiding (drop)
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

open import Relation.Binary.PropositionalEquality

open import Embeddings
open import Syntax
open import Utils


module NormalForm (S : Monad) where

open Monad S

-- normal and neutral forms

mutual
  data Nf (Γ : Ctx) : Ty → Set where
    ne-⊤ : Ne Γ `⊤ → Nf Γ `⊤
    ne-⊥ : Ne Γ `⊥ → Nf Γ `⊥
    lam  : ∀ {A B} → Nf (A ∷ Γ) B → Nf Γ (A ⊃ B)
    inl  : ∀ {A B} → Nf Γ A → Nf Γ (A ∨ B)
    inr  : ∀ {A B} → Nf Γ B → Nf Γ (A ∨ B)
    _,_  : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A ∧ B)


  data Ne (Γ : Ctx) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⊃ B) → Nf Γ A → Ne Γ B
