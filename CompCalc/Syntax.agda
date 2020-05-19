open import Data.List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional

open import Relation.Binary.PropositionalEquality


module Syntax where

-- types

data Ty : Set where
  `⊥  : Ty                -- falsum
  `⊤  : Ty                -- verum
  _∧_ : Ty → Ty → Ty      -- conjunction 
  _⊃_ : Ty → Ty → Ty      -- implication
  _∨_ : Ty → Ty → Ty      -- disjunction 
  ◆   : Ty → Ty           -- modality

-- natural deduction

Ctx : Set
Ctx = List Ty

infix 0 _⊢_

data _⊢_ : Ctx → Ty → Set where
  -- identity
  id : ∀ {Γ A} → A ∈ Γ → Γ ⊢ A
  -- verum
  `⊤  : ∀ {Γ} → Γ ⊢ `⊤
  -- falsum
  ExFalsum : ∀ {Γ A} → Γ ⊢ `⊥ → Γ ⊢ A
  -- conjunction 
  _,_ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ∧ B)
  fst : ∀ {Γ A B} → Γ ⊢ (A ∧ B) → Γ ⊢ A
  snd : ∀ {Γ A B} → Γ ⊢ (A ∧ B) → Γ ⊢ B
  -- implication

  abs : ∀ {Γ A B} → (A ∷ Γ) ⊢ B → Γ ⊢ (A ⊃ B)
  app : ∀ {Γ A B} → Γ ⊢ (A ⊃ B) → Γ ⊢ A → Γ ⊢ B
  -- disjunction
  inl : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ (A ∨ B)
  inr : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ (A ∨ B)
  case : ∀ {Γ A B C} → Γ ⊢ (A ∨ B) → (A ∷ Γ) ⊢ C → (B ∷ Γ) ⊢ C → Γ ⊢ C
  -- modality
  val : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ ◆ A
  bind : ∀ {Γ A B} → Γ ⊢ ◆ A → (A ∷ Γ) ⊢ ◆ B → Γ ⊢ ◆ B


-- substitution / cut

substitution : ∀ {Γ A B} → Γ ⊢ A → (A ∷ Γ) ⊢ B → Γ ⊢ B
substitution (id x) p' = app (abs p') (id x)
substitution `⊤ p' = app (abs p') `⊤
substitution (ExFalsum p) p' = ExFalsum p
substitution (p , p₁) p' = app (abs p') (p , p₁)
substitution (fst p) p' = app (abs p') (fst p)
substitution (snd p) p' = app (abs p') (snd p)
substitution (abs p) p' = app (abs p') (abs p)
substitution (app p p₁) p' = app (abs p') (app p p₁)
substitution (inl p) p' = app (abs p') (inl p)
substitution (inr p) p' = app (abs p') (inr p)
substitution (case p p₁ p₂) p' = app (abs p') (case p p₁ p₂)
substitution (val p) p' = app (abs p') (val p)
substitution (bind p p₁) p' = app (abs p') (bind p p₁)
