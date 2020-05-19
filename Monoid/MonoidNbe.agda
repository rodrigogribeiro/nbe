open import Data.List

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary hiding (Sym ; Trans)

module MonoidNbe {A : Set}(_≡?_ : Decidable {A = A} _≡_) where

  data Exp : Set where
    Val : A -> Exp
    ε   : Exp
    _●_ : Exp -> Exp -> Exp

  ⟦_⟧ : Exp -> Exp -> Exp
  ⟦ Val x ⟧ e' = Val x ● e'
  ⟦ ε ⟧ e' = e'
  ⟦ e ● e' ⟧ e'' = ⟦ e ⟧ (⟦ e' ⟧ e'')


  reify : (Exp -> Exp) -> Exp
  reify f = f ε

  nbe : Exp -> Exp
  nbe e = reify ⟦ e ⟧

  data _~_ : Exp -> Exp -> Set where
    Refl  : ∀ {e} -> e ~ e
    Sym   : ∀ {e e'} -> e ~ e' -> e' ~ e
    Trans : ∀ {e e' e''} -> e ~ e'   ->
                            e' ~ e'' ->
                            e  ~ e''
    Assoc : ∀ {e e' e''} -> (e ● (e' ● e'')) ~ ((e ● e') ● e'')
    Idr : ∀ {e} -> e ~ (e ● ε)
    Idl : ∀ {e} -> e ~ (ε ● e)
    Fun : ∀ {e e1 e' e1'} -> e ~ e1   ->
                             e' ~ e1' ->
                             (e ● e') ~ (e1 ● e1')




  ~-lemma : ∀ {e e'} -> e ~ e' -> ⟦ e ⟧ ≡ ⟦ e' ⟧
  ~-lemma Refl = refl
  ~-lemma (Sym p) rewrite (~-lemma p) = refl
  ~-lemma (Trans p p') rewrite (~-lemma p) | ~-lemma p' = refl
  ~-lemma Assoc = refl
  ~-lemma Idr = refl
  ~-lemma Idl = refl
  ~-lemma (Fun p p') rewrite ~-lemma p' | ~-lemma p = refl

  soundness : ∀ {e e'} -> e ~ e' -> (nbe e) ≡ (nbe e')
  soundness Refl = refl
  soundness (Sym p) rewrite (soundness p) = refl
  soundness (Trans p p') rewrite (soundness p) | soundness p' = refl
  soundness Assoc = refl
  soundness Idr = refl
  soundness Idl = refl
  soundness (Fun p p') rewrite soundness p' | ~-lemma p = refl

  ~-nbe-lemma : ∀ e e' -> (e ● e') ~ ⟦ e ⟧ e'
  ~-nbe-lemma (Val x) e' = Refl
  ~-nbe-lemma ε e' = Sym Idl
  ~-nbe-lemma (e ● e1) e'
      = Trans (Sym Assoc)
              (Trans (Fun Refl (~-nbe-lemma e1 e'))
                     (~-nbe-lemma e (⟦ e1 ⟧ e')))

  completeness-lemma : ∀ e -> e ~ nbe e
  completeness-lemma e with ~-nbe-lemma e ε
  ...| p = Trans Idr p


  completeness : ∀ e e' -> nbe e ≡ nbe e' -> e ~ e'
  completeness e e' eq with completeness-lemma e | completeness-lemma e'
  ...| p | p' rewrite eq = Trans p (Sym p') 
