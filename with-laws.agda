{-# OPTIONS --cubical --guardedness #-}

module with-laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat                 hiding (elim)
open import Cubical.Data.Sum                 hiding (elim)
open import Cubical.Data.FinData             hiding (elim)
open import Cubical.Data.Empty
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.Data.Bool                hiding (elim)
open import Agda.Builtin.String

data R {n : ℕ} : Type where
  doc : R
  _↔_[at]_ : (s1 s2 : String) → (i : Fin n) → doc ≡ doc
  indep : (s t u v : String) (i j : Fin n) → (i ≡ j → ⊥) → (_↔_[at]_ {n = n} s t i) ∙ (_↔_[at]_ {n = n} u v j) ≡ (_↔_[at]_ {n = n} u v j) ∙ (_↔_[at]_ {n = n} s t i)
  noop : (s : String) (i : Fin n) → _↔_[at]_ {n = n} s s i ≡ refl

-- apd f : (p : x ≡ y) → PathOver B p (f x) (f y)
-- congP {B} f p

-- f doc = doc'
-- β₁ : fold swap
-- β₂₁ : PathOver (λ (x , y) → x ∙ y ≡ y ∙ x) (β₁ , β₁) (ap (ap f) (indep s t uv i j i≠j)) (indep' s t u v i j i≠j) 
-- β₂₂ : PathOver (λ x → x ≡ refl) β₁ (ap (ap f) (noop s i)) (noop' s i) 
fold : {n : ℕ} {X : Type} (doc' : X) (swap' : (s1 s2 : String) (i : Fin n) → doc' ≡ doc')
       (indep' : (s t u v : String) (i j : Fin n) → (i ≡ j → ⊥) → (swap' s t i) ∙ (swap' u v j) ≡ (swap' u v j) ∙ (swap' s t i))
       (noop' : (s : String) (i : Fin n) → swap' s s i ≡ refl) → R {n} → X
fold doc' swap' indep' noop' doc                           = doc'
fold doc' swap' indep' noop' ((s1 ↔ s2 [at] i) j)          = swap' s1 s2 i j
fold doc' swap' indep' noop' (indep s t u v i j i≠j x y)   = {!!}
fold doc' swap' indep' noop' (noop s i i₁ i₂)              = {!!}

postulate
    stringEq : (s1 s2 : String) → (s1 ≡ s2) ⊎ (s1 ≡ s2 → ⊥)

permute : (String × String) → String → String
permute (s1 , s2) s with stringEq s1 s
... | inl x = s2
... | inr x with stringEq s2 s
... | inl y = s1
... | inr y = s

applyat : {n : ℕ} {A : Type} → (A → A) → Fin n → Vec A n → Vec A n
applyat f zero (x ∷ v) = f x ∷ v
applyat f (suc i) (x ∷ v) = x ∷ (applyat f i v)

permute-perm : ((s1 , s2) : String × String) → (s : String)
               → permute (s1 , s2) (permute (s1 , s2) s) ≡ s
permute-perm (s1 , s2) s with stringEq s1 s
permute-perm (s1 , s2) s | inl x with stringEq s1 s2
permute-perm (s1 , s2) s | inl x | inl y = y ⁻¹ ∙ x
permute-perm (s1 , s2) s | inl x | inr y with stringEq s2 s2
permute-perm (s1 , s2) s | inl x | inr y | inl z = x -- x
permute-perm (s1 , s2) s | inl x | inr y | inr z = elim (z (refl))
permute-perm (s1 , s2) s | inr x with stringEq s2 s
permute-perm (s1 , s2) s | inr x | inl y with stringEq s1 s1
permute-perm (s1 , s2) s | inr x | inl y | inl z = y
permute-perm (s1 , s2) s | inr x | inl y | inr z with stringEq s2 s1
permute-perm (s1 , s2) s | inr x | inl y | inr z | inl w = elim (z refl)
permute-perm (s1 , s2) s | inr x | inl y | inr z | inr w = elim (z refl)
permute-perm (s1 , s2) s | inr x | inr y with stringEq s1 s
permute-perm (s1 , s2) s | inr x | inr y | inl z = elim (x z)
permute-perm (s1 , s2) s | inr x | inr y | inr z with stringEq s2 s
permute-perm (s1 , s2) s | inr x | inr y | inr z | inl w = elim (y w)
permute-perm (s1 , s2) s | inr x | inr y | inr z | inr w = refl

applyat-perm2 : {n : ℕ} → ((s1 , s2) : String × String) → (i : Fin n)
                → (v : Vec String n)
                → applyat (permute (s1 , s2)) i (applyat (permute (s1 , s2)) i v) ≡ v
applyat-perm2 (s1 , s2) zero (x ∷ v) = cong (_∷ v) (permute-perm (s1 , s2) x) 
applyat-perm2 (s1 , s2) (suc i) (x ∷ v) = cong (x ∷_) (applyat-perm2 (s1 , s2) i v) 

open Iso
swapatIso : {n : ℕ} → (String × String) → Fin n → Iso (Vec String n) (Vec String n) 
swapatIso (s1 , s2) i .fun = applyat (permute (s1 , s2)) i
swapatIso (s1 , s2) i .inv = applyat (permute (s1 , s2)) i
swapatIso (s1 , s2) i .sec = applyat-perm2 (s1 , s2) i
swapatIso (s1 , s2) i .ret = applyat-perm2 (s1 , s2) i

swapat : {n : ℕ} → (String × String) → Fin n → Vec String n ≃ Vec String n
swapat (s1 , s2) i = isoToEquiv (swapatIso (s1 , s2) i)

swapat-independent : {n : ℕ} (s t u v : String) (i j : Fin n) → (i ≡ j → ⊥)
                     → (swapat (s , t) i) ∙ₑ (swapat (u , v) j) ≡ (swapat (u , v) j) ∙ₑ (swapat (s , t) i)
swapat-independent s t u v i j i≠j x = {!!}

I' : {n : ℕ} → R {n} → Type
I' {n} doc = Vec String n
I' {n} ((s1 ↔ s2 [at] i) j) = ua (swapat (s1 , s2) i) j
I' {n} (indep s t u v i j x i₁ i₂) = {!!}
I' {n} (noop s i i₁ i₂) = {!!}

interp : {n : ℕ} → (doc ≡ doc) → (Vec String n) ≃ (Vec String n) 
interp p = {!!}

