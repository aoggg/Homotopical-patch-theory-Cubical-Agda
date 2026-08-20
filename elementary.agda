{-# OPTIONS --cubical --guardedness #-}

module elementary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Int
open import Cubical.Data.Nat                 hiding (_+_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws

data R : Type where
  num  : R
  add1 : num ≡ num

Patch = num ≡ num

open Iso
successor : Iso ℤ ℤ
successor .fun = sucℤ
successor .inv = predℤ
successor .sec = sucPred
successor .ret = predSuc

succEquiv : ℤ ≃ ℤ
succEquiv = isoToEquiv successor

foldR : {X : Type} (b : X) → (l : b ≡ b) → R → X
foldR b l num      = b
foldR b l (add1 i) = l i

I' : R → Type
I' num      = ℤ
I' (add1 i) = ua succEquiv i 

-- ua : Bijection A B → A ≡ B (isoToPath)
-- coeBiject : A ≡ B → Bijection A B (pathToIso)

interp : (num ≡ num) → ℤ ≃ ℤ
interp p = pathToEquiv (λ i → I' (p i)) 

interp-add1 : interp add1 ≡ succEquiv 
interp-add1 = pathToEquiv-ua succEquiv
-- interp add1                     ≡⟨ refl ⟩
-- pathToEquiv (λ i → I' (add1 i)) ≡⟨ refl ⟩
-- pathToEquiv (ua succEquiv)      ≡⟨ pathToEquiv-ua succEquiv ⟩
-- succEquiv                       ∎

-- path composition : _∙_
-- equiv composition : _∙ₑ_

pathToEquiv-comp : {A B C : Type} (q : A ≡ B) → (p : B ≡ C)
                   → pathToEquiv (q ∙ p) ≡ pathToEquiv q ∙ₑ pathToEquiv p 
pathToEquiv-comp q p =
    pathToEquiv (q ∙ p)
        ≡⟨ cong pathToEquiv (cong₂ _∙_ (sym (ua-pathToEquiv q)) (sym (ua-pathToEquiv p))) ⟩
    pathToEquiv (ua (pathToEquiv q) ∙ ua (pathToEquiv p))
        ≡⟨ cong pathToEquiv (sym (uaCompEquiv (pathToEquiv q) (pathToEquiv p))) ⟩
    pathToEquiv (ua (pathToEquiv q ∙ₑ pathToEquiv p))
        ≡⟨ pathToEquiv-ua (pathToEquiv q ∙ₑ pathToEquiv p) ⟩
    pathToEquiv q ∙ₑ pathToEquiv p ∎

interp-trans : {q p : num ≡ num} → interp (q ∙ p) ≡ ((interp q) ∙ₑ (interp p))
interp-trans {q = q} {p = p} = pathToEquiv-comp (cong I' q) (cong I' p)
--     interp (q ∙ p)
--         ≡⟨ refl ⟩
--     pathToEquiv (cong I' (q ∙ p))
--         ≡⟨ refl ⟩
--     pathToEquiv ((cong I' q) ∙ (cong I' p))
--         ≡⟨ pathToEquiv-comp (cong I' q) (cong I' p) ⟩
--     pathToEquiv (cong I' q) ∙ₑ pathToEquiv (cong I' p)
--         ≡⟨ refl ⟩
--     (interp q) ∙ₑ (interp p) ∎

interp-refl : interp refl ≡ idEquiv ℤ
interp-refl = pathToEquivRefl
--     interp refl      ≡⟨ refl ⟩
--     pathToEquiv refl ≡⟨ pathToEquivRefl ⟩
--     idEquiv ℤ        ∎

interp-sym : {p : num ≡ num} → interp (sym p) ≡ invEquiv (interp p)
interp-sym {p = p} =
    interp (sym p)
        ≡⟨ refl ⟩
    pathToEquiv (cong I' (sym p))
        ≡⟨ refl ⟩
    pathToEquiv (sym (cong I' p))
        ≡⟨ cong (λ x → pathToEquiv (sym x)) (sym (ua-pathToEquiv (cong I' p))) ⟩
    pathToEquiv (sym (ua (pathToEquiv (cong I' p))))
        ≡⟨ cong (λ x → pathToEquiv x) (sym (uaInvEquiv (pathToEquiv (cong I' p)))) ⟩
    pathToEquiv (ua (invEquiv (pathToEquiv (cong I' p))))
        ≡⟨ pathToEquiv-ua (invEquiv (pathToEquiv (cong I' p))) ⟩
    invEquiv (pathToEquiv (cong I' p))
        ≡⟨ refl ⟩
    invEquiv (interp p) ∎

interp-comp-rev : (interp (add1 ∙ sym add1) .fst) 0 ≡ 0
interp-comp-rev = refl 

winding : num ≡ num → ℤ
winding p = ((interp p) .fst) 0

repeat : ℤ → num ≡ num
repeat (pos zero)       = refl
repeat (pos (suc n))    = repeat (pos n) ∙ add1
repeat (negsuc zero)    = sym add1
repeat (negsuc (suc n)) = repeat (negsuc n) ∙ sym add1

repeat-sucℤ : (z : ℤ) → repeat (sucℤ z) ≡ repeat z ∙ add1
repeat-sucℤ (pos n)          = refl
repeat-sucℤ (negsuc zero)    = sym (lCancel add1)
repeat-sucℤ (negsuc (suc n)) = rUnit (repeat (negsuc n)) ∙ (λ i → repeat (negsuc n) ∙ lCancel add1 (~ i)) ∙ assoc (repeat (negsuc n)) (sym add1) add1

repeat-predℤ : (z : ℤ) → repeat (predℤ z) ≡ repeat z ∙ sym add1
repeat-predℤ (pos zero)      = lUnit (sym add1)
repeat-predℤ (pos (suc n))   = rUnit (repeat (pos n)) ∙ (λ i → repeat (pos n) ∙ rCancel add1 (~ i)) ∙ assoc (repeat (pos n)) add1 (sym add1)
repeat-predℤ (negsuc n)      = refl

repeat-homo : (x : ℤ) → (y : ℤ) → repeat (x + y) ≡ repeat x ∙ repeat y
repeat-homo x (pos zero)       = rUnit (repeat x)
-- repeat (x + pos 0) ≡⟨ refl ⟩
-- repeat (x +pos 0)  ≡⟨ refl ⟩
-- repeat x           ≡⟨ rUnit (repeat x) ⟩
-- repeat x ∙ refl    ≡⟨ refl ⟩
-- repeat x ∙ repeat (pos 0) ∎
repeat-homo x (pos (suc n))    =
    repeat (x + pos (suc n))
        ≡⟨ refl ⟩
    repeat (x +pos (suc n)) 
        ≡⟨ refl ⟩
    repeat (sucℤ (x +pos n))
        ≡⟨ repeat-sucℤ (x +pos n) ⟩
    repeat (x +pos n) ∙ add1
        ≡⟨ refl ⟩
    repeat (x + (pos n)) ∙ add1
        ≡⟨ cong (_∙ add1) (repeat-homo x (pos n)) ∙ sym (assoc (repeat x) (repeat (pos n)) add1) ⟩
    repeat x ∙ repeat (pos n) ∙ add1
        ≡⟨ refl ⟩
    repeat x ∙ repeat (pos (suc n)) ∎
repeat-homo x (negsuc zero)    = repeat-predℤ x
--     repeat (x + negsuc 0) ≡⟨ refl ⟩
--     repeat (x +negsuc 0) ≡⟨ refl ⟩
--     repeat (predℤ x) ≡⟨ repeat-predℤ x ⟩
--     repeat x ∙ sym (add1) ≡⟨ refl ⟩
--     repeat x ∙ repeat (negsuc 0) ∎
repeat-homo x (negsuc (suc n)) =
    repeat (x + negsuc (suc n))
        ≡⟨ refl ⟩
    repeat (x +negsuc (suc n))
        ≡⟨ refl ⟩
    repeat (predℤ (x +negsuc n))
        ≡⟨ repeat-predℤ (x +negsuc n) ⟩
    repeat (x +negsuc n) ∙ sym add1
        ≡⟨ cong (_∙ sym add1) (repeat-homo x (negsuc n)) ∙ sym (assoc (repeat x) (repeat (negsuc n)) (sym add1)) ⟩
    repeat x ∙ repeat (negsuc n) ∙ sym add1
        ≡⟨ refl ⟩
    repeat x ∙ repeat (negsuc (suc n)) ∎

repeat-comm : (x : ℤ) → (y : ℤ) → repeat x ∙ repeat y ≡ repeat y ∙ repeat x
repeat-comm x y = repeat x ∙ repeat y ≡⟨ sym (repeat-homo x y) ⟩
                  repeat (x + y)      ≡⟨ cong repeat (+Comm x y) ⟩
                  repeat (y + x)      ≡⟨ repeat-homo y x ⟩
                  repeat y ∙ repeat x ∎ 

winding-repeat : (n : ℤ) → winding (repeat n) ≡ n
winding-repeat (pos zero)       = refl
winding-repeat (pos (suc n))    = cong (_+ winding (add1)) (winding-repeat (pos n))
--     winding (repeat (pos (suc n))) ≡⟨ refl ⟩
--     winding (repeat (pos n) ∙ add1) ≡⟨ refl ⟩
--     winding (repeat (pos n)) + winding (add1) ≡⟨ cong (_+ winding (add1)) (winding-repeat (pos n)) ⟩
--     (pos n) + 1 ≡⟨ refl ⟩
--     pos (suc n) ∎
winding-repeat (negsuc zero)    = refl 
winding-repeat (negsuc (suc n)) = cong (_+ winding (sym add1)) (winding-repeat (negsuc n))
--     winding (repeat (negsuc (suc n))) ≡⟨ refl ⟩
--     winding (repeat (negsuc n) ∙ sym add1) ≡⟨ refl ⟩
--     winding (repeat (negsuc n)) + winding (sym add1) ≡⟨ cong (_+ winding (sym add1)) (winding-repeat (negsuc n)) ⟩
--     (negsuc n) - 1 ≡⟨ refl ⟩
--     negsuc (suc n) ∎

encode : (x : R) → num ≡ x → I' x
encode x p = transport (cong I' p) 0

decodeSquare : (n : ℤ) → PathP (λ i → num ≡ add1 i) (repeat (predℤ n)) (repeat n)
decodeSquare (pos zero) i j    = add1 (i ∨ ~ j)
decodeSquare (pos (suc n)) i j = hfill (λ k → λ { (j = i0) → num ; (j = i1) → add1 k}) (inS (repeat (pos n) j)) i
decodeSquare (negsuc n) i j    = hfill (λ k → λ { (j = i0) → num ; (j = i1) → add1 (~ k)}) (inS (repeat (negsuc n) j)) (~ i)

decode : (x : R) → I' x → num ≡ x
decode num          = repeat
decode (add1 i) y j =
  let n : ℤ
      n = unglue (i ∨ ~ i) y
  in
  hcomp
    (λ k → λ
      { (i = i0) → repeat (predSuc y k) j
      ; (i = i1) → repeat y j
      ; (j = i0) → num
      ; (j = i1) → add1 i
      })
    (decodeSquare n i j)

decodeEncode : (x : R) → (p : num ≡ x) → decode x (encode x p) ≡ p
decodeEncode x p = J (λ y q → decode y (encode y q) ≡ q) (λ _ → refl) p

repeat-winding : (p : Patch) → repeat (winding p) ≡ p
repeat-winding p = decodeEncode num p
  
merge : Patch × Patch → Patch × Patch
merge (f1 , f2) = (f2 , f1)

reconcile : (f1 f2 g1 g2 : Patch) → merge (f1 , f2) ≡ (g1 , g2)
            → g1 ∙ f1 ≡ g2 ∙ f2
reconcile f1 f2 g1 g2 p =
    g1 ∙ f1
        ≡⟨ cong (λ q → q ∙ f1) (sym (cong fst p)) ⟩
    f2 ∙ f1
        ≡⟨ cong₂ _∙_ (sym (repeat-winding f2)) (sym (repeat-winding f1)) ⟩
    repeat (winding f2) ∙ repeat (winding f1)
        ≡⟨ repeat-comm (winding f2) (winding f1) ⟩
    repeat (winding f1) ∙ repeat (winding f2)
        ≡⟨ cong₂ _∙_ (repeat-winding f1) (repeat-winding f2) ⟩
    f1 ∙ f2
        ≡⟨ cong (λ q → q ∙ f2) (cong snd p) ⟩
    g2 ∙ f2 ∎

symmetric : (f1 f2 g1 g2 : Patch) → merge (f1 , f2) ≡ (g1 , g2)
            → merge (f2 , f1) ≡ (g2 , g1)
symmetric f1 f2 g1 g2 p = cong (λ (x , y) → (y , x)) p

rebase : Patch × Patch → Patch
rebase (f1 , f2) = f1

merge≡rebase : (f1 f2 g1 g2 g : Patch)
               → merge (f1 , f2) ≡ (g1 , g2) → rebase (f1 , f2) ≡ g
               → g2 ∙ f2 ≡ g ∙ f2
merge≡rebase f1 f2 g1 g2 g p q = 
    g2 ∙ f2
        ≡⟨ cong (λ r → r ∙ f2) (sym (cong snd p)) ⟩
    f1 ∙ f2
        ≡⟨ cong (λ r → r ∙ f2) (q) ⟩
    g ∙ f2 ∎

rebase-symm : (f1 f2 g1 g2 h1 h2 : Patch)
              → merge (f1 , f2) ≡ (g1 , g2)
              → rebase (f1 , f2) ≡ h1 → rebase (f2 , f1) ≡ h2
              → h1 ∙ f2 ≡ h2 ∙ f1
rebase-symm f1 f2 g1 g2 h1 h2 p q r = 
    h1 ∙ f2 ≡⟨ {!!} ⟩
    f
    h2 ∙ f1 ∎
        

-- rebase : Patch × Patch → Patch
-- rebase (f1 , f2) = f2 ∙ f1
-- 
-- merge≡rebase : (f1 f2 g1 g2 g : Patch)
--                → merge (f1 , f2) ≡ (g1 , g2) → rebase (f1 , f2) ≡ g
--                → g1 ∙ f1 ≡ g
-- merge≡rebase f1 f2 g1 g2 g p q =
--     g1 ∙ f1 ≡⟨ cong (λ q → q ∙ f1) (sym (cong fst p)) ⟩
--     f2 ∙ f1 ≡⟨ q ⟩
--     g ∎
-- 
-- rebase-symm : (f1 f2 g : Patch)
--               → rebase (f1 , f2) ≡ g → rebase (f2 , f1) ≡ g
-- rebase-symm f1 f2 g p = 
--     rebase (f2 , f1)
--         ≡⟨ refl ⟩
--     f1 ∙ f2
--         ≡⟨ cong₂ _∙_ (sym (repeat-winding f1)) (sym (repeat-winding f2)) ⟩
--     repeat (winding f1) ∙ repeat (winding f2)
--         ≡⟨ repeat-comm (winding f1) (winding f2) ⟩
--     repeat (winding f2) ∙ repeat (winding f1)
--         ≡⟨ cong₂ _∙_ (repeat-winding f2) (repeat-winding f1) ⟩
--     f2 ∙ f1
--         ≡⟨ refl ⟩
--     rebase (f1 , f2)
--         ≡⟨ p ⟩
--     g ∎
