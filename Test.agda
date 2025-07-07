open import Relation.Binary.PropositionalEquality 

H : ∀ (A B : Set) (f g : A → B) (x y : A) → f x ≡ g y → B 
H A B f g x y refl = ?