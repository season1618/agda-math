module Irrelevance where

postulate
    .irrAx : ∀ {l} {A : Set l} -> .A -> A

record IrrProduct (A B : Set) : Set where
    constructor _,_
    field
        fst : A
        .snd : B
