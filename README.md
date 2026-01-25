# HyperLogic
High order logic in the form of Hyper Doctrine

Actual

````bash
├── _CoqProject
├── LICENSE
├── Makefile
├── README.md
└── theories
    ├── Cat
    │   ├── Adjoint.v
    │   ├── CCC.v
    │   ├── Core.v
    │   ├── Fibration.v
    │   └── Functor.v
    ├── Logic
    └── Model

````



Planed

````bash

HyperLogic/                 <-- -R
├── _CoqProject             <-- Coq info
├── Makefile                <-- make and clean
└── theories/               <-- logic and math 
    ├── Cat/                <-- Categories
    │   ├── Core.v          <-- Setoid Category, Morphisms
    │   ├── Functor.v       <-- Functor definitions
    │   ├── Adjunction.v    <-- Adjunction, IsLeftAdjoint, IsRightAdjoint
    │   ├── CCC.v           <-- Cartesian Closed Category
    │   └── Fibration.v     <-- GoodFibration (Hiper Doctrine Basics)
    ├── Logic/              <-- Natural Deduction Logic (Syntax)
    │   ├── Base.v          <-- Canonic Base Cat (S & One), BMor
    │   ├── Syntax.v        <-- LogTyp, LogTerm 
    │   └── Typing.v        <-- Context, LogTyty (Judgments)
    └── Model/              <-- Semantics
        ├── SyntacticCat.v  <-- Lemmas
        └── Hyperdoctrine.v <-- Theorems
````
