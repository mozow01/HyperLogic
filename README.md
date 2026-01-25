# HyperLogic
High order logic in the form of Hyper Doctrine

Actual

````bash
├── _CoqProject
├── LICENSE
├── Makefile
├── Makefile.coq
├── Makefile.coq.conf
├── README.md
└── theories
    ├── Cat
    │   ├── Adjoint.glob
    │   ├── Adjoint.v
    │   ├── Adjoint.vo
    │   ├── Adjoint.vok
    │   ├── Adjoint.vos
    │   ├── CCC.glob
    │   ├── CCC.v
    │   ├── CCC.vo
    │   ├── CCC.vok
    │   ├── CCC.vos
    │   ├── Core.glob
    │   ├── Core.v
    │   ├── Core.vo
    │   ├── Core.vok
    │   ├── Core.vos
    │   ├── Fibration.v
    │   ├── Functor.glob
    │   ├── Functor.v
    │   ├── Functor.vo
    │   ├── Functor.vok
    │   └── Functor.vos
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
