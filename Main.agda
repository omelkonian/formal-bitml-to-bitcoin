module Main where

open import Compiler
open import Compiler.Example

open import SymbolicModel
open import ComputationalModel

open import Coherence

-- ** typechecking these needs around 10GB of RAM, fails on CI
-- open import Coherence.Example.Withdraw
-- open import Coherence.Example.TC

-- ** typechecking too slow and too memory-hungry even in local machine
-- open import Coherence.Example.WithdrawDSL
-- open import Coherence.Example.TC-DSL

open import Coherence.ValuePreservation
-- open import SecureCompilation.Lemma6

open import SecureCompilation
