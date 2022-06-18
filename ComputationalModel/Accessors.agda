module ComputationalModel.Accessors where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Accessors

open import Bitcoin

unquoteDecl _∙Value _∙value ∙value=_ = genAccessor _∙Value _∙value ∙value=_ (quote Value)
instance
  TxOutput∙Value : TxOutput ctx ∙Value
  TxOutput∙Value = ∙value= value

  ∃TxOutput∙Value : ∃TxOutput ∙Value
  ∃TxOutput∙Value = ∙value= λ where (_ , txo) → txo ∙value

  TxInput′∙Value : TxInput′ ∙Value
  TxInput′∙Value = ∙value= λ where ((_ , _ , T) at o) → (T ‼ᵒ o) ∙value
