import Contracts.Common

namespace Tamago.Proof.EventSimp

open Verity

@[simp] theorem mapM_eventArg_toWord_nil (state : ContractState) :
    List.mapM Contracts.EventArg.toWord [] state =
      ContractResult.success [] state := by
  rfl

@[simp] theorem mapM_eventArg_toWord_one_pure
    (first : Uint256) (state : ContractState) :
    List.mapM Contracts.EventArg.toWord
        [Contracts.EventArg.word (Verity.pure first)]
        state =
      ContractResult.success [first] state := by
  rfl

@[simp] theorem mapM_eventArg_toWord_two_pure
    (first second : Uint256) (state : ContractState) :
    List.mapM Contracts.EventArg.toWord
        [Contracts.EventArg.word (Verity.pure first),
         Contracts.EventArg.word (Verity.pure second)]
        state =
      ContractResult.success [first, second] state := by
  rfl

@[simp] theorem mapM_eventArg_toWord_three_pure
    (first second third : Uint256) (state : ContractState) :
    List.mapM Contracts.EventArg.toWord
        [Contracts.EventArg.word (Verity.pure first),
         Contracts.EventArg.word (Verity.pure second),
         Contracts.EventArg.word (Verity.pure third)]
        state =
      ContractResult.success [first, second, third] state := by
  rfl

@[simp] theorem mapM_eventArg_toWord_four_pure
    (first second third fourth : Uint256) (state : ContractState) :
    List.mapM Contracts.EventArg.toWord
        [Contracts.EventArg.word (Verity.pure first),
         Contracts.EventArg.word (Verity.pure second),
         Contracts.EventArg.word (Verity.pure third),
         Contracts.EventArg.word (Verity.pure fourth)]
        state =
      ContractResult.success [first, second, third, fourth] state := by
  rfl

@[simp] theorem mapM_eventArg_toWord_five_pure
    (first second third fourth fifth : Uint256) (state : ContractState) :
    List.mapM Contracts.EventArg.toWord
        [Contracts.EventArg.word (Verity.pure first),
         Contracts.EventArg.word (Verity.pure second),
         Contracts.EventArg.word (Verity.pure third),
         Contracts.EventArg.word (Verity.pure fourth),
         Contracts.EventArg.word (Verity.pure fifth)]
        state =
      ContractResult.success [first, second, third, fourth, fifth] state := by
  rfl

end Tamago.Proof.EventSimp
