import src.ERC20Lite

namespace spec.ERC20LiteSpec

open Verity
open Verity.EVM.Uint256

-- Each definition below is a `Prop` over (input, pre-state, post-state, …).
-- Discharging it in the proof file binds an obligation to the implementation;
-- mirroring it in a Foundry test ties the same obligation to the compiled
-- bytecode. The collection here is intentionally varied so the starter shows
-- four common shapes:
--   1. View / read-only specs   — `balanceOf_spec`, `totalSupply_spec`, `owner_spec`
--   2. Frame conditions          — `mint_owner_preserved`, `transfer_total_supply_preserved`,
--                                  `transferOwnership_supply_preserved`,
--                                  `transferOwnership_balances_preserved`
--   3. Authorized-path effects   — `transferOwnership_authorized_sets_owner`,
--                                  `transfer_balances_effect`
--   4. Negative access control   — `mint_unauthorized_no_change`,
--                                  `transferOwnership_unauthorized_owner_unchanged`

/-! ## Frame conditions
Properties of the form `s'.X = s.X` — the function does not touch part of state. -/

def transfer_total_supply_preserved (s s' : ContractState) : Prop :=
  s'.storage 2 = s.storage 2

def mint_owner_preserved (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = s.storageAddr 0

def transferOwnership_supply_preserved (s s' : ContractState) : Prop :=
  s'.storage 2 = s.storage 2

def transferOwnership_balances_preserved (account : Address) (s s' : ContractState) : Prop :=
  s'.storageMap 1 account = s.storageMap 1 account

/-! ## Read-only specs
Pure queries that return storage and leave state alone. -/

def balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 1 account

def totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 2

def owner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-! ## Authorized-path effects
Capturing what an authorized caller observes after a successful state write. -/

def transferOwnership_authorized_sets_owner
    (newOwner : Address) (s s' : ContractState) : Prop :=
  s.sender = s.storageAddr 0 → s'.storageAddr 0 = newOwner

-- Successful-path arithmetic for `transfer`. The single shared precondition
-- is "sender has enough balance"; the body splits on whether sender equals
-- recipient. Self-transfer is the well-known footgun: a naive implementation
-- that does `balance[sender] -= amount; balance[recipient] += amount` reads
-- a stale `balance[recipient]` after the debit, which can mint or burn
-- value when sender = recipient. The spec explicitly demands that the
-- *entire balance mapping* be left untouched in that branch — full mapping
-- equality, not just the sender's slot, so a faulty implementation that
-- happened to leave sender alone but corrupted some other balance would
-- still fail proof. The `if sender == toAddr then pure ()` short-circuit
-- in the contract is what makes that true. The non-self branch
-- additionally requires that crediting the recipient does not overflow
-- Uint256, and pins down the exact debit and credit.
def transfer_balances_effect
    (toAddr : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  amount.val ≤ (s.storageMap 1 s.sender).val →
    (s.sender = toAddr →
      s'.storageMap = s.storageMap) ∧
    (s.sender ≠ toAddr →
      (s.storageMap 1 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        s'.storageMap 1 s.sender = (s.storageMap 1 s.sender) - amount ∧
        s'.storageMap 1 toAddr = (s.storageMap 1 toAddr) + amount)

/-! ## Negative access control
The half of access control that says "non-owners cannot move state at all".
Together with the authorized-path effect this is the full access-control story
for `transferOwnership`; for `mint` it captures the security property that
unauthorized callers leave totalSupply and the recipient's balance untouched. -/

def mint_unauthorized_no_change
    (toAddr : Address) (_amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender ≠ s.storageAddr 0 →
    s'.storage 2 = s.storage 2 ∧
    s'.storageMap 1 toAddr = s.storageMap 1 toAddr

def transferOwnership_unauthorized_owner_unchanged
    (s s' : ContractState) : Prop :=
  s.sender ≠ s.storageAddr 0 → s'.storageAddr 0 = s.storageAddr 0

end spec.ERC20LiteSpec
