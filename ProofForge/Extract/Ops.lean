import ProofForge.Extract.IR

namespace ProofForge.Extract.Ops

/-- Decoder-facing names over the extensible extraction dialect; no second Ops tree is created. -/
abbrev Cmp := IR.Cmp
abbrev Val := IR.Val
abbrev Op := IR.Op



private def nearLeaf (kind : ProofForge.Wasm.Near.Ops.ValKind) : Val :=
  .ext (.near kind) #[]


@[match_pattern] def Val.nearBlockIndex : Val := nearLeaf .blockIndex
@[match_pattern] def Val.nearBlockTimestamp : Val := nearLeaf .blockTimestamp
@[match_pattern] def Val.nearStorageUsage : Val := nearLeaf .storageUsage
@[match_pattern] def Val.nearPredecessor : Val := nearLeaf .predecessor
@[match_pattern] def Val.nearPredecessorLen : Val := nearLeaf .predecessorLen
@[match_pattern] def Val.nearPredecessorW1 : Val := nearLeaf .predecessorW1
@[match_pattern] def Val.nearPredecessorW2 : Val := nearLeaf .predecessorW2
@[match_pattern] def Val.nearPredecessorW3 : Val := nearLeaf .predecessorW3
@[match_pattern] def Val.nearPredecessorW4 : Val := nearLeaf .predecessorW4
@[match_pattern] def Val.nearPredecessorW5 : Val := nearLeaf .predecessorW5
@[match_pattern] def Val.nearPredecessorW6 : Val := nearLeaf .predecessorW6
@[match_pattern] def Val.nearPredecessorW7 : Val := nearLeaf .predecessorW7
@[match_pattern] def Val.nearAttachedDeposit : Val := nearLeaf .attachedDeposit
@[match_pattern] def Val.nearAttachedDepositW0 : Val := nearLeaf .attachedDepositW0
@[match_pattern] def Val.nearAttachedDepositW1 : Val := nearLeaf .attachedDepositW1
@[match_pattern] def Val.nearAccountBalance : Val := nearLeaf .accountBalance
@[match_pattern] def Val.nearAccountBalanceW0 : Val := nearLeaf .accountBalanceW0
@[match_pattern] def Val.nearAccountBalanceW1 : Val := nearLeaf .accountBalanceW1
@[match_pattern] def Val.nearTokenAddOk (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenAddOk) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenAddW0 (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenAddW0) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenAddW1 (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenAddW1) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenSubOk (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenSubOk) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenSubW0 (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenSubW0) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenSubW1 (leftLo leftHi rightLo rightHi : Val) : Val :=
  .ext (.near .nearTokenSubW1) #[leftLo, leftHi, rightLo, rightHi]
@[match_pattern] def Val.nearTokenMulU64Ok (valueLo valueHi factor : Val) : Val :=
  .ext (.near .nearTokenMulU64Ok) #[valueLo, valueHi, factor]
@[match_pattern] def Val.nearTokenMulU64W0 (valueLo valueHi factor : Val) : Val :=
  .ext (.near .nearTokenMulU64W0) #[valueLo, valueHi, factor]
@[match_pattern] def Val.nearTokenMulU64W1 (valueLo valueHi factor : Val) : Val :=
  .ext (.near .nearTokenMulU64W1) #[valueLo, valueHi, factor]
@[match_pattern] def Val.nearCurrentAccountId : Val := nearLeaf .currentAccountId
@[match_pattern] def Val.nearCurrentAccountIdLen : Val := nearLeaf .currentAccountIdLen
@[match_pattern] def Val.nearCurrentAccountIdW1 : Val := nearLeaf .currentAccountIdW1
@[match_pattern] def Val.nearCurrentAccountIdW2 : Val := nearLeaf .currentAccountIdW2
@[match_pattern] def Val.nearCurrentAccountIdW3 : Val := nearLeaf .currentAccountIdW3
@[match_pattern] def Val.nearCurrentAccountIdW4 : Val := nearLeaf .currentAccountIdW4
@[match_pattern] def Val.nearCurrentAccountIdW5 : Val := nearLeaf .currentAccountIdW5
@[match_pattern] def Val.nearCurrentAccountIdW6 : Val := nearLeaf .currentAccountIdW6
@[match_pattern] def Val.nearCurrentAccountIdW7 : Val := nearLeaf .currentAccountIdW7
@[match_pattern] def Val.nearEpochHeight : Val := nearLeaf .epochHeight
@[match_pattern] def Val.nearPrepaidGas : Val := nearLeaf .prepaidGas
@[match_pattern] def Val.nearUsedGas : Val := nearLeaf .usedGas
@[match_pattern] def Val.nearAccountLockedBalance : Val := nearLeaf .accountLockedBalance
@[match_pattern] def Val.nearAccountLockedBalanceW0 : Val := nearLeaf .accountLockedBalanceW0
@[match_pattern] def Val.nearAccountLockedBalanceW1 : Val := nearLeaf .accountLockedBalanceW1
@[match_pattern] def Val.nearSigner : Val := nearLeaf .signer
@[match_pattern] def Val.nearSignerLen : Val := nearLeaf .signerLen
@[match_pattern] def Val.nearSignerW1 : Val := nearLeaf .signerW1
@[match_pattern] def Val.nearSignerW2 : Val := nearLeaf .signerW2
@[match_pattern] def Val.nearSignerW3 : Val := nearLeaf .signerW3
@[match_pattern] def Val.nearSignerW4 : Val := nearLeaf .signerW4
@[match_pattern] def Val.nearSignerW5 : Val := nearLeaf .signerW5
@[match_pattern] def Val.nearSignerW6 : Val := nearLeaf .signerW6
@[match_pattern] def Val.nearSignerW7 : Val := nearLeaf .signerW7
@[match_pattern] def Val.nearSignerPk : Val := nearLeaf .signerPk
@[match_pattern] def Val.nearSignerPkW1 : Val := nearLeaf .signerPkW1
@[match_pattern] def Val.nearSignerPkW2 : Val := nearLeaf .signerPkW2
@[match_pattern] def Val.nearSignerPkW3 : Val := nearLeaf .signerPkW3
@[match_pattern] def Val.nearSignerPkW4 : Val := nearLeaf .signerPkW4
@[match_pattern] def Val.nearRandomSeed : Val := nearLeaf .randomSeed
@[match_pattern] def Val.nearRandomSeedW1 : Val := nearLeaf .randomSeedW1
@[match_pattern] def Val.nearRandomSeedW2 : Val := nearLeaf .randomSeedW2
@[match_pattern] def Val.nearRandomSeedW3 : Val := nearLeaf .randomSeedW3

@[match_pattern] def Val.nearSha256ResultW0 (capacity : Nat) : Val :=
  nearLeaf (.sha256ResultW0 capacity)
@[match_pattern] def Val.nearSha256ResultW1 (capacity : Nat) : Val :=
  nearLeaf (.sha256ResultW1 capacity)
@[match_pattern] def Val.nearSha256ResultW2 (capacity : Nat) : Val :=
  nearLeaf (.sha256ResultW2 capacity)
@[match_pattern] def Val.nearSha256ResultW3 (capacity : Nat) : Val :=
  nearLeaf (.sha256ResultW3 capacity)
@[match_pattern] def Val.nearKeccak256ResultW0 (capacity : Nat) : Val :=
  nearLeaf (.keccak256ResultW0 capacity)
@[match_pattern] def Val.nearKeccak256ResultW1 (capacity : Nat) : Val :=
  nearLeaf (.keccak256ResultW1 capacity)
@[match_pattern] def Val.nearKeccak256ResultW2 (capacity : Nat) : Val :=
  nearLeaf (.keccak256ResultW2 capacity)
@[match_pattern] def Val.nearKeccak256ResultW3 (capacity : Nat) : Val :=
  nearLeaf (.keccak256ResultW3 capacity)
@[match_pattern] def Val.nearKeccak512ResultW0 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW0 capacity)
@[match_pattern] def Val.nearKeccak512ResultW1 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW1 capacity)
@[match_pattern] def Val.nearKeccak512ResultW2 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW2 capacity)
@[match_pattern] def Val.nearKeccak512ResultW3 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW3 capacity)
@[match_pattern] def Val.nearKeccak512ResultW4 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW4 capacity)
@[match_pattern] def Val.nearKeccak512ResultW5 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW5 capacity)
@[match_pattern] def Val.nearKeccak512ResultW6 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW6 capacity)
@[match_pattern] def Val.nearKeccak512ResultW7 (capacity : Nat) : Val :=
  nearLeaf (.keccak512ResultW7 capacity)
@[match_pattern] def Val.nearRipemd160ResultW0 (capacity : Nat) : Val :=
  nearLeaf (.ripemd160ResultW0 capacity)
@[match_pattern] def Val.nearRipemd160ResultW1 (capacity : Nat) : Val :=
  nearLeaf (.ripemd160ResultW1 capacity)
@[match_pattern] def Val.nearRipemd160ResultW2 (capacity : Nat) : Val :=
  nearLeaf (.ripemd160ResultW2 capacity)
@[match_pattern] def Val.nearEcrecoverStatus (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverStatus capacity)
@[match_pattern] def Val.nearEcrecoverResultW0 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW0 capacity)
@[match_pattern] def Val.nearEcrecoverResultW1 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW1 capacity)
@[match_pattern] def Val.nearEcrecoverResultW2 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW2 capacity)
@[match_pattern] def Val.nearEcrecoverResultW3 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW3 capacity)
@[match_pattern] def Val.nearEcrecoverResultW4 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW4 capacity)
@[match_pattern] def Val.nearEcrecoverResultW5 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW5 capacity)
@[match_pattern] def Val.nearEcrecoverResultW6 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW6 capacity)
@[match_pattern] def Val.nearEcrecoverResultW7 (capacity : Nat) : Val :=
  nearLeaf (.ecrecoverResultW7 capacity)
@[match_pattern] def Val.nearEd25519VerifyOk (capacity : Nat) : Val :=
  nearLeaf (.ed25519VerifyOk capacity)


@[match_pattern] def Val.nearTransientBuffer64Get (capacity : Nat) (index : Val) : Val :=
  .ext (.near (.transientBuffer64Get capacity)) #[index]

@[match_pattern] def Val.nearStorageResultStatus (capacity : Nat) : Val :=
  nearLeaf (.storageResultStatus capacity)
@[match_pattern] def Val.nearStorageResultLength (capacity : Nat) : Val :=
  nearLeaf (.storageResultLength capacity)
@[match_pattern] def Val.nearStorageResultFits (capacity : Nat) : Val :=
  nearLeaf (.storageResultFits capacity)
@[match_pattern] def Val.nearStorageResultByte (capacity : Nat) (index : Val) : Val :=
  .ext (.near (.storageResultByte capacity)) #[index]
@[match_pattern] def Val.nearStorageResultNearTokenW0Strict : Val :=
  nearLeaf .storageResultNearTokenW0Strict
@[match_pattern] def Val.nearStorageResultNearTokenW1Strict : Val :=
  nearLeaf .storageResultNearTokenW1Strict

@[match_pattern] def Val.nearPromiseResultsCount : Val :=
  nearLeaf .promiseResultsCount
@[match_pattern] def Val.nearPromiseResultStatus (capacity : Nat) : Val :=
  nearLeaf (.promiseResultStatus capacity)
@[match_pattern] def Val.nearPromiseResultLength (capacity : Nat) : Val :=
  nearLeaf (.promiseResultLength capacity)
@[match_pattern] def Val.nearPromiseResultFits (capacity : Nat) : Val :=
  nearLeaf (.promiseResultFits capacity)
@[match_pattern] def Val.nearPromiseResultByte (capacity : Nat) (index : Val) : Val :=
  .ext (.near (.promiseResultByte capacity)) #[index]
@[match_pattern] def Val.nearPromiseResultBorshUInt64D
    (capacity : Nat) (fallback : Val) : Val :=
  .ext (.near (.promiseResultBorshUInt64D capacity)) #[fallback]
@[match_pattern] def Val.nearPromiseResultQuotedU128Valid (capacity : Nat) : Val :=
  nearLeaf (.promiseResultQuotedU128Valid capacity)
@[match_pattern] def Val.nearPromiseResultQuotedU128W0 (capacity : Nat) : Val :=
  nearLeaf (.promiseResultQuotedU128W0 capacity)
@[match_pattern] def Val.nearPromiseResultQuotedU128W1 (capacity : Nat) : Val :=
  nearLeaf (.promiseResultQuotedU128W1 capacity)

@[match_pattern] def Op.nearLogUtf8 (message : String) : Op :=
  .ext (.near (.logUtf8 message))

@[match_pattern] def Op.nearLogUtf8Bounded (capacity : Nat) (message : Array Val) : Op :=
  .ext (.near (.logUtf8Bounded capacity message))

@[match_pattern] def Op.nearStorageUnregisteredLog (account : Array Val) : Op :=
  .ext (.near (.storageUnregisteredLog account))

@[match_pattern] def Op.nearNep297StringData (standard version event : String)
    (capacity : Nat) (data : Array Val) : Op :=
  .ext (.near (.nep297StringData standard version event capacity data))

@[match_pattern] def Op.nearNep141FtMint (owner : Array Val) (amountLo amountHi : Val) : Op :=
  .ext (.near (.nep141FtMint owner amountLo amountHi))

@[match_pattern] def Op.nearNep141FtTransfer (oldOwner newOwner : Array Val)
    (amountLo amountHi : Val) : Op :=
  .ext (.near (.nep141FtTransfer oldOwner newOwner amountLo amountHi))

@[match_pattern] def Op.nearNep141FtBurn (owner : Array Val) (amountLo amountHi : Val) : Op :=
  .ext (.near (.nep141FtBurn owner amountLo amountHi))

@[match_pattern] def Op.nearNep141FtMintMemo (memoCapacity : Nat) (owner : Array Val)
    (amountLo amountHi : Val) (memo : Array Val) : Op :=
  .ext (.near (.nep141FtMintMemo memoCapacity owner amountLo amountHi memo))

@[match_pattern] def Op.nearNep141FtTransferMemo (memoCapacity : Nat)
    (oldOwner newOwner : Array Val) (amountLo amountHi : Val) (memo : Array Val) : Op :=
  .ext (.near (.nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo))

@[match_pattern] def Op.nearNep141FtBurnMemo (memoCapacity : Nat) (owner : Array Val)
    (amountLo amountHi : Val) (memo : Array Val) : Op :=
  .ext (.near (.nep141FtBurnMemo memoCapacity owner amountLo amountHi memo))

@[match_pattern] def Op.nearPromiseFunctionCallDetached
    (receiver method : String) (argsCapacity : Nat) (arguments : Array Val)
    (depositLo depositHi gas : Val) : Op :=
  .ext (.near (.promiseFunctionCallDetached receiver method argsCapacity arguments
    depositLo depositHi gas))

@[match_pattern] def Op.nearPromiseFunctionCallReturned
    (receiver method : String) (argsCapacity : Nat) (arguments : Array Val)
    (depositLo depositHi gas : Val) : Op :=
  .ext (.near (.promiseFunctionCallReturned receiver method argsCapacity arguments
    depositLo depositHi gas))

@[match_pattern] def Op.nearPromiseTransferDetached
    (receiver : String) (amountLo amountHi : Val) : Op :=
  .ext (.near (.promiseTransferDetached receiver amountLo amountHi))

@[match_pattern] def Op.nearPromiseTransferReturned
    (receiver : String) (amountLo amountHi : Val) : Op :=
  .ext (.near (.promiseTransferReturned receiver amountLo amountHi))

@[match_pattern] def Op.nearPromiseTransferAccountDetached
    (receiver : Array Val) (amountLo amountHi : Val) : Op :=
  .ext (.near (.promiseTransferAccountDetached receiver amountLo amountHi))

@[match_pattern] def Op.nearPromiseTransferAccountReturned
    (receiver : Array Val) (amountLo amountHi : Val) : Op :=
  .ext (.near (.promiseTransferAccountReturned receiver amountLo amountHi))

@[match_pattern] def Op.nearPromiseFtOnTransferReturned
    (receiver sender : Array Val) (amountLo amountHi : Val) (message : Array Val) : Op :=
  .ext (.near (.promiseFtOnTransferReturned receiver sender amountLo amountHi message))

@[match_pattern] def Op.nearPromiseFtOnTransferThenResolveReturned
    (receiver sender : Array Val) (amountLo amountHi : Val) (message : Array Val) : Op :=
  .ext (.near (.promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message))

@[match_pattern] def Op.nearPromiseCreateAccountDetached (receiver : String) : Op :=
  .ext (.near (.promiseCreateAccountDetached receiver))

@[match_pattern] def Op.nearPromiseCreateAccountReturned (receiver : String) : Op :=
  .ext (.near (.promiseCreateAccountReturned receiver))

@[match_pattern] def Op.nearPromiseDeployContractDetached
    (codeCapacity : Nat) (receiver : String) (code : Array Val) : Op :=
  .ext (.near (.promiseDeployContractDetached codeCapacity receiver code))

@[match_pattern] def Op.nearPromiseDeployContractReturned
    (codeCapacity : Nat) (receiver : String) (code : Array Val) : Op :=
  .ext (.near (.promiseDeployContractReturned codeCapacity receiver code))

@[match_pattern] def Op.nearPromiseStakeDetached
    (receiver : String) (publicKey : Array Val) (stakeLo stakeHi : Val) : Op :=
  .ext (.near (.promiseStakeDetached receiver publicKey stakeLo stakeHi))

@[match_pattern] def Op.nearPromiseStakeReturned
    (receiver : String) (publicKey : Array Val) (stakeLo stakeHi : Val) : Op :=
  .ext (.near (.promiseStakeReturned receiver publicKey stakeLo stakeHi))

@[match_pattern] def Op.nearPromiseAddKeyDetached
    (receiver : String) (publicKey : Array Val) (nonce : Val) : Op :=
  .ext (.near (.promiseAddKeyDetached receiver publicKey nonce))

@[match_pattern] def Op.nearPromiseAddKeyReturned
    (receiver : String) (publicKey : Array Val) (nonce : Val) : Op :=
  .ext (.near (.promiseAddKeyReturned receiver publicKey nonce))

@[match_pattern] def Op.nearPromiseDeleteKeyDetached
    (receiver : String) (publicKey : Array Val) : Op :=
  .ext (.near (.promiseDeleteKeyDetached receiver publicKey))

@[match_pattern] def Op.nearPromiseDeleteKeyReturned
    (receiver : String) (publicKey : Array Val) : Op :=
  .ext (.near (.promiseDeleteKeyReturned receiver publicKey))

@[match_pattern] def Op.nearPromiseDeleteAccountDetached
    (receiver beneficiary : String) : Op :=
  .ext (.near (.promiseDeleteAccountDetached receiver beneficiary))

@[match_pattern] def Op.nearPromiseDeleteAccountReturned
    (receiver beneficiary : String) : Op :=
  .ext (.near (.promiseDeleteAccountReturned receiver beneficiary))

@[match_pattern] def Op.nearPromiseYieldCreate
    (argsCapacity : Nat) (methodName : String) (arguments dataId : Array Val)
    (gas weight : Val) : Op :=
  .ext (.near (.promiseYieldCreate argsCapacity methodName arguments dataId gas weight))

@[match_pattern] def Op.nearPromiseYieldResume
    (idCapacity payloadCapacity : Nat) (dataId payload : Array Val) : Op :=
  .ext (.near (.promiseYieldResume idCapacity payloadCapacity dataId payload))

@[match_pattern] def Op.nearPromiseFunctionCallThenReturned
    (receiver childMethod callbackMethod : String)
    (childArgsCapacity callbackArgsCapacity : Nat)
    (childArguments callbackArguments : Array Val)
    (childDepositLo childDepositHi childGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
    childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAndThenReturned
    (leftReceiver leftMethod rightReceiver rightMethod callbackMethod : String)
    (leftArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments rightArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAndThenReturned
    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
    leftArguments rightArguments callbackArguments
    leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
    callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd3ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd3ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod
    leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity
    leftArguments midArguments rightArguments callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd4ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments fourthArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (fourthDepositLo fourthDepositHi fourthGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd4ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
    callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
    callbackArgsCapacity leftArguments midArguments rightArguments fourthArguments callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
    callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd5ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments fourthArguments fifthArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (fourthDepositLo fourthDepositHi fourthGas : Val)
    (fifthDepositLo fifthDepositHi fifthGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd5ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
      fourthArgsCapacity fifthArgsCapacity callbackArgsCapacity leftArguments midArguments
      rightArguments fourthArguments fifthArguments callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
    fifthDepositLo fifthDepositHi fifthGas callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd6ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (fourthDepositLo fourthDepositHi fourthGas : Val)
    (fifthDepositLo fifthDepositHi fifthGas : Val)
    (sixthDepositLo sixthDepositHi sixthGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd6ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod leftArgsCapacity midArgsCapacity
      rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
    fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
    callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd7ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (fourthDepositLo fourthDepositHi fourthGas : Val)
    (fifthDepositLo fifthDepositHi fifthGas : Val)
    (sixthDepositLo sixthDepositHi sixthGas : Val)
    (seventhDepositLo seventhDepositHi seventhGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd7ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
    fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
    seventhDepositLo seventhDepositHi seventhGas callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseFunctionCallAnd8ThenReturned
    (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
      eighthMethod callbackMethod : String)
    (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity : Nat)
    (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments eighthArguments callbackArguments : Array Val)
    (leftDepositLo leftDepositHi leftGas : Val)
    (midDepositLo midDepositHi midGas : Val)
    (rightDepositLo rightDepositHi rightGas : Val)
    (fourthDepositLo fourthDepositHi fourthGas : Val)
    (fifthDepositLo fifthDepositHi fifthGas : Val)
    (sixthDepositLo sixthDepositHi sixthGas : Val)
    (seventhDepositLo seventhDepositHi seventhGas : Val)
    (eighthDepositLo eighthDepositHi eighthGas : Val)
    (callbackDepositLo callbackDepositHi callbackGas : Val) : Op :=
  .ext (.near (.promiseFunctionCallAnd8ThenReturned
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
      eighthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments eighthArguments callbackArguments
    leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
    rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
    fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
    seventhDepositLo seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas
    callbackDepositLo callbackDepositHi callbackGas))

@[match_pattern] def Op.nearPromiseResultRead (capacity : Nat) (index : Val) : Op :=
  .ext (.near (.promiseResultRead capacity index))

@[match_pattern] def Op.nearTransientBuffer64Begin (capacity : Nat) : Op :=
  .ext (.near (.transientBuffer64Begin capacity))

@[match_pattern] def Op.nearTransientBuffer64Set
    (capacity : Nat) (index value : Val) : Op :=
  .ext (.near (.transientBuffer64Set capacity index value))

@[match_pattern] def Op.nearTransientBuffer64Finish (capacity : Nat) : Op :=
  .ext (.near (.transientBuffer64Finish capacity))

@[match_pattern] def Op.nearStorageRead
    (resultCapacity keyCapacity : Nat) (key : Array Val) : Op :=
  .ext (.near (.storageRead resultCapacity keyCapacity key))

@[match_pattern] def Op.nearStorageWrite
    (resultCapacity keyCapacity valueCapacity : Nat) (key value : Array Val) : Op :=
  .ext (.near (.storageWrite resultCapacity keyCapacity valueCapacity key value))

@[match_pattern] def Op.nearStorageRemove
    (resultCapacity keyCapacity : Nat) (key : Array Val) : Op :=
  .ext (.near (.storageRemove resultCapacity keyCapacity key))

@[match_pattern] def Op.nearStorageHasKey
    (resultCapacity keyCapacity : Nat) (key : Array Val) : Op :=
  .ext (.near (.storageHasKey resultCapacity keyCapacity key))

@[match_pattern] def Op.nearSha256Hash
    (resultCapacity inputCapacity : Nat) (input : Array Val) : Op :=
  .ext (.near (.sha256Hash resultCapacity inputCapacity input))

@[match_pattern] def Op.nearKeccak256Hash
    (resultCapacity inputCapacity : Nat) (input : Array Val) : Op :=
  .ext (.near (.keccak256Hash resultCapacity inputCapacity input))

@[match_pattern] def Op.nearKeccak512Hash
    (resultCapacity inputCapacity : Nat) (input : Array Val) : Op :=
  .ext (.near (.keccak512Hash resultCapacity inputCapacity input))

@[match_pattern] def Op.nearRipemd160Hash
    (resultCapacity inputCapacity : Nat) (input : Array Val) : Op :=
  .ext (.near (.ripemd160Hash resultCapacity inputCapacity input))

@[match_pattern] def Op.nearEcrecover
    (resultCapacity : Nat) (hash sig : Array Val) (v malleability : Val) : Op :=
  .ext (.near (.ecrecover resultCapacity hash sig v malleability))

@[match_pattern] def Op.nearEd25519Verify
    (resultCapacity : Nat) (sig msg pk : Array Val) : Op :=
  .ext (.near (.ed25519Verify resultCapacity sig msg pk))



private partial def walk (ops : Array Op) (predicate : Op → Bool) : Bool :=
  ops.any fun op =>
    predicate op ||
      match op with
      | .ite _ _ _ thn els => walk thn predicate || walk els predicate
      | .forBody _ body => walk body predicate
      | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walk ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walk ops fun | .forAccum .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walk ops fun | .indexSetLeaf .. | .indexSet .. => true | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walk ops fun | .storeField .. => true | _ => false


partial def isLangLeaf : Val → Bool
  | .local _ | .loopIx | .select .. | .bitAnd .. | .bitOr .. | .bitXor ..
  | .bitNot .. | .shiftL .. | .shiftR .. | .indexGet .. => true
  | .field base _ => isLangLeaf base
  | .ext _ operands => operands.any isLangLeaf
  | _ => false

private partial def hasSelectVal : Val → Bool
  | .select .. => true
  | .field base _ | .bitNot base => hasSelectVal base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      hasSelectVal lhs || hasSelectVal rhs
  | .indexGet base _ index _ _ => hasSelectVal base || hasSelectVal index
  | .ext _ operands => operands.any hasSelectVal
  | _ => false

private partial def isBitVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. => true
  | .field base _ => isBitVal base
  | .select _ lhs rhs thn els =>
      isBitVal lhs || isBitVal rhs || isBitVal thn || isBitVal els
  | .ext _ operands => operands.any isBitVal
  | _ => false

private def opValuesAny (predicate : Val → Bool) : Op → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      predicate value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
  | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ => predicate lhs || predicate rhs
  | .ext (.near _) => false
  | .errorTyped frame => frame.values.any predicate
  | .joinLocal _ | .forBody _ _ | .errorOverflow | .errorNamed _ => false



def hasLangOp (ops : Array Op) : Bool :=
  walk ops fun op =>
    match op with
    | .forAccum .. | .forBody .. | .indexSetLeaf .. | .indexSet .. | .errorNamed _ => true
    | _ => opValuesAny (fun value => isLangLeaf value || isBitVal value || hasSelectVal value) op


def hasNearEffect (ops : Array Op) : Bool :=
  walk ops fun
    | .ext (.near (.logUtf8 _))
    | .ext (.near (.logUtf8Bounded _ _))
    | .ext (.near (.storageUnregisteredLog _))
    | .ext (.near (.nep297StringData _ _ _ _ _))
    | .ext (.near (.nep141FtMint _ _ _))
    | .ext (.near (.nep141FtTransfer _ _ _ _))
    | .ext (.near (.nep141FtBurn _ _ _))
    | .ext (.near (.nep141FtMintMemo _ _ _ _ _))
    | .ext (.near (.nep141FtTransferMemo _ _ _ _ _ _))
    | .ext (.near (.nep141FtBurnMemo _ _ _ _ _))
    | .ext (.near (.promiseFunctionCallDetached _ _ _ _ _ _ _))
    | .ext (.near (.promiseFunctionCallReturned _ _ _ _ _ _ _))
    | .ext (.near (.promiseFtOnTransferReturned _ _ _ _ _))
    | .ext (.near (.promiseFtOnTransferThenResolveReturned _ _ _ _ _))
    | .ext (.near (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _))
    | .ext (.near (.transientBuffer64Begin _))
    | .ext (.near (.transientBuffer64Set _ _ _))
    | .ext (.near (.transientBuffer64Finish _))
    | .ext (.near (.storageRead _ _ _))
    | .ext (.near (.storageWrite _ _ _ _ _))
    | .ext (.near (.storageRemove _ _ _))
    | .ext (.near (.storageHasKey _ _ _))
    | .ext (.near (.sha256Hash _ _ _))
    | .ext (.near (.keccak256Hash _ _ _))
    | .ext (.near (.keccak512Hash _ _ _))
    | .ext (.near (.ripemd160Hash _ _ _))
    | .ext (.near (.ecrecover _ _ _ _ _))
    | .ext (.near (.ed25519Verify _ _ _ _)) => true
    | _ => false

end ProofForge.Extract.Ops
