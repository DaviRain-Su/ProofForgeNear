import ProofForge.Extract.IR
import ProofForge.Wasm.Near.Ops

namespace Tests.TargetOpsSpec

#guard ProofForge.Extract.IR.ValKind.arity (.near .reserved) == 0
#guard ProofForge.Extract.IR.ValKind.arity (.near .nearTokenAddOk) == 4
#guard ProofForge.Extract.IR.ValKind.arity (.near (.transientBuffer64Get 4)) == 1
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .reserved == 0

#guard !ProofForge.Extract.IR.OpExt.wellFormed (.near .reserved)
#guard ProofForge.Extract.IR.OpExt.wellFormed (.near (.logUtf8 "ok"))
#guard !ProofForge.Extract.IR.OpExt.wellFormed
  (.near (.logUtf8 (String.ofList (List.replicate 1025 'x'))))
#guard !ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val)
#guard !ProofForge.Wasm.Near.Ops.Op.wellFormed (.ext .reserved)
#guard !ProofForge.Extract.IR.Op.wellFormed (.ext (.near .reserved))

#guard ProofForge.Extract.IR.OpExt.values (.near (.logUtf8 "ok")) == #[]
#guard ProofForge.Extract.IR.OpExt.mapValues (fun v => v) (.near (.logUtf8 "ok")) ==
  .near (.logUtf8 "ok")

#guard
  ((.ext (.near .blockIndex) #[] : ProofForge.Extract.IR.Val).wellFormed
    ProofForge.Extract.IR.ValKind.arity)
#guard
  ((.ext (.near .reserved) #[] : ProofForge.Extract.IR.Val).wellFormed
    ProofForge.Extract.IR.ValKind.arity)

#guard
  let payload : ProofForge.Extract.IR.OpExt ProofForge.Extract.IR.Val :=
    .near (.promiseTransferDetached "aa" (.local 1) (.lit 0))
  let mapped := ProofForge.Extract.IR.OpExt.mapValues
    (fun
      | .local 1 => .local 0
      | v => v) payload
  mapped == .near (.promiseTransferDetached "aa" (.local 0) (.lit 0)) &&
    ProofForge.Extract.IR.OpExt.values payload == #[.local 1, .lit 0]

end Tests.TargetOpsSpec
