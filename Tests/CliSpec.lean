import ProofForge.Cli

namespace Tests.CliSpec

-- build: names + --out; --target omitted
#guard
  match ProofForge.Cli.parseArgs ["build", "Counter", "--out", "build/tmp"] with
  | .ok o =>
      o.command == .build &&
        o.outDir.toString == "build/tmp" && o.names == #["Counter"]
  | .error _ => false

-- --target near is accepted as a no-op
#guard
  match ProofForge.Cli.parseArgs
      ["build", "Counter", "Pair", "--out", "out", "--target", "near"] with
  | .ok o =>
      o.command == .build &&
        o.outDir.toString == "out" && o.names == #["Counter", "Pair"]
  | .error _ => false

-- --module repeatable
#guard
  match ProofForge.Cli.parseArgs
      ["build", "--module", "MyContract.Counter", "--module", "MyContract.Pair"] with
  | .ok o => o.modules == #["MyContract.Counter", "MyContract.Pair"] && o.names.isEmpty
  | .error _ => false

-- --help / --version
#guard
  match ProofForge.Cli.parseArgs ["--help"] with
  | .ok o => o.help == true
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["build", "-h"] with
  | .ok o => o.help == true
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["--version"] with
  | .ok o => o.version == true
  | .error _ => false

#guard
  match ProofForge.Cli.parseArgs ["-V"] with
  | .ok o => o.version == true
  | .error _ => false

-- unknown flag (including the retired --backend)
#guard
  match ProofForge.Cli.parseArgs ["build", "--foo"] with
  | .ok _ => false
  | .error e => e == "unknown flag --foo"

#guard
  match ProofForge.Cli.parseArgs ["build", "--backend", "wat2wasm", "Counter"] with
  | .ok _ => false
  | .error e => e == "unknown flag --backend"

-- family name is not a target
#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "wasm"] with
  | .ok _ => false
  | .error e =>
      e == "wasm is a chain family, not a target; this build of pf supports NEAR only"

-- non-NEAR --target is an error
#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "svm", "--out", "build/sbpf", "Counter"] with
  | .ok _ => false
  | .error e =>
      e == "unknown target svm (this build of pf supports NEAR only)"

#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "evm"] with
  | .ok _ => false
  | .error e =>
      e == "unknown target evm (this build of pf supports NEAR only)"

#guard
  match ProofForge.Cli.parseArgs ["build", "--target", "solana"] with
  | .ok _ => false
  | .error e => e == "unknown target solana (this build of pf supports NEAR only)"

-- `init` is not a command
#guard
  match ProofForge.Cli.parseArgs ["init", "demo"] with
  | .ok o => o.command == .build && o.names == #["init", "demo"]
  | .error _ => false

-- fixture mapping (single-argument)
#guard ProofForge.Cli.fixtureModule "Counter" == `Examples.Counter
#guard ProofForge.Cli.fixtureModule "TokenShape" == `Examples.TokenShape
#guard ProofForge.Cli.fixtureModule "NearPromiseHandle" == `Examples.NearPromiseHandle
#guard ProofForge.Cli.fixtureModule "NearTokenErgonomics" == `Examples.NearTokenErgonomics
#guard ProofForge.Cli.fixtureModule "NearCtx" == `Examples.Near.NearCtx

end Tests.CliSpec
