import Lake
open Lake DSL

package OrchardFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Orchard where

require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal" @ "main"

require poseidon_formal from git
  "https://github.com/oxarbitrage/poseidon-formal" @ "main"

require redpallas_formal from git
  "https://github.com/oxarbitrage/redpallas-formal" @ "main"

require sinsemilla_formal from git
  "https://github.com/oxarbitrage/sinsemilla-formal" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5450b53e5ddc75d46418fabb605edbf36bd0beb6"
