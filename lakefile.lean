import Lake
open Lake DSL

package OrchardFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Orchard where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"

require poseidon_formal from git
  "https://github.com/oxarbitrage/poseidon-formal"

require redpallas_formal from git
  "https://github.com/oxarbitrage/redpallas-formal"

require sinsemilla_formal from git
  "https://github.com/oxarbitrage/sinsemilla-formal"
