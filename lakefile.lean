import Lake
open Lake DSL

package kevros where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib KevrosCorrect where
  srcDir := "."
