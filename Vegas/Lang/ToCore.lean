import Vegas.Lang.Nullable

/-!
# Surface-to-core lowering

This module is the public ownership point for the `VegasLang -> VegasCore`
compiler edge. The concrete definitions currently live on `VegasLang.lower`
and `VegasLang.compileNullable`; this module records their role in the semantic
pipeline.
-/
