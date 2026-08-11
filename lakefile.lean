import Lake
open Lake DSL

package «pq-das»

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @
  "ea9916db809a18da16ad495eef5f8d03ca58f1b4"

@[default_target]
lean_lib PqDas
