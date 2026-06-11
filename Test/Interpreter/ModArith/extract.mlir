// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i16}> ({
    %c243 = "mod_arith.constant"() <{ "value" = 243 : i16 }> : () -> !mod_arith.int<251 : i16>
    %ext = "mod_arith.extract"(%c243) : (!mod_arith.int<251 : i16>) -> i16
    "func.return"(%ext) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00f3#16]
