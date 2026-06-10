// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
      %1 = "mod_arith.extract"(%0) : (!mod_arith.int<17 : i32>) -> i32
      %2 = "mod_arith.encapsulate"(%1) : (i32) -> !mod_arith.int<17 : i32>
      %3 = "mod_arith.reduce"(%2) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      %4 = "mod_arith.mac"(%3, %3, %3) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()


// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %{{.*}} = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
// CHECK-NEXT:         %{{.*}} = "mod_arith.extract"(%{{.*}}) : (!mod_arith.int<17 : i32>) -> i32
// CHECK-NEXT:         %{{.*}} = "mod_arith.encapsulate"(%{{.*}}) : (i32) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:         %{{.*}} = "mod_arith.reduce"(%{{.*}}) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:         %{{.*}} = "mod_arith.mac"(%{{.*}}, %{{.*}}, %{{.*}}) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
// CHECK-NEXT:         "func.return"() : () -> ()
// CHECK-NEXT:     }) : () -> ()
// CHECK-NEXT: }) : () -> ()
