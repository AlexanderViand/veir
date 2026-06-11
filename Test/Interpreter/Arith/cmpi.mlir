// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1)}> ({
    %lhs = "arith.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %rhs = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
    %lt = "arith.cmpi"(%lhs, %rhs) <{"predicate" = 6 : i64}> : (i32, i32) -> i1
    %ge = "arith.cmpi"(%lhs, %rhs) <{"predicate" = 9 : i64}> : (i32, i32) -> i1
    "func.return"(%lt, %ge) : (i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1#1, 0x0#1]
