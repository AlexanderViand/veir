// RUN: veir-opt %s -p="mod-arith-to-arith,reconcile-cast" | filecheck %s

// A chain of mod_arith operations (add feeding into mul). Each op is lowered independently and
// eagerly packs its result back to !mod_arith.int and unpacks it again at the next op, producing a
// !mod_arith.int -> i32 -> !mod_arith.int round-trip cast between consecutive ops. reconcile-cast
// folds these intermediate round-trips, so the only surviving casts are the block-argument inputs
// and the final returned result.

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>, sym_name = "main"}> ({
    ^bb0(%0 : !mod_arith.int<7 : i32>, %1 : !mod_arith.int<7 : i32>, %2 : !mod_arith.int<7 : i32>):
      %a = "mod_arith.add"(%0, %1) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      %b = "mod_arith.mul"(%a, %2) : (!mod_arith.int<7 : i32>, !mod_arith.int<7 : i32>) -> !mod_arith.int<7 : i32>
      "func.return"(%b) : (!mod_arith.int<7 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// The three operands are unpacked from !mod_arith.int (input casts are kept) ...
// CHECK:      ^{{.*}}([[ARG0:%.*]] : !mod_arith.int<7 : i32>, [[ARG1:%.*]] : !mod_arith.int<7 : i32>, [[ARG2:%.*]] : !mod_arith.int<7 : i32>):
// CHECK-NEXT:   [[C0:%.*]] = "builtin.unrealized_conversion_cast"([[ARG0]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E0:%.*]] = "arith.extui"([[C0]]) : (i32) -> i33
// CHECK-NEXT:   [[C1:%.*]] = "builtin.unrealized_conversion_cast"([[ARG1]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[E1:%.*]] = "arith.extui"([[C1]]) : (i32) -> i33
// CHECK-NEXT:   [[QADD:%.*]] = "arith.constant"() <{"value" = 7 : i33}> : () -> i33
// CHECK-NEXT:   [[SUM:%.*]] = "arith.addi"([[E0]], [[E1]]) : (i33, i33) -> i33
// CHECK-NEXT:   [[SUMR:%.*]] = "arith.remui"([[SUM]], [[QADD]]) : (i33, i33) -> i33

// ... the add produces an i32 result via trunci, which flows directly into the mul's widening
// (the intermediate !mod_arith.int round-trip cast has been reconciled away) ...
// CHECK-NEXT:   [[ADD:%.*]] = "arith.trunci"([[SUMR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i33) -> i32
// CHECK-NEXT:   [[M0:%.*]] = "arith.extui"([[ADD]]) : (i32) -> i64
// CHECK-NEXT:   [[C2:%.*]] = "builtin.unrealized_conversion_cast"([[ARG2]]) : (!mod_arith.int<7 : i32>) -> i32
// CHECK-NEXT:   [[M1:%.*]] = "arith.extui"([[C2]]) : (i32) -> i64
// CHECK-NEXT:   [[QMUL:%.*]] = "arith.constant"() <{"value" = 7 : i64}> : () -> i64
// CHECK-NEXT:   [[PROD:%.*]] = "arith.muli"([[M0]], [[M1]]) : (i64, i64) -> i64
// CHECK-NEXT:   [[PRODR:%.*]] = "arith.remui"([[PROD]], [[QMUL]]) : (i64, i64) -> i64

// ... and only the final result is packed back into !mod_arith.int.
// CHECK-NEXT:   [[MUL:%.*]] = "arith.trunci"([[PRODR]]) <{"overflowFlags" = #arith.overflow<nuw>}> : (i64) -> i32
// CHECK-NEXT:   [[RES:%.*]] = "builtin.unrealized_conversion_cast"([[MUL]]) : (i32) -> !mod_arith.int<7 : i32>
// CHECK-NEXT:   "func.return"([[RES]]) : (!mod_arith.int<7 : i32>) -> ()
