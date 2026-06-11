// RUN: VEIR_ROUNDTRIP

// For backwards compatibility we keep accepting the legacy `i32` bitmask encoding
// (nsw = 1, nuw = 2) of the overflow flags on arith operations, but always print
// the MLIR-compatible `#arith.overflow<...>` attribute.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i32) -> i32, sym_name = "main"}> ({
  ^bb0(%a : i32, %b : i32):
    %addi = "arith.addi"(%a, %b) <{"overflowFlags" = 0 : i32}> : (i32, i32) -> i32
    %addi_nsw = "arith.addi"(%a, %b) <{"overflowFlags" = 1 : i32}> : (i32, i32) -> i32
    %addi_nuw = "arith.addi"(%a, %b) <{"overflowFlags" = 2 : i32}> : (i32, i32) -> i32
    %addi_nsw_nuw = "arith.addi"(%a, %b) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
    "func.return"(%addi) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw>}> : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32, i32) -> i32
// CHECK-NEXT: %{{.*}} = "arith.addi"(%{{.*}}, %{{.*}}) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i32, i32) -> i32
