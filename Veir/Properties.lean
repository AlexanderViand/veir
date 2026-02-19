module

public import Veir.OpCode
public import Veir.IR.Attribute

namespace Veir

public section

/--
  Properties of the `arith.constant` operation.
-/
structure ArithConstantProperties where
  value : Attribute
deriving Inhabited, Repr, Hashable

def ArithConstantProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String ArithConstantProperties := do
  if attrDict.size > 1 then
    throw s!"arith.constant: expected only 'value' property, but got {attrDict.size} properties"
  let some attr := attrDict["value".toUTF8]?
    | throw "arith.constant: missing 'value' property"
  return { value := attr }

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose]
def propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith_constant => ArithConstantProperties
| _ => Unit

instance (opCode : OpCode) : Inhabited (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

instance (opCode : OpCode) : Repr (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

instance (opCode : OpCode) : Hashable (propertiesOf opCode) := by
  unfold propertiesOf
  cases opCode <;> infer_instance

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (propertiesOf opCode) := by
  cases opCode
  case arith_constant => exact (ArithConstantProperties.fromAttrDict attrDict)
  all_goals exact (Except.ok ())

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict (opCode : OpCode) (props : propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode with
  | .arith_constant =>
    (Std.HashMap.emptyWithCapacity 2).insert "value".toUTF8 props.value
  | _ =>
    Std.HashMap.emptyWithCapacity 0

end
end Veir
