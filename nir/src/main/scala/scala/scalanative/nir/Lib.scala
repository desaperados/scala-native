package scala.scalanative
package nir

import Type._

object Lib {
  val Type =
    Struct(Global.Top("scala.scalanative.runtime.Type"), Seq(I32, Ptr))

  val CharArray = Class(Global.Top("scala.scalanative.runtime.CharArray"))

  val Object = Class(Global.Top("java.lang.Object"))

  val String               = Class(Global.Top("java.lang.String"))
  val StringValue          = String.name member "value" tag "field"
  val StringOffset         = String.name member "offset" tag "field"
  val StringCount          = String.name member "count" tag "field"
  val StringCachedHashCode = String.name member "cachedHashCode" tag "field"

  val Boolean   = Class(Global.Top("java.lang.Boolean"))
  val Character = Class(Global.Top("java.lang.Character"))
  val Byte      = Class(Global.Top("java.lang.Byte"))
  val Short     = Class(Global.Top("java.lang.Short"))
  val Integer   = Class(Global.Top("java.lang.Integer"))
  val Long      = Class(Global.Top("java.lang.Long"))
  val Float     = Class(Global.Top("java.lang.Float"))
  val Double    = Class(Global.Top("java.lang.Double"))

  val BoxesRunTime = Global.Top("scala.runtime.BoxesRunTime$")
  val RuntimeBoxes = Global.Top("scala.scalanative.runtime.Boxes$")

  val BoxOf: Map[Type, Type] = Map(
      (Boolean, Bool),
      (Character, I16),
      (Byte, I8),
      (Short, I16),
      (Integer, I32),
      (Long, I64),
      (Float, F32),
      (Double, F64)
  )

  val BoxTo: Map[Global, Char] = Seq(
      ('B', BoxesRunTime, "boxToBoolean_bool_class.java.lang.Boolean"),
      ('C', BoxesRunTime, "boxToCharacter_i16_class.java.lang.Character"),
      ('z', RuntimeBoxes, "boxToUByte_i8_class.java.lang.Object"),
      ('Z', BoxesRunTime, "boxToByte_i8_class.java.lang.Byte"),
      ('s', RuntimeBoxes, "boxToUShort_i16_class.java.lang.Object"),
      ('S', BoxesRunTime, "boxToShort_i16_class.java.lang.Short"),
      ('i', RuntimeBoxes, "boxToUInt_i32_class.java.lang.Object"),
      ('I', BoxesRunTime, "boxToInteger_i32_class.java.lang.Integer"),
      ('l', RuntimeBoxes, "boxToULong_i64_class.java.lang.Object"),
      ('L', BoxesRunTime, "boxToLong_i64_class.java.lang.Long"),
      ('F', BoxesRunTime, "boxToFloat_f32_class.java.lang.Float"),
      ('D', BoxesRunTime, "boxToDouble_f64_class.java.lang.Double")
  ).map {
    case (code, module, id) =>
      Global.Member(module, id) -> code
  }.toMap

  val UnboxTo: Map[Global, Char] = Seq(
      ('B', BoxesRunTime, "unboxToBoolean_class.java.lang.Object_bool"),
      ('C', BoxesRunTime, "unboxToChar_class.java.lang.Object_i16"),
      ('z', RuntimeBoxes, "unboxToUByte_class.java.lang.Object_i8"),
      ('Z', BoxesRunTime, "unboxToByte_class.java.lang.Object_i8"),
      ('s', RuntimeBoxes, "unboxToUShort_class.java.lang.Object_i16"),
      ('S', BoxesRunTime, "unboxToShort_class.java.lang.Object_i16"),
      ('i', RuntimeBoxes, "unboxToUInt_class.java.lang.Object_i32"),
      ('I', BoxesRunTime, "unboxToInt_class.java.lang.Object_i32"),
      ('l', RuntimeBoxes, "unboxToULong_class.java.lang.Object_i64"),
      ('L', BoxesRunTime, "unboxToLong_class.java.lang.Object_i64"),
      ('F', BoxesRunTime, "unboxToFloat_class.java.lang.Object_f32"),
      ('D', BoxesRunTime, "unboxToDouble_class.java.lang.Object_f64")
  ).map {
    case (code, module, id) =>
      Global.Member(module, id) -> code
  }.toMap
}
