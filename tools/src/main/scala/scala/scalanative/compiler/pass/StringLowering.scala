package scala.scalanative
package compiler
package pass

import scala.collection.mutable
import compiler.analysis.ClassHierarchy._
import compiler.analysis.ClassHierarchyExtractors._
import util.ScopedVar, ScopedVar.scoped
import nir._

/** Maps string values to intrinsified global constants. */
class StringLowering(implicit top: Top) extends Pass {
  import StringLowering._

  private val strings = mutable.UnrolledBuffer.empty[String]

  /** Names of the fields of the java.lang.String in the memory layout order. */
  private val stringFieldNames = {
    val node  = ClassRef.unapply(Lib.String.name).get
    val names = node.allfields.sortBy(_.index).map(_.name)
    assert(names.length == 4, "java.lang.String is expected to have 4 fields.")
    names
  }

  override def preVal = {
    case Val.String(v) =>
      val StringCls    = ClassRef.unapply(Lib.String.name).get
      val CharArrayCls = ClassRef.unapply(Lib.CharArray.name).get

      val chars       = v.toCharArray
      val charsLength = Val.I32(chars.length)
      val charsConst = Val.Const(
        Val.Struct(
          Global.None,
          Seq(CharArrayCls.typeConst,
              charsLength,
              Val.I32(0), // padding to get next field aligned properly
              Val.Array(Type.I16, chars.map(c => Val.I16(c.toShort))))))

      val fieldValues = stringFieldNames.map {
        case Lib.StringValue          => charsConst
        case Lib.StringOffset         => Val.I32(0)
        case Lib.StringCount          => charsLength
        case Lib.StringCachedHashCode => Val.I32(v.hashCode)
        case _                        => util.unreachable
      }

      Val.Const(Val.Struct(Global.None, StringCls.typeConst +: fieldValues))
  }
}

object StringLowering extends PassCompanion {
  def apply(ctx: Ctx) = new StringLowering()(ctx.top)

  override val depends = Seq(Lib.String.name,
                             Lib.StringValue,
                             Lib.StringOffset,
                             Lib.StringCount,
                             Lib.StringCachedHashCode,
                             Lib.CharArray.name)
}
