package scala.scalanative
package compiler
package pass

import scala.collection.mutable
import util.{Show, sh, unsupported}
import nir._, Shows._, Inst.Let

/** Verify that IR is well-formed. */
class Verify extends Pass {
  private val failures = mutable.UnrolledBuffer.empty[String]

  private def ensure(cond: Boolean, msg: => Show.Result): Unit =
    if (!cond) {
      failures += msg.toString
    }

  private def verifyOp(op: Op): Unit = op match {
    case Op.Conv(Conv.Sext, toty, v) =>
      val fromty = v.ty
      ensure(toty.isInstanceOf[Type.I],
             sh"can't sext to non-integer type $toty")
      ensure(fromty.isInstanceOf[Type.I],
             sh"can't sext from non-integer typ $fromty")

      val Type.I(fromw) = fromty
      val Type.I(tow)   = toty
      ensure(fromw < tow, sh"can't sext from $fromty to $toty")

    case _ =>
      ()
  }

  override def postAssembly = {
    case assembly =>
      if (failures.nonEmpty) {
        throw new Verify.Failure(failures)
      }
      assembly
  }

  override def preInst = {
    case inst @ Let(_, op) =>
      verifyOp(op)
      Seq(inst)
  }
}

object Verify extends PassCompanion {
  final case class Failure(msgs: Seq[String]) extends Exception {
    override def getMessage(): String =
      msgs.mkString("NIR is not well-formed:\n", "\n*", "")
  }

  def apply(ctx: Ctx) = new Verify
}
