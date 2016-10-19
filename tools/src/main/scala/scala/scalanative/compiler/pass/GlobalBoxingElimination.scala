package scala.scalanative
package compiler
package pass

import scala.collection.mutable
import nir._, Inst.Let
import analysis.DominatorTree
import analysis.ControlFlow

/** Eliminates redundant box/unbox operations within
 *  a single method definition. This is quite simplistic approach
 *  but we need this to remove boxing around pointer operations
 *  that happen to have generic signatures.
 */
class GlobalBoxingElimination extends Pass {
  import GlobalBoxingElimination._

  override def preDefn = {
    case defn: Defn.Define =>
      val records = mutable.UnrolledBuffer.empty[Record]

      // Setup the dominator tree checks
      val cfg             = ControlFlow.Graph(defn.insts)
      val blockDomination = DominatorTree.build(cfg)

      val localToBlock =
        cfg.all.flatMap { block =>
          val params = block.params.map { local =>
            (local.name, block)
          }
          val insts = block.insts.collect {
            case Let(name, _) => (name, block)
          }
          params ++ insts
        }.toMap

      def isDominatedBy(dominated: Local, dominating: Local): Boolean = {
        val dominatedBlock  = localToBlock(dominated)
        val dominatingBlock = localToBlock(dominating)
        blockDomination(dominatedBlock).contains(dominatingBlock)
      }

      def canReuse(target: Local, reusedVal: Val): Boolean = {
        reusedVal match {
          case Val.Local(reusedLocal, _) => isDominatedBy(target, reusedLocal)
          case _                         => false
        }
      }

      // Original box elimination code
      val newinsts = defn.insts.map {
        case inst @ Let(to, op @ Op.Call(_, BoxRef(code), Seq(_, from))) =>
          records.collectFirst {
            // if a box for given value already exists, re-use the box
            case Box(rcode, rfrom, rto)
                if rcode == code && from == rfrom && canReuse(to, rto) =>
              Let(to, Op.Copy(rto))

            // if we re-box previously unboxed value, re-use the original box
            case Unbox(rcode, rfrom, rto)
                if rcode == code && from == rto && canReuse(to, rfrom) =>
              Let(to, Op.Copy(rfrom))
          }.getOrElse {
            // otherwise do actual boxing
            records += Box(code, from, Val.Local(to, op.resty))
            inst
          }

        case inst @ Let(to, op @ Op.Call(_, UnboxRef(code), Seq(_, from))) =>
          records.collectFirst {
            // if we unbox previously boxed value, return original value
            case Box(rcode, rfrom, rto)
                if rcode == code && from == rto && canReuse(to, rfrom) =>
              Let(to, Op.Copy(rfrom))

            // if an unbox for this value already exists, re-use unbox
            case Unbox(rcode, rfrom, rto)
                if rcode == code && from == rfrom && canReuse(to, rto) =>
              Let(to, Op.Copy(rto))
          }.getOrElse {
            // otherwise do actual unboxing
            records += Unbox(code, from, Val.Local(to, op.resty))
            inst
          }

        case inst =>
          inst
      }

      Seq(defn.copy(insts = newinsts))
  }
}

object GlobalBoxingElimination extends PassCompanion {
  private sealed abstract class Record
  private final case class Box(code: Char, from: nir.Val, to: nir.Val)
      extends Record
  private final case class Unbox(code: Char, from: nir.Val, to: nir.Val)
      extends Record

  object BoxRef {
    def unapply(value: Val): Option[Char] = value match {
      case Val.Global(n, _) => Lib.BoxTo.get(n)
      case _                => None
    }
  }
  object UnboxRef {
    def unapply(value: Val): Option[Char] = value match {
      case Val.Global(n, _) => Lib.UnboxTo.get(n)
      case _                => None
    }
  }

  def apply(ctx: Ctx) = new GlobalBoxingElimination
}
