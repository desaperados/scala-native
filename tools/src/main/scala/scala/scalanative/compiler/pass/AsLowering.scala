package scala.scalanative
package compiler
package pass

import nir._, Inst.Let

/** Translates high-level casts to corresponding low-level instructions. */
class AsLowering extends Pass {
  private val conv: PartialFunction[(Type, Type), Conv] = {
    case (Type.I(w1), Type.I(w2)) if w1 > w2 => Conv.Sext
    case (Type.I(w1), Type.I(w2)) if w1 < w2 => Conv.Trunc
    case (Type.I(_), Type.F(_))              => Conv.Fptosi
    case (Type.F(_), Type.I(_))              => Conv.Sitofp
    case (Type.F(w1), Type.F(w2)) if w1 > w2 => Conv.Fpext
    case (Type.F(w1), Type.F(w2)) if w1 < w2 => Conv.Fptrunc
    case (Type.Ptr, _: Type.RefKind)         => Conv.Bitcast
    case (_: Type.RefKind, Type.Ptr)         => Conv.Bitcast
  }

  override def preInst = {
    case Let(n, Op.As(ty1, Of(v, ty2))) if ty1 == ty2 =>
      Seq(Let(n, Op.Copy(v)))

    case Let(n, Op.As(_: Type.RefKind, Of(v, _: Type.RefKind))) =>
      Seq(Let(n, Op.Copy(v)))

    case Let(n, Op.As(toty, Of(v, fromty)))
        if conv.isDefinedAt((toty, fromty)) =>
      Seq(Let(n, Op.Conv(conv((toty, fromty)), toty, v)))

    case inst @ Let(n, Op.As(to, Of(v, from))) =>
      util.unsupported(inst)
  }

  object Of {
    def unapply(v: Val): Some[(Val, Type)] = Some((v, v.ty))
  }
}

object AsLowering extends PassCompanion {
  def apply(ctx: Ctx) = new AsLowering
}
