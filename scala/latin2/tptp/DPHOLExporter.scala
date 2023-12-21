package latin2.tptp

import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.objects._
import info.kwarc.mmt.api.MPath
import leo.datastructures.TPTP._
import lf.{TypedPredicateSubtypes, TypedTerms}
import latin2.tptp.THFExporterUtil._
import latin2.tptp.DIHOLExporterUtil._

class DPHOLExporter extends DHOLExporter {
  override val priority: Int = 7
  override val theoryPath: info.kwarc.mmt.api.MPath = lf.DPHOL._path

  override def translate_type(t: Term): THF.Formula = t match {
    case TypedPredicateSubtypes.predsub(tp, _) => translate_type(tp)
    case _ => super.translate_type(t)
  }

  override def type_rel(tp: Term, left: THF.Formula, right: THF.Formula)(implicit usedVars: List[String]): THF.Formula = {
    tp match {
      case TypedPredicateSubtypes.predsub(tp, pred) =>
        THFAnd(THFAnd(type_rel(tp, left, right),
          THFApp(translate_term(pred), left)), THFApp(translate_term(pred), right))
      case _ => super.type_rel(tp, left, right)
    }
  }
}
