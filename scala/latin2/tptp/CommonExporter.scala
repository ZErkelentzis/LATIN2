package latin2.tptp

import leo.datastructures.TPTP.{AnnotatedFormula, Comment}

object CommonExporter {
  def splitFormulasAndComments(formulasAndComments: List[(AnnotatedFormula, Option[Comment])]): (Seq[AnnotatedFormula], Map[String, Seq[Comment]]) = {
    var formulas = Seq[AnnotatedFormula]()
    var comments = Map[String, Seq[Comment]]()
    for ((formula, comment) <- formulasAndComments) {
      comment match {
        case Some(comment) => comments += (formula.name -> Seq(comment))
      }
    }
    (formulas, comments)
  }
}
