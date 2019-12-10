package latin2.diagops

import info.kwarc.mmt.api.uom.{TheoryScala, UnaryConstantScala}
import info.kwarc.mmt.api.{DPath, LocalName, utils}

object LogicDiagramOperatorsSyntax extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("LogicDiagramOperatorsSyntax")

  object fol_typifier extends UnaryConstantScala(_path, "fol_typifier")
}
