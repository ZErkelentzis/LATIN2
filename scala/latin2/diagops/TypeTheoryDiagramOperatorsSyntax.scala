package latin2.diagops

import info.kwarc.mmt.api.uom.{TheoryScala, UnaryConstantScala}
import info.kwarc.mmt.api.{DPath, LocalName, utils}

object TypeTheoryDiagramOperatorsSyntax extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("TypeTheoryDiagramOperatorsSyntax")

  object single_underscore_typeindexifier extends UnaryConstantScala(_path, "single_typeindexifier")
  object multi_underscore_typeindexifier extends UnaryConstantScala(_path, "multi_typeindexifier")
}
