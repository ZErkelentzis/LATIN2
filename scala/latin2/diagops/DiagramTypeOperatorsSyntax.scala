package latin2.diagops

import info.kwarc.mmt.api.uom.{TheoryScala, UnaryConstantScala}
import info.kwarc.mmt.api.{DPath, LocalName, utils}

object DiagramTypeOperatorsSyntax extends TheoryScala {
  val _base = DPath(utils.URI(Some("latin"), None, abs=true))
  val _name = LocalName("DiagramTypeOperatorsSyntax")

  object single_underscore_typeindexifier extends UnaryConstantScala(_path, "single_typeindexifier")
  object multi_underscore_typeindexifier extends UnaryConstantScala(_path, "multi_typeindexifier")

}
