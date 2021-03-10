package latin2.proving

import info.kwarc.mmt.api.LocalName
import info.kwarc.mmt.api.modules.ModuleOrLink
import info.kwarc.mmt.api.symbols.{Declaration, DerivedDeclaration, Elaboration, ParametricTheoryLike, StructuralFeature, StructuralFeatureRule}
import info.kwarc.mmt.api.uom.ExtendedSimplificationEnvironment
/*
class printType extends  StructuralFeature("printMeta") with ParametricTheoryLike {
  /**
    * defines the outer perspective of a derived declaration
    *
    * @param parent the containing module
    * @param dd     the derived declaration
    */
 override def elaborate(parent: ModuleOrLink, dd:  DerivedDeclaration)(implicit env:  Option[ExtendedSimplificationEnvironment]): Elaboration = {

    new Elaboration {
      override def domain: List[LocalName] = {

      }
      override def getO(name:  LocalName): Option[Declaration] = {

      }
}
  }
} */