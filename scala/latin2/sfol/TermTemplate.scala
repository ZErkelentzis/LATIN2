package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.{OMV, Term}

class TermTemplate(temp: Term, sublist: List[(OMV, Term, Int, TermTemplate)],
                   contemp: List[(GlobalName, Int, Int)] = List[(GlobalName, Int, Int)]()) {
  //continuoustemplate contains list of function operators, minimal numbers, maximal numbers
  //if nonempty, every triple is treated as a level of the continuous template. The absolute template is used as the
  //final level, allowing e.g. buildings terms of the form and or x
  //order is quantifiers, formula symbols, atomic formula symbols, term symbols.
  //not all levels have to be used. quantifiers can be skipped, and the absolute template can be used together with
  //criteria
  val continoustemplate: List[(GlobalName, Int, Int)] = contemp
  val template: Term = temp
  val substitutions: List[(OMV, Term, Int, TermTemplate)] = sublist
}