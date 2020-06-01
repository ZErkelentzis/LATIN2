package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.Term

import scala.collection.mutable

class Complexity(d: Int, varlist: List[Term], symlist: List[GlobalName]) {
  //object to save term complexity. Can save depth (level of nesting), variables and symbols of a term
  def depth = d
  def variables = varlist
  def symbols = symlist

  def getvarnum() = variables.length
  def getsymnum() = symbols.length
}
