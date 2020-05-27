package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.Term

class Complexity(d: Int, varlist: List[Term], symlist: List[GlobalName]) {
  //object to save term complexity. Can save depth (level of nesting), variables and symbols of a term
  //todo: change so that variables and symbols only contain unique values, as redundancies are useless and
  //todo: counterproductive here. Use hashmap here? Maybe as input, then to list
  def depth = d
  def variables = varlist
  def symbols = symlist

  def getdepth() = this.depth
  def getvarnum() = variables.length
  def getsymnum() = symbols.length
}
