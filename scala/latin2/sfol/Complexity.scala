package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.{OMV, Term}
import lf.Propositions

import scala.collection.mutable

class Complexity(d: Int, tp: Term, varlist: List[(OMV, Term)], symlist: List[GlobalName], lquant: Int = 0, qalt: Int = 0,
                 bvar: List[(OMV, Term)] = List[(OMV, Term)]()) {
  //object to save term complexity. Can save depth (level of nesting), variables and symbols of a term
  //if a formula is described, sub term complexities are not taken into account here, as we finished using them in term
  //generation. Formula specific complexities are optional, to make term generation easier to program.
  //todo: Question is: Are the complexities of sub terms interesting for the evaluation of formulas? If yes, we might
  //todo: want to consider an access method to get the complexities of subterms, and store subterms here in a list.
  //todo: But is that useful at all?
  def depth = d
  def output: Term = tp
  //term generator saves variables, symbols etc unique, so we have information which symbols are contained, but not
  //how often. Variables are saved as OMV references, and include the variable type
  def variables = varlist
  def symbols = symlist
  //we save the last applied quantor of a formula here in flag form.
  //0 = no quantor, 1 = forall, 2 = exists, 3 = existsUnique
  def lastquant: Int = lquant
  def quantalt = qalt

  //number of different variables used in the term/formula
  def getvarnum() = variables.length
  //depending on theory, e.g. plus, minus, etc
  def getsymnum() = symbols.length
  //Quantifiers, Equal, etc
  def getalternations() = quantalt

  //extension to save formula information with standard values set to regular terms
  //todo: save number or different predicates/quantifiers/etc too? Where to save? In new list? Or together with
  //todo: symbols? Consideration of different kinds of complexity here required.
  //Formulas are terms that return a proposition. We use that here to determine if we have a Formula
  def isFormula(): Boolean = {
    if(output == Propositions.prop.term) true
    else false
  }
  //it can be interesting for generation and evaluation purposes to have a list of bound variables, as well
  //the unbound variables
  def boundVars = bvar
  def getUnbound() = variables.filterNot(bvar.contains(_))
  //todo: Quantifier alternations

  def getboundnum() = boundVars.length
  def getunboundnum() = getvarnum() - getboundnum()

}
