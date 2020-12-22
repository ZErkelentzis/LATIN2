package latin2.sfol

import info.kwarc.mmt.api.GlobalName
import info.kwarc.mmt.api.objects.{OMV, Term}

class GenCriteria(GenMode: Boolean = true, variables: Int = 3, literals: Int = 3, excludedTypes: List[Term] = List[Term](),
                  MinDepth: Int = 0, MaxDepth: Int = -1, escalate: Boolean = false, enum: Int = 100, senum: Int = 100,
                  Ratio: Int = 50, Formula: Boolean = false, TermCriteria: GenCriteria = null, qtop: Boolean = false,
                  qmin: Int = 0, qmax: Int = -1, quant: Int = 0, minfv: Int = 0, maxfv: Int = -1,
                  anum: Int = 100, skip: Boolean = false,
                  excludedfunctions: List[GlobalName] = List[GlobalName](), temp: TermTemplate = null,
                  logicmode: Boolean = false) {
  //form - whether the criteria are for formulas or terms
  //mode - Term generation: Forward or backward generation
  //tp - Term Generation: The requested term type
  //min: the minimal syntax tree depth to be generated
  //max: the maximal syntax tree depth
  //rat: aimed Ratio/Percentage of variables vs literals. 80 means there is a 80% chance a variable is used
  //tc: term generation criteria for formula generation
  //initialization criteria
  //number of variables and literals instantiated on generator call
  def varnum: Int = variables
  def litnum: Int = literals
  //if logic mode is used, propositional variables are instantiated
  //and only formulas without quantifiers can be generated
  def logmode: Boolean = logicmode
  //specifies if formulas or terms are generated
  def form: Boolean = Formula
  //mode: 0 = backward generation, 1 = forward generation
  def mode: Boolean = GenMode

  def excludedtypes: List[Term] = excludedTypes
  def exclusionlist: List[GlobalName] = excludedfunctions

  def escalation: Boolean = escalate
  def escdepth: Int = enum
  def sescdepth: Int = senum

  def atomicformulas: Int = anum
  def skipatomics: Boolean = skip
  def min: Int = MinDepth
  def max: Int = MaxDepth



  def rat: Int = Ratio
  def quantors: Int = quant
  def quanttop: Boolean = qtop
  def quantmax: Int = qmax
  def quantmin: Int = qmin
  def maxfreevars: Int = maxfv
  def minfreevars: Int = minfv
  def tc: GenCriteria = {
    if(Formula && (TermCriteria == null)){
      new GenCriteria()
    }
    else TermCriteria
  }
  //a list that allows the targeted exclusion of operators on both theory level and SFOL level

  //a template can come in 2 variants - an absolute template, and an infinite template
  //examples for absolute templates:
  //ax^2 + bx + c, where a, b, c are to be substituted with a literal
  //pred1(t1) and pred(t2) or (t3=t4). where t1 to t4 are terms
  //examples for infinite template
  //Horn Formula, CNF, sum.
  def template: TermTemplate = temp
}
