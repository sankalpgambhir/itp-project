#!/usr/bin/scala-cli shebang
//> using scala 3.7.0
//> using dep "com.lihaoyi::os-lib:0.11.5-M9"
//> using dep "org.scala-lang.modules::scala-parser-combinators:2.4.0"

import os.*
import scala.util.matching.Regex

object ProcessDL:
  sealed trait OutputStage
  case object Rocq extends OutputStage
  case object Datalog extends OutputStage

  /**
    * Usage: datalog-preprocessing.sc [dir = pwd(*)] [outputStage = rocq(*)|datalog]
    *
    * @param args
    */
  def main(args: Array[String]): Unit =
    val baseDir = 
      if args.isEmpty then
        pwd
      else
        Path(args(0), pwd)
    val outDir  = baseDir / "out"
    os.makeDir.all(outDir)

    val outputStage =
      try
        args(1).toLowerCase() match
          case "rocq" => Rocq         
          case "coq" => Rocq
          case "dl" => Datalog
          case "datalog" => Datalog         
      catch
        case _ => Rocq

    val dlFiles  = FileUtils.findFiles(baseDir, ".dl")

    // input data for facts is stored in a "facts" directory
    // inline it to make the files self contained
    val factsDir = baseDir / "facts"
    val factsMap = FactLoader.load(factsDir)
    val factInliner  = FactInliner(factsMap)

    val dataRocqer = DataRocq

    val transformers: Seq[Transformation] = 
      Seq.empty
      ++ Seq(factInliner)
      ++ (if outputStage == Rocq then Seq(dataRocqer) else Seq.empty)

    val outExt = 
      outputStage match
        case Rocq => ".v"
        case Datalog => ".dl"

    // Process each .dl file through the pipeline
    dlFiles.foreach: dlPath =>
      val rawContent   = os.read(dlPath)
      val finalContent = transformers.foldLeft(rawContent)((c, tf) => tf.transform(c))
      os.write.over(outDir / (dlPath.baseName + outExt), finalContent)
      println(s"Processed: ${dlPath.last}")

/** Utility to find files by extension using os-lib. */
object FileUtils:
  def findFiles(dir: Path, ext: String): Seq[Path] =
    os.list(dir)
      .filter(p => isFile(p) && p.ext == ext.stripPrefix("."))

object FactLoader:
  def load(factsDir: Path): Map[String, Seq[String]] =
    if !os.exists(factsDir) then Map.empty
    else
      os.list(factsDir)
        .filter(p => isFile(p) && p.ext == "facts")
        .map: path =>
          val rel = path.baseName
          val lines = os.read.lines(path)
            // don't care about fluff in fact list
            // in fact this should be empty, in general
            .filterNot(l => l.trim.isEmpty || l.trim.startsWith("//"))
            .map: l =>
              val cols = l.trim.split("\\s+")
              // "0 1" |-> "rel(0, 1)."
              s"$rel(${cols.mkString(", ")})."
          rel -> lines
        .toMap

trait Transformation:
  def transform(input: String): String

/** Inlines facts from .fact files. */
case class FactInliner(facts: Map[String, Seq[String]]) extends Transformation:
  private val declPattern: Regex = "\\.decl\\w+\\s+(\\w+)\\s*\\(".r
  def transform(input: String): String =
    val relations = 
      input.linesIterator.map(DataRocq.DeclarationParser.decl)
        .collect { case Some(decl) => decl.name }
        .toSet
    val sb = StringBuilder(input.trim)
    for 
        rel <- relations
        relFacts <- facts.get(rel) 
    do
      sb.append("\n\n// Inlined facts for relation: ").append(rel)
      relFacts.foreach(f => sb.append("\n").append(f))
    sb.append("\n").toString

/**
  * Read and process a datalog file to extract the problem as a Rocq file
  * containing only inductive definitions.
  */
case object DataRocq extends Transformation:
  import scala.util.parsing.combinator.*

  sealed trait DLType:
    def toRocq: String = this match
      case NumberType => "Z"
  case object NumberType extends DLType

  case class Param(name: String, ty: DLType)

  case class PredDecl(name: String, params: Seq[Param])

  sealed trait Term:
    def freeVars: Set[String] = this match
      case Value(name) => Set(name)
      case Constant(value) => Set.empty
      case Plus(left, right) => left.freeVars ++ right.freeVars
      case Minus(left, right) => left.freeVars ++ right.freeVars
      case Times(left, right) => left.freeVars ++ right.freeVars
      case Div(left, right) => left.freeVars ++ right.freeVars
  case class Value(name: String) extends Term:
    override def toString: String = name
  case class Constant(value: String) extends Term:
    override def toString: String = value
  case class Plus(left: Term, right: Term) extends Term:
    override def toString: String = s"($left + $right)"
  case class Minus(left: Term, right: Term) extends Term:
    override def toString: String = s"($left - $right)"
  case class Times(left: Term, right: Term) extends Term:
    override def toString: String = s"($left * $right)"
  case class Div(left: Term, right: Term) extends Term:
    override def toString: String = s"($left / $right)"

  object Term:
    private var counter = 0
    def freshVar =
      counter += 1
      Value(s"freshvv$counter")

  sealed trait Formula:
    def freeVars: Set[String] = this match
      case Pred(name, args) => args.toSet.flatMap(_.freeVars)
      case Equality(left, right) => left.freeVars ++ right.freeVars
      case Lt(left, right) => left.freeVars ++ right.freeVars
      case Gt(left, right) => left.freeVars ++ right.freeVars
      case Lte(left, right) => left.freeVars ++ right.freeVars
      case Gte(left, right) => left.freeVars ++ right.freeVars
      case False | True => Set.empty
  case class Pred(name: String, args: Seq[Term]) extends Formula
  case class Equality(left: Term, right: Term) extends Formula
  case class Lt(left: Term, right: Term) extends Formula
  case class Gt(left: Term, right: Term) extends Formula
  case class Lte(left: Term, right: Term) extends Formula
  case class Gte(left: Term, right: Term) extends Formula
  case object False extends Formula
  case object True extends Formula

  case class Clause(head: Formula, body: Seq[Formula]):
    def freeVars: Set[String] =
      head.freeVars ++ body.flatMap(_.freeVars)

  class DeclarationParser extends RegexParsers:
    override def skipWhitespace = true

    def param: Parser[Param] = 
      "[a-zA-Z0-9]+".r ~ ":" ~ "[a-zA-Z]+".r ^^ {
        case name ~ _ ~ tpe => Param(name, tpe match {
          case "number" => NumberType
          case _ => throw new IllegalArgumentException(s"Unknown type: $tpe")
        })
      }

    def paramList: Parser[Seq[Param]] = repsep(param, ", ")

    def declaration: Parser[PredDecl] = 
      ".decl".r ~ "[a-zA-Z0-9]+".r ~ "(" ~ paramList ~ ")" ^^ {
        case _ ~ name ~ _ ~ params ~ _ => PredDecl(name, params)
      }

  object DeclarationParser extends DeclarationParser:
    def decl(line: String): Option[PredDecl] =
      parse(declaration, line) match {
        case Success(result, _) => Some(result)
        case _ => None
      }

  class ClauseParser extends RegexParsers:
    override def skipWhitespace = true

    def varName: Parser[String] = "[a-zA-Z][a-zA-Z0-9]*".r
    def predicateName: Parser[String] = varName

    // term parsers
    def freshVariable: Parser[Term] = 
      "_".r ^^ (_ => Term.freshVar)
    def variableTerm : Parser[Term] = varName ^^ Value.apply
    def constantTerm: Parser[Term] = 
      "[0-9]+".r ^^ (num => Constant(num))
    def valueTerm: Parser[Term] = 
      constantTerm | freshVariable | variableTerm
    def addTerm: Parser[Term] = valueTerm ~ "+" ~ valueTerm ^^ {
      case left ~ _ ~ right => Plus(left, right)
    }
    def subTerm: Parser[Term] = valueTerm ~ "-" ~ valueTerm ^^ {
      case left ~ _ ~ right => Minus(left, right)
    }
    def mulTerm: Parser[Term] = valueTerm ~ "*" ~ valueTerm ^^ {
      case left ~ _ ~ right => Times(left, right)
    }
    def divTerm: Parser[Term] = valueTerm ~ "/" ~ valueTerm ^^ {
      case left ~ _ ~ right => Div(left, right)
    }
    def term: Parser[Term] = 
      addTerm | subTerm | mulTerm | divTerm | valueTerm

    // formula parsers

    def predicate : Parser[Formula] = 
      predicateName ~ "(" ~ repsep(term, ",") ~ ")" ^^ {
        case name ~ _ ~ args ~ _ => Pred(name, args)
      }
    def lt: Parser[Formula] = term ~ "<" ~ term ^^ {
      case left ~ _ ~ right => Lt(left, right)
    }
    def gt: Parser[Formula] = term ~ ">" ~ term ^^ {
      case left ~ _ ~ right => Gt(left, right)
    }
    def lte: Parser[Formula] = term ~ "<=" ~ term ^^ {
      case left ~ _ ~ right => Lte(left, right)
    }
    def gte: Parser[Formula] = term ~ ">=" ~ term ^^ {
      case left ~ _ ~ right => Gte(left, right)
    }
    def equality: Parser[Formula] = term ~ "=" ~ term ^^ {
      case left ~ _ ~ right => Equality(left, right)
    }
    def falseFormula: Parser[Formula] = "false" ^^ (_ => False)
    def trueFormula: Parser[Formula] = "true" ^^ (_ => True)

    def formula: Parser[Formula] = 
      predicate | lt | gt | lte | gte | equality | falseFormula | trueFormula

    def atomicFormula: Parser[Formula] = 
      predicate | falseFormula | trueFormula

    def factClause: Parser[Clause] = 
      atomicFormula ~ "." ^^ {
        case head ~ _ => Clause(head, Seq.empty)
      }

    def bodiedClause: Parser[Clause] = 
      atomicFormula ~ ":-" ~ repsep(formula, ",") ^^ {
        case head ~ _ ~ body => Clause(head, body)
      }

    def clauseParser: Parser[Clause] = factClause | bodiedClause

  object ClauseParser extends ClauseParser:
    def clause(line: String): Option[Clause] =
      parse(clauseParser, line) match {
        case Success(result, _) => Some(result)
        case _ => None
      }

  def transform(input: String): String =
    // collect predicate decls
    // these are what we need to make blocks for
    val decls = 
      input.linesIterator
        .map(DeclarationParser.decl)
        .collect:
          case Some(decl) => decl
        .toSeq
    val clauses = 
      input.linesIterator
        .map(ClauseParser.clause)
        .collect:
          case Some(clause) => clause
        .toSeq
        .groupBy(_.head match
          case Pred(name, _) => name
          case _ => throw new IllegalArgumentException("Clause head must be a predicate")
        )

    val rocqDecls = decls.map { decl =>
      // collect the clauses for this predicate
      val predClauses = clauses.getOrElse(decl.name, Seq.empty)
      val declLine =
        val paramTypes = decl.params.map(_.ty.toRocq)
        val tyString =
          if paramTypes.isEmpty then "Prop"
          else s"${paramTypes.mkString(" -> ")} -> Prop"
        s"Inductive ${decl.name}: $tyString :=\n"
      val clauseLines = {
        predClauses
          .iterator
          .zipWithIndex
          .map: (clause, i) =>
            val freeVars = clause.freeVars 
            val constrName = s"${decl.name}__$i"
            val termArgs = 
              if freeVars.isEmpty then
                ""
              else
                s"{${freeVars.mkString(" ")}}"
            val rHead = clause.head match {
              case Pred(name, args) => s"($name ${args.mkString(" ")})"
              case _ => throw new IllegalArgumentException("Clause head must be a predicate")
            }
            val rBody = 
              clause.body.map: f =>
                f match
                  case Pred(name, args) => s"($name ${args.mkString(" ")})"
                  case Equality(left, right) => s"$left = $right"
                  case Lt(left, right) =>  s"Z.lt $left $right"
                  case Gt(left, right) =>  s"Z.gt $left $right"
                  case Lte(left, right) => s"Z.le $left $right"
                  case Gte(left, right) => s"Z.ge $left $right"
                  case False => "False"
                  case True => "True"
            val typeStr =
              if rBody.isEmpty then
                rHead
              else
                rBody.mkString("", " -> ", s" -> $rHead")
            s"  | $constrName $termArgs : $typeStr"
      }
      s"$declLine${clauseLines.mkString("\n")}\n  .\n"
    }
      
    val imports =
      "Require Import ZArith.\n"

    imports + "\n" +
    rocqDecls.mkString("\n") + 
    "\n"
    