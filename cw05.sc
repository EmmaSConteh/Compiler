// // CW5

import $file.cw2_3, cw2_3._

var counter = -1

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// prelude
val prelude = """
declare i32 @printf(i8*, ...)

@.str_nl = private constant [2 x i8] c"\0A\00"
@.str_star = private constant [2 x i8] c"*\00"
@.str_space = private constant [2 x i8] c" \00"
@.str_int = private constant [3 x i8] c"%d\00"
@.str_c = private constant [3 x i8] c"%c\00"

define void @new_line() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_nl, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_star() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_star, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_space() #0 {
  %t0 = getelementptr [2 x i8], [2 x i8]* @.str_space, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0)
  ret void
}

define void @print_int(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_int, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x) 
  ret void
}

define void @print_char(i32 %x) {
  %t0 = getelementptr [3 x i8], [3 x i8]* @.str_c, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %t0, i32 %x)
  ret void
}

define void @skip() #0 {
  ret void
}

; END OF BUILT-IN FUNCTIONS (prelude)
"""


// Internal CPS language for FUN
abstract class KExp
abstract class KVal

case class KVar(s: String , ty: Ty = "UNDEF") extends KVal
case class KNum(i: Int) extends KVal
case class KFNum(i: Double) extends KVal
// case class KVarString(s: String) extends KVal
case class KOp(o: String, a1: KVal, a2: KVal) extends KVal
case class KCall(name: String, vs: List[KVal]) extends KVal
// case class KList(vs: List[ChConst]) extends KVal
case class KConst(c: String) extends KVal
case class KFConst(c: String) extends KVal
case object KVoid extends KVal
case class KVoid(v: KVal, e: KExp) extends KExp
case class KReturn(v: KVal) extends KExp



case class KLet(x: String, e1: KVal, e2: KExp) extends KExp {
  override def toString = s"LET $x = $e1 in \n$e2" 
}
case class KIf(x1: String, e1: KExp, e2: KExp) extends KExp {
  def p(e: KExp) = e.toString.replaceAll("(?m)^", "  ")

  override def toString = 
     s"IF $x1\nTHEN\n${p(e1)}\nELSE\n${p(e2)}"
}

// typing
type Ty = String
type TyEnv = Map[String, Ty]

// initial typing environment
val initialEnv = Map[String, Ty]("skip" -> "Void", "print_int" -> "Void", "print_char" -> "Void",
                                "print_space" -> "Void", "print_star" -> "Void", "new_line" -> "Void")

val typeConversion = Map("Int" -> "i32", "Double" -> "double", "Void" -> "void")

def typ_val(v: KVal, ts: TyEnv) : String = v match {
  case KVar(s, ty) => ty
  // case KVarString(s) => "String"
  case KNum(i) => "Int"
  case KFNum(i) => "Double"
  case KCall(o, vrs) => ts(o)
  case KConst(s) => "Int"
  case KFConst(s) => "Double"
  case KOp(o, v1, v2) => typ_val(v1, ts)
  // case KList(vs) => "List[ChConst]"
}

def typ_exp(a: KExp, ts: TyEnv) : KExp = ???


def CPS(e: Exp, ts: TyEnv)(k: (KVal, TyEnv) => (KExp, TyEnv)): (KExp, TyEnv) = e match {
  case Num(i) => k(KNum(i), ts)
  case FNum(i) => k(KFNum(i), ts)
  case ChConst(i) => k(KNum(i), ts)
  case Sequence(e1, e2) => 
    CPS(e1, ts)((x, y) => CPS(e2, y)((x2, y2) => k(x2, y2)))
  case Var(s) => {
    val local = ts.getOrElse(s"%$s", "UNDEF")
    val func = ts.getOrElse(s"@$s", "UNDEF")
    if (local == "UNDEF") {
      if (func == "UNDEF") {
        throw new Exception ("undefined")
      } else {
        val tmp_label = Fresh("tmp")
        val x = ts + (s"%$tmp_label" -> func)
        CPS(Var(tmp_label), x)((y, z) => {
          val ij = k(KVar(tmp_label, func), z)
          (KLet(tmp_label, KConst(s), ij._1), ij._2)
        })
      }
    } else {
      k(KVar(s, local), ts)
    }
  }
  case Aop(o, a1, a2) => {
    val tmp_label = Fresh("tmp")
    CPS(a1, ts)((e1, ts2) => {
      CPS(a2, ts2)((e2, ts3) => {
        val ij = k(KVar(tmp_label, typ_val(KOp(o, e1, e2), ts3)), ts3 + (s"%$tmp_label" -> typ_val(KOp(o, e1, e2), ts3)))
        (KLet(tmp_label, KOp(o, e1, e2), ij._1), ij._2)
      })
    })
  }
  case If(Bop(o, b1, b2), e1, e2) => {
    val tmp_label = Fresh("tmp")
    CPS(b1, ts)((x1, ts2) => {
      CPS(b2, ts2)((x2, ts3) => {
        val equation1 = CPS(e1, ts3)(k)
        val equation2 = CPS(e2, equation1._2)(k)
        (KLet(tmp_label, KOp(o, x1, x2), KIf(tmp_label, equation1._1, equation2._1)), ts3)
      })
    })
  }
  case Call(name, args) => {
    def aux(args: List[Exp], ts: TyEnv, vrs: List[KVal]) : (KExp, TyEnv) = args match {
      case Nil => {
        if(ts(name) == "Void") {
          val update = k(KVoid, ts)
          (KVoid(KCall(name, vrs), update._1), update._2)
        } else {
          val ty = ts(name)
          val tmp_label = Fresh("tmp")
          var update = k(KVar(tmp_label, ty), ts + (s"%$tmp_label" -> ty))
          (KLet(tmp_label, KCall(name, vrs), update._1), update._2)
        }
      }
      case a::as => CPS(a, ts)((x, y) => aux(as, y, vrs ::: List(x)))
    }
    aux(args, ts, Nil)
  }
  // case PrintString(name, vrs) => {
  //   val tmp_label = Fresh("tmp")
  //   val update = k(KVar(tmp_label, "List[ChConst]"), ts + (s"%$tmp_label" -> "List[ChConst]"))
  //   (KLet(tmp_label, KList(vrs), update._1), update._2)
  // }
}

def CPSi(e: Exp, ts: TyEnv) = CPS(e, ts)((e1, ts2) => (KReturn(e1), ts2))

extension (sc: StringContext) 
  def lab(args: Any*) = sc.s(args:_*) ++ ":\n" // label
  def indent(args: Any*) = "  " ++ sc.s(args:_*) ++ "\n" // indent
  def method(args: Any*) = sc.s(args:_*) ++ "\n" // method

def compile_op (op: String) = op match {
  case "+" => "add i32 "
  case "*" => "mul i32 "
  case "-" => "sub i32 "
  case "==" => "icmp eq i32 "
  case "!=" => "icmp ne i32 "
  case "<=" => "icmp sle i32 " // signed less or equal
  case "<" => "icmp slt i32 " // signed less than
  case "%" => "srem i32 " 
  case "/" => "sdiv i32 "
}

def compile_dop (op: String) = op match {
  case "+" => "fadd double "
  case "*" => "fmul double "
  case "-" => "fsub double "
  case "==" => "fcmp oeq double "
  case "!=" => "fcmp one double "
  case "<=" => "fcmp ole double "
  case "<" => "fcmp olt double "
  case "%" => "frem double "
  case "/" => "fdiv double "
}



def compile_val(v: KVal, ts: TyEnv) : String = v match {
  case KNum(i) => s"$i"
  case KFNum(i) => s"$i"
  // case KVarString(s) => s"$s"
  case KVar(s, ty) => s"%$s"
  case KConst(s) => s"load ${ typeConversion(typ_val(KConst(s), ts)) }, ${ typeConversion(typ_val(KConst(s), ts)) }* @$s"
  case KOp(op, x1, x2) => {
    if (typ_val(KOp(op, x1, x2), ts) == "Int") {
      s"${compile_op(op)} ${compile_val(x1, ts)}, ${compile_val(x2, ts)}" 
    } else {
      s"${compile_dop(op)} ${compile_val(x1, ts)}, ${compile_val(x2, ts)}" 
    }
  }
  case KCall(name, args) => {
    val conversion = typeConversion(typ_val(KCall(name, args), ts))
    s"call ${conversion} @$name(${ args.map({ case e1 => s"${ typeConversion(typ_val(e1, ts)) } ${ compile_val(e1, ts) }" }).mkString(", ") })"
  }
}

def compile_exp(a: KExp, ts: TyEnv) : String = a match {
  case KVoid(KCall(name, args), e) => {
    indent"call void @$name(${ args.map({ case e1 => s"${ typeConversion(typ_val(e1, ts)) } ${ compile_val(e1, ts) }" }).mkString(", ") })" ++ compile_exp(e, ts)
  }
  case KReturn(v) => {
    if (v == KVoid) {
      indent"ret void"
    } else{
      indent"ret ${ typeConversion(typ_val(v, ts)) } ${ compile_val(v, ts) }"
    }
  }
  case KLet(x, e1, e2) => 
    indent"%$x = ${compile_val(e1, ts)}" ++ compile_exp(e2, ts)
  case KIf(x, e1, e2) => {
    val if_branch = Fresh("if_branch")
    val else_branch = Fresh("else_branch")
    indent"br i1 %$x, label %$if_branch, label %$else_branch" ++
    lab"\n$if_branch" ++
    compile_exp(e1, ts) ++
    lab"\n$else_branch" ++ 
    compile_exp(e2, ts)
  }
}

def compile_decl(d: Decl, ts: TyEnv) : (String, TyEnv) = d match {
  case Def(name, args, typ, body) => {
    val argsmap = args.map(arg => (s"%${arg._1}" ->  arg._2))
    val c = CPSi(body, (ts + (name -> typ) ++ argsmap))
    (method"define ${ typeConversion(typ) } @$name (${ args.map({case (x, y) => s"${typeConversion(y)} %$x"}).mkString(", ") }) {" ++ compile_exp(c._1, c._2) ++ method"}\n", c._2)
  }
  case Main(body) => {
    val c = CPS(body, ts)((e1, t1) => (KReturn(KNum(0)), t1))
    (method"define i32 @main() {" ++ compile_exp(c._1, c._2) ++ method"}\n", c._2)
  }
  case Const(str, v) => {
    (method"@$str = global i32 $v", ts + (s"@$str" -> "Int"))
  }
  case FConst(str, v) => {
    (method"@$str = global double $v", ts + (s"@$str" -> "Double"))
  }
}

def compile(prog: List[Decl], ts: TyEnv = initialEnv) : String = prog match {
  case a::as => (compile_decl(a, ts))._1 ++ compile(as, (compile_decl(a, ts))._2)
  case _ => ""
}

val x = Block.parse_all(tokenise(os.read(os.pwd/"mand2.fun"))).head
println(compile(x))
