// Compiler for the JVM
//====================== 

import $file.cw02, cw02._
import $file.cw03, cw03._

val beginning = """
.class public XXX.XXX
.super java/lang/Object

.method public static write(I)V
  .limit locals 1
  .limit stack 2
  getstatic java/lang/System/out Ljava/io/PrintStream;
  iload 0
  invokevirtual java/io/PrintStream/println(I)V
  return
.end method

.method public static writes(Ljava/lang/String;)V
  .limit stack 2
  .limit locals 1
  getstatic java/lang/System/out Ljava/io/PrintStream;
  aload 0
  invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
  return
.end method

.method public static read()I
  .limit locals 10
  .limit stack 10

  ldc 0
  istore 1 ; this will hold our final integer
Label1:
  getstatic java/lang/System/in Ljava/io/InputStream;
  invokevirtual java/io/InputStream/read()I
  istore 2
  iload 2
  ldc 10 ; test for the newline delimiter for Unix
  isub
  ifeq Label2
  iload 2
  ldc 13 ; test for the carriage -return in Windows
  isub
  ifeq Label2
  iload 2
  ldc 32 ; the space delimiter
  isub
  ifeq Label2
  iload 2
  ldc 48 ; we have our digit in ASCII , have to subtract it from 48
  isub
  ldc 10
  iload 1
  imul
  iadd
  istore 1
  goto Label1
Label2:
  ; when we come here we have our integer computed
  ; in local variable 1
  iload 1
  ireturn
.end method


.method public static main([Ljava/lang/String;)V
   .limit locals 200
   .limit stack 200

; COMPILED CODE STARTS
"""

val end_of_program = "end_of_program"
val ending = """
end_of_program:
; COMPILED CODE ENDS
   return

.end method
"""

// fresh variables
var counter = -1
var current_loop_end = "DefaultEndLabel"  
var crt = ""

def Fresh(x: String) = {
  counter += 1
  x ++ "_" ++ counter.toString()
}

// for JVM instructions and labels
extension (sc: StringContext) {
    def i(args: Any*): String = "   " ++ sc.s(args:_*) ++ "\n"
    def l(args: Any*): String = sc.s(args:_*) ++ ":\n"
}


// environment where variables are stored
type Env = Map[String, Int]

// you can make changes to the arguments of the compile_*
// functions, but compile needs to take a block and a
// class_name as argument, and produce the j-file as 
// string.


def compile_op(op: String) = op match {
  case "+" => i"iadd"
  case "-" => i"isub"
  case "*" => i"imul"
}


def compile_aexp(a: AExp, env : Env) : String = a match {
  case Num(i) => i"ldc $i"
  case Var(s) => i"iload ${env(s)} \t\t; $s"
  case Aop(op, a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ compile_op(op)
}

def compile_bexp(b: BExp, env : Env, jmp: String) : String = b match {
  case True => ""
  case False => i"goto $jmp"
  case Bop("==", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpne $jmp"
  case Bop("!=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpeq $jmp"
  case Bop("<", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpge $jmp"
  case Bop(">", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmple $jmp"
  case Bop("<=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmpgt $jmp"
  case Bop(">=", a1, a2) => 
    compile_aexp(a1, env) ++ compile_aexp(a2, env) ++ i"if_icmplt $jmp"
  case And(b1, b2) => compile_bexp(b1, env, jmp) ++ compile_bexp(b2, env, jmp)
  case Or(b1, b2) => {
    val or_b1 = Fresh("or_b1")
    val or_b2 = Fresh("or_b2")
    (compile_bexp(b1, env, or_b1) ++ i"goto $or_b2" ++ l"$or_b1" ++
     compile_bexp(b2, env, jmp) ++ l"$or_b2")
  }
}

def compile_stmt(s: Stmt, env: Env) : (String, Env) = s match {
  case Skip => ("", env)
  case Assign(x, a) => {
    val index = env.getOrElse(x, env.keys.size)
    (compile_aexp(a, env) ++ i"istore $index \t\t; $x", env + (x -> index))
  } 
  case If(b, bl1, bl2) => {
    val if_else = Fresh("If_else")
    val if_end = Fresh("If_end")
    val (instrs1, env1) = compile_block(bl1, env)
    val (instrs2, env2) = compile_block(bl2, env1)
    (compile_bexp(b, env, if_else) ++
     instrs1 ++
     i"goto $if_end" ++
     l"$if_else" ++
     instrs2 ++
     l"$if_end", env2)
  }
  case While(b, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    val (instrs1, env1) = compile_block(bl, env)
    (l"$loop_begin" ++
     compile_bexp(b, env, loop_end) ++
     instrs1 ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }
  case Read(x) => {
    val index = env.getOrElse(x, env.keys.size)
    (i"invokestatic XXX/XXX/read()I" ++ i"istore $index \t\t; $x", env + (x -> index))
  }
  case WriteId(x) => 
    (i"iload ${env(x)} \t\t; $x" ++ 
     i"invokestatic XXX/XXX/write(I)V", env)
  case WriteString(x) => 
    (i"ldc $x \t\t; '$x'" ++ 
     i"invokestatic XXX/XXX/writes(Ljava/lang/String;)V", env)

  case For(x, from, upto, bl) => {
    val loop_begin = Fresh("Loop_begin")
    val loop_end = Fresh("Loop_end")
    current_loop_end = loop_end
    val index = env.getOrElse(x, env.keys.size)
    val (instrs1, env1) = compile_block(bl, env + (x -> index))
    val (one, two) = compile_stmt(Assign(x, Aop("+", Var(x), Num(1))), env1)

    (compile_aexp(from, env1) ++ i"istore $index \t\t; $x" ++ l"$loop_begin" ++
     compile_bexp(Bop("<=", Var(x), upto), env1, loop_end) ++ instrs1 ++
     one ++
     i"goto $loop_begin" ++
     l"$loop_end", env1)
  }

  case Break => {
    if (current_loop_end == "DefaultEndLabel") {
      (i"goto $end_of_program", env)
    } else {
      crt = current_loop_end
      current_loop_end = "DefaultEndLabel"
      (i"goto $crt", env)
      
  }
  }
}

def compile_block(bl: Block, env: Env) : (String, Env) = bl match {
  case Nil => ("", env)
  case s::bl => {
    val (instrs1, env1) = compile_stmt(s, env)
    val (instrs2, env2) = compile_block(bl, env1)
    (instrs1 ++ instrs2, env2)
  }
}

def compile(bl: Block, class_name: String) : String = {
  val instructions = compile_block(bl, Map.empty)._1
  (beginning ++ instructions ++ ending).replaceAllLiterally("XXX", class_name)
}

// println(compile(Stmts.parse_all(tokenise(os.read(os.pwd / "fib.while"))).head, "fib"))
// println(compile(Stmts.parse_all(tokenise(os.read(os.pwd / "factorial.while"))).head, "factorial"))
// println(compile(Stmts.parse_all(tokenise(os.read(os.pwd / "forloop1.while"))).head, "forloop1"))
// println(compile(Stmts.parse_all(tokenise(os.read(os.pwd / "forloop2.while"))).head, "forloop2"))
// println(compile(Stmts.parse_all(tokenise(os.read(os.pwd / "break.while"))).head, "break"))
