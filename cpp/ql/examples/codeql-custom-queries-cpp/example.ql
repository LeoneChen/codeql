import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.security.FunctionWithWrappers
import semmle.code.cpp.models.interfaces.Alias
import semmle.code.cpp.models.interfaces.SideEffect
import semmle.code.cpp.pointsto.CallGraph
import semmle.code.cpp.ir.dataflow.ResolveCall

predicate isCompared(Expr e) {
  (
    exists(IfStmt is | is.getControllingExpr() = e)
    or
    exists(WhileStmt ws | ws.getControllingExpr() = e)
    or
    exists(ForStmt fs | fs.getControllingExpr() = e)
    or
    exists(ConditionalExpr ce | ce.getCondition() = e)
    or
    exists(ComparisonOperation co | co.getAnOperand() = e)
    or
    exists(BinaryLogicalOperation blo | blo.getAnOperand() = e)
    or
    exists(UnaryLogicalOperation ulo | ulo.getAnOperand() = e)
  ) and
  exists(SwitchStmt ss |
    ss.getControllingExpr() != e and ss.getControllingExpr() != e.getEnclosingElement()
  )
}

predicate isSwitched(Expr e) {
  exists(SwitchStmt ss, Expr ce | ce = ss.getControllingExpr() |
    ce = e or ce = e.getEnclosingElement()
  )
}

predicate isUnusualComparison(Expr e) {
  exists(SwitchStmt ss, Expr ce | ce = ss.getControllingExpr() |
    ce = e or ce = e.getEnclosingElement()
  )
  or
  exists(ComparisonOperation co, Expr another |
    co.getAnOperand() = e and another = co.getAnOperand() and another != e
  |
    another.getValue() != "0" and another.getValue() != "-1"
  )
}

class ErrnoFunction extends Function {
  ErrnoFunction() {
    exists(string nme | this.hasGlobalName(nme) | nme = ["errno", "__errno_location"])
  }
}

class ErrnoCall extends Call {
  ErrnoCall() { exists(ErrnoFunction func | resolvedCall(this, func)) }
}

class InterestingErrnoCall extends ErrnoCall {
  InterestingErrnoCall() {
    exists(ErrnoCall second |
      this != second and
      this.getLocation().getFile() = second.getLocation().getFile() and
      0 < (second.getLocation().getEndLine() - this.getLocation().getEndLine()) and
      (second.getLocation().getEndLine() - this.getLocation().getEndLine()) < 10 and
      isCompared(this.getEnclosingElement()) and
      isCompared(second.getEnclosingElement())
    )
    or
    isSwitched(this.getEnclosingElement())
  }
}

class GlibcFunctionWithWrappers extends FunctionWithWrappers {
  GlibcFunctionWithWrappers() {
    exists(string nme | this.hasGlobalName(nme) |
      nme =
        [
          "access",
          "chdir",
          "chmod",
          "close",
          "closedir",
          "dlclose",
          "dlerror",
          "dlopen",
          "dlsym",
          "exit",
          "fchmod",
          "fchown",
          "fclose",
          "fcntl",
          "fcntl64",
          "fdatasync",
          "fflush",
          "fgetc",
          "fgets",
          "fopen",
          "fopen64",
          "fprintf",
          "fputc",
          "fputs",
          "fread",
          "free",
          "fseek",
          "fstat",
          "fstat64",
          "ftell",
          "ftruncate",
          "ftruncate64",
          "fwrite",
          "getcwd",
          "getenv",
          "geteuid",
          "getpid",
          "getpwuid",
          "getrusage",
          "gettimeofday",
          "getuid",
          "isatty",
          "__isoc99_sscanf",
          "localtime_r",
          "lstat",
          "lstat64",
          "malloc",
          "malloc_usable_size",
          "mkdir",
          "mmap",
          "mmap64",
          "mremap",
          "munmap",
          "open",
          "open64",
          "opendir",
          "pclose",
          "popen",
          "pread",
          "pread64",
          "printf",
          "pthread_create",
          "pthread_join",
          "pthread_mutexattr_destroy",
          "pthread_mutexattr_init",
          "pthread_mutexattr_settype",
          "pthread_mutex_destroy",
          "pthread_mutex_init",
          "pthread_mutex_lock",
          "pthread_mutex_trylock",
          "pthread_mutex_unlock",
          "putc",
          "putchar",
          "puts",
          "pwrite",
          "pwrite64",
          "raise",
          "read",
          "readdir",
          "readdir64",
          "readlink",
          "realloc",
          "rewind",
          "rmdir",
          "setvbuf",
          "signal",
          "sleep",
          "stat",
          "stat64",
          "strdup",
          "symlink",
          "sysconf",
          "system",
          "time",
          "unlink",
          "usleep",
          "utime",
          "utimes",
          "write",
        ]
    )
  }

  override predicate interestingArg(int arg) { arg = 0 }
}

class GlibcCall extends Call {
  GlibcCall() {
    exists(GlibcFunctionWithWrappers func, Function wrapper |
      func.wrapperFunction(wrapper, _, _) and
      wrapper.getName().toLowerCase().matches("%" + func.getName().toLowerCase() + "%") and
      resolvedCall(this, wrapper) and
      (
        exists(MacroInvocation mi |
          mi.getAnExpandedElement() = this.(ExprCall).getExpr() and
          mi.getMacroName().toLowerCase().matches("%" + func.getName().toLowerCase() + "%")
        )
        or
        not this instanceof ExprCall
      )
    )
  }
}

// from GlibcFunctionWithWrappers func, Function wrapper, Call call
// where
//   func.wrapperFunction(wrapper, _, _) and
//   wrapper.getName().toLowerCase().matches("%" + func.getName().toLowerCase() + "%") and
//   resolvedCall(call, wrapper) and
//   (
//     exists(MacroInvocation mi |
//       mi.getAnExpandedElement() = call.(ExprCall).getExpr() and
//       mi.getMacroName().toLowerCase().matches("%" + func.getName().toLowerCase() + "%")
//     )
//     or
//     not call instanceof ExprCall
//   )
// select func, wrapper, call
class InterestingGlibcCall extends GlibcCall {
  InterestingGlibcCall() {
    exists(DataFlow::Node source, DataFlow::Node sink1, DataFlow::Node sink2 |
      (
        source.asExpr() = this
        or
        source.asExpr() = this.getAnArgument() and
        source.asExpr().getType() instanceof PointerType and
        not source.asExpr().getType() instanceof CharPointerType
      ) and
      DataFlow::localFlow(source, sink1) and
      DataFlow::localFlow(source, sink2) and
      sink1 != sink2 and
      exists(ComparisonOperation co1, Expr another1, ComparisonOperation co2, Expr another2 |
        co1.getAnOperand() = sink1.asExpr() and
        co1.getAnOperand() = another1 and
        another1 != sink1.asExpr() and
        co2.getAnOperand() = sink2.asExpr() and
        co2.getAnOperand() = another2 and
        another2 != sink2.asExpr()
      |
        another1.getValue() != another2.getValue()
      ) and
      isUnusualComparison(sink1.asExpr())
    )
  }
}

// from DataFlow::Node source, DataFlow::Node sink1, DataFlow::Node sink2
// where
//   (
//     source.asExpr() instanceof GlibcCall
//     or
//     exists(GlibcCall glibc_call |
//       source.asExpr() = glibc_call.getAnArgument() and
//       source.asExpr().getType() instanceof PointerType and
//       not source.asExpr().getType() instanceof CharPointerType
//     )
//   ) and
//   DataFlow::localFlow(source, sink1) and
//   DataFlow::localFlow(source, sink2) and
//   sink1 != sink2 and
//   exists(ComparisonOperation co1, Expr another1, ComparisonOperation co2, Expr another2 |
//     co1.getAnOperand() = sink1.asExpr() and
//     co1.getAnOperand() = another1 and
//     another1 != sink1.asExpr() and
//     co2.getAnOperand() = sink2.asExpr() and
//     co2.getAnOperand() = another2 and
//     another2 != sink2.asExpr()
//   |
//     another1.getValue() != another2.getValue()
//   ) and
//   isUnusualComparison(sink1.asExpr())
// select source, sink1, sink2
from Expr e
where
  e instanceof InterestingGlibcCall
  or
  e instanceof InterestingErrnoCall
select e
