#include "clang/Basic/LLVM.h"
#include "llvm/Support/raw_ostream.h"

#include "Formatter.hpp"

namespace fmt {

Formatter::Formatter ()
  : out(llvm::outs()), depth(0), spaces(0) {
}

Formatter::Formatter (llvm::raw_ostream &_out)
	: out(_out), depth(0), spaces(0) {
}

llvm::raw_ostream&
Formatter::line () {
  out << "\n";
  unsigned int d = this->depth;
  while (d--) {
	out << " ";
  }
  spaces = 0;
  return out;
}

llvm::raw_ostream&
Formatter::nobreak () {
  while (spaces > 0) {
	out << " ";
	spaces--;
  }
  return out;
}

void
Formatter::nbsp () {
  spaces++;
}

void
Formatter::indent () {
  this->depth += 2;
}
void
Formatter::outdent () {
  assert(this->depth >= 2);
  this->depth -= 2;
}

Formatter Formatter::default_output = Formatter();

struct NBSP;
const NBSP* nbsp;

Formatter&
operator<<(Formatter &out, const NBSP *_)
{
  out.nbsp();
  return out;
}

struct INDENT;
const INDENT* indent;

Formatter&
operator<<(Formatter &out, const INDENT *_)
{
  out.indent();
  return out;
}

struct OUTDENT;
const OUTDENT* outdent;

Formatter&
operator<<(Formatter &out, const OUTDENT *_)
{
  out.outdent();
  return out;
}

struct LPAREN;
const LPAREN* lparen;

Formatter&
operator<<(Formatter &out, const LPAREN *_)
{
  out.nobreak() << "(";
  out.indent();
  return out;
}

struct RPAREN;
const RPAREN* rparen;

Formatter&
operator<<(Formatter &out, const RPAREN *_)
{
  out.outdent();
  out.nobreak() << ")";
  return out;
}

struct LINE;
const LINE* line;
Formatter&
operator<<(Formatter &out, const LINE *_)
{
  out.line();
  return out;
}

Formatter&
operator<<(Formatter &out, const char *str)
{
  out.nobreak() << str;
  return out;
}

Formatter&
operator<<(Formatter &out, const std::string &str)
{
  out.nobreak() << str;
  return out;
}

}
