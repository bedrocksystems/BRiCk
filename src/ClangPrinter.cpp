#include <clang/AST/ASTContext.h>
#include "ToCoq.hpp"

unsigned ClangPrinter::getCharWidth() const {
  return this->context_->getCharWidth();
}