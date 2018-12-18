#include "clang/AST/Stmt.h"
#include "clang/AST/Decl.h"

class Outputter;

extern Outputter* defaultOutput;

void declToCoq(clang::ASTContext *ctxt, const clang::Decl* decl);

void stmtToCoq(clang::ASTContext *ctxt, const clang::Stmt* stmt);
