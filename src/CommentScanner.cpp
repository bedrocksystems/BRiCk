/*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 */
#include "CommentScanner.hpp"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclBase.h>
#include <list>

using namespace clang;
using namespace comment;

static SourceLocation
getStartSourceLocWithComment(clang::ASTContext *ctxt, const Decl *d) {
    auto comment = ctxt->getRawCommentForDeclNoCache(d);
    return comment ?
#if CLANG_VERSION_MAJOR >= 8
               comment->getBeginLoc() :
               d->getBeginLoc();
#else
               comment->getLocEnd() :
               d->getLocStart();
#endif
}

static Decl *
getPreviousDeclInContext(const Decl *d) {
    auto dc = d->getLexicalDeclContext();

    Decl *prev = nullptr;
    for (auto it : dc->decls()) {
        if (it == d) {
            return prev;
        } else {
            prev = it;
        }
    }
    return nullptr;
}

static SourceLocation
getPrevSourceLoc(SourceManager &sm, const Decl *d) {
    auto pd = getPreviousDeclInContext(d);
#if CLANG_VERSION_MAJOR >= 8
    return (pd && pd->getEndLoc().isValid()) ?
               pd->getEndLoc()
#else
    return (pd && pd->getLocEnd().isValid()) ?
               pd->getLocEnd()
#endif
               :
               sm.getLocForStartOfFile(
                   sm.getFileID(d->getSourceRange().getBegin()));
}

CommentScanner
CommentScanner::decl_comments(const clang::Decl *decl,
                              clang::ASTContext *ctxt) {
    SourceManager &sm = ctxt->getSourceManager();
    auto start = getPrevSourceLoc(sm, decl);
    auto end = getStartSourceLocWithComment(ctxt, decl);

    llvm::errs() << "start/end: " << start.printToString(sm) << " "
                 << end.printToString(sm) << "\n";

    if (start.isValid() && end.isValid()) {
        llvm::errs() << StringRef(sm.getCharacterData(start),
                                  sm.getCharacterData(end) -
                                      sm.getCharacterData(start))
                     << "\n";
        return comment::CommentScanner(
            StringRef(sm.getCharacterData(start),
                      sm.getCharacterData(end) - sm.getCharacterData(start)));
    } else {

        return comment::CommentScanner("");
    }
}
