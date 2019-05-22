// Copyright (C) 2019 BedRock Systems
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
#include "CommentScanner.hpp"
#include "clang/Basic/Version.inc"
#include <Formatter.hpp>
#include <clang/AST/ASTContext.h>
#include <clang/AST/DeclBase.h>
#include <list>

using namespace clang;
using namespace comment;

static SourceLocation getStartSourceLocWithComment(
        clang::ASTContext *ctxt, const Decl *d)
{
  if (auto comment = ctxt->getRawCommentForDeclNoCache(d)) {
    return comment->getLocStart();
  } else {
    return d->getLocStart();
  }
}

static Decl *getPreviousDeclInContext(const Decl *d)
{
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

static SourceLocation getPrevSourceLoc(SourceManager &sm, const Decl *d)
{
  auto pd = getPreviousDeclInContext(d);
  if (pd && pd->getLocEnd().isValid()) {
    return pd->getLocEnd();
  } else {
    return sm.getLocForStartOfFile(
            sm.getFileID(d->getSourceRange().getBegin()));
  }
}

CommentScanner CommentScanner::decl_comments(
        const clang::Decl *decl, clang::ASTContext *ctxt)
{
  SourceManager &sm = ctxt->getSourceManager();
  auto start = getPrevSourceLoc(sm, decl);
  auto end = getStartSourceLocWithComment(ctxt, decl);

  if (start.isValid() && end.isValid()) {
    return comment::CommentScanner(StringRef(sm.getCharacterData(start),
            sm.getCharacterData(end) - sm.getCharacterData(start)));
  } else {
    return comment::CommentScanner("");
  }
}
