#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"

using namespace clang;

class PrintSpec :
    public ConstDeclVisitorArgs<PrintSpec, void, CoqPrinter &, ClangPrinter &,
                                clang::comments::FullComment &> {
private:
    llvm::StringRef get_text(SourceRange range) const {
        auto len = sm_.getCharacterData(range.getEnd()) -
                   sm_.getCharacterData(range.getBegin());
        return StringRef(sm_.getCharacterData(range.getBegin()), len + 1);
    }

    void write_paragraph(CoqPrinter &print,
                         comments::ParagraphComment *comment) const {
        auto txt = get_text(comment->getSourceRange());
        auto both = txt.split("\n");
        while (both.first != "") {
            print.output() << both.first.trim(' ').trim('\t') << fmt::line;
            auto rest = both.second.drop_while(isWhitespace);
            if (rest.startswith("*")) {
                rest = rest.substr(1).drop_while(isWhitespace);
            }
            both = rest.split("\n");
        }
    }

    comments::ParagraphComment *get_tag(clang::comments::FullComment &comment,
                                        const char *tag) const {
        for (auto b : comment.getBlocks()) {
            if (auto pcc = dyn_cast<comments::ParagraphComment>(b)) {
                auto sr = get_text(pcc->getSourceRange()).ltrim();
                if (sr.startswith(tag)) {
                    return pcc;
                }
            }
        }
        return nullptr;
    }

    bool is_raw(clang::comments::FullComment &cmt) {
        return get_tag(cmt, "\\raw") != nullptr;
    }

    // this prints a `function_spec`
    void print_function_spec(CoqPrinter &print, ClangPrinter &cprint,
                             clang::comments::FullComment &comment) const {
        // print the \with blocks
        {
            bool started = false;
            for (auto b : comment.getBlocks()) {
                if (auto pcc = dyn_cast<comments::ParagraphComment>(b)) {
                    auto sr = get_text(pcc->getSourceRange())
                                  .trim(' ')
                                  .trim('\n')
                                  .trim(' ');
                    if (sr.startswith("\\with")) {
                        if (!started) {
                            started = true;
                            print.output() << "\\with" << fmt::indent;
                        }
                        auto a = sr.split("\n");
                        print.output() << a.first.trim().substr(5);
                    }
                }
            }
            if (started) {
                print.output() << fmt::outdent << fmt::line;
            }
        }

        // print the \pre blocks
        {
            for (auto b : comment.getBlocks()) {
                if (auto bcc = dyn_cast<comments::BlockCommandComment>(b)) {
                    if (get_text(bcc->getSourceRange()).startswith("\\pre")) {
                        print.output() << "\\pre  " << fmt::indent;
                        write_paragraph(print, bcc->getParagraph());
                        print.output() << fmt::outdent;
                    }
                }
            }
        }

        // print the \post blocks
        {
            for (auto b : comment.getBlocks()) {
                if (auto bcc = dyn_cast<comments::BlockCommandComment>(b)) {
                    if (get_text(bcc->getSourceRange()).startswith("\\post")) {
                        print.output() << "\\post " << fmt::indent;
                        write_paragraph(print, bcc->getParagraph());
                        print.output() << fmt::outdent;
                    }
                }
            }
        }
    }

    void print_arguments(const FunctionDecl *decl, CoqPrinter &print,
                         ClangPrinter &cprint,
                         clang::comments::FullComment &cmt, bool with_this) {
        bool has_args = with_this || decl->param_begin() != decl->param_end();
        if (has_args) {
            print.ctor("fun");
            if (with_this) {
                print.output() << "this" << fmt::nbsp;
            }
            for (auto i : decl->parameters()) {
                print.output() << i->getName() << fmt::nbsp;
            }
            if (has_args) {
                print.output() << "=>" << fmt::line;
            }

            print_function_spec(print, cprint, cmt);

            print.end_ctor();
        } else {
            print.output() << fmt::line << fmt::lparen;
            print_function_spec(print, cprint, cmt);
            print.output() << fmt::rparen;
        }
    }

    void print_parameter_types(const FunctionDecl *decl, CoqPrinter &print,
                               ClangPrinter &cprint) {
        print.begin_list();
        for (auto i : decl->parameters()) {
            cprint.printQualType(i->getType(), print);
            print.cons();
        }
        print.end_list();
    }

public:
    bool is_internal(clang::comments::FullComment &cmt) {
        return get_tag(cmt, "\\internal") != nullptr;
    }

    bool has_specification(clang::comments::FullComment &cmt) {
        for (auto i : cmt.getBlocks()) {
            auto txt = get_text(i->getSourceRange());
            if (txt.startswith("\\pre") || txt.startswith("\\post") ||
                txt.startswith("\\spec")) {
                return true;
            }
        }
        return false;
    }

    void VisitCXXMethodDecl(const CXXMethodDecl *decl, CoqPrinter &print,
                            ClangPrinter &cprint,
                            clang::comments::FullComment &cmt) {
        if (auto spec_para = get_tag(cmt, "\\spec")) {
            write_paragraph(print, spec_para);
            return;
        }

        print.ctor("ticptr");
        if (decl->isStatic()) {
            print.ctor("SFunction");
            cprint.printQualType(decl->getReturnType(), print);
            print.output() << fmt::nbsp;

            print_parameter_types(decl, print, cprint);

            print_arguments(decl, print, cprint, cmt, false);

            print.end_ctor();
        } else {
            print.ctor("SMethod");
            cprint.printGlobalName(decl->getParent(), print);
            print.output() << fmt::nbsp;
            cprint.printQualifier(decl->isConst(), decl->isVolatile(), print);
            print.output() << fmt::nbsp;
            cprint.printQualType(decl->getReturnType(), print);
            print.output() << fmt::nbsp;

            print_parameter_types(decl, print, cprint);

            print_arguments(decl, print, cprint, cmt, true);

            print.end_ctor();
        }
        print.end_ctor();
    }

    void VisitFunctionDecl(const FunctionDecl *decl, CoqPrinter &print,
                           ClangPrinter &cprint,
                           clang::comments::FullComment &cmt) {
        if (auto spec_para = get_tag(cmt, "\\spec")) {
            write_paragraph(print, spec_para);
            return;
        }

        print.ctor("ticptr");
        print.ctor("SFunction");
        cprint.printQualType(decl->getReturnType(), print);
        print.output() << fmt::nbsp;

        print_parameter_types(decl, print, cprint);

        print_arguments(decl, print, cprint, cmt, false);

        print.end_ctor();
        print.end_ctor();
    }

    void VisitCXXConstructorDecl(const CXXConstructorDecl *decl,
                                 CoqPrinter &print, ClangPrinter &cprint,
                                 clang::comments::FullComment &cmt) {
        if (auto spec_para = get_tag(cmt, "\\spec")) {
            write_paragraph(print, spec_para);
            return;
        }

        print.ctor("ticptr");
        if (is_raw(cmt)) {
            print.ctor("SMethod");
            cprint.printGlobalName(decl->getParent(), print);
            print.output() << fmt::nbsp;
            cprint.printQualifier(false, false, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(ctxt_.VoidTy, print);
            print.output() << fmt::nbsp;

        } else {
            print.ctor("SConstructor");

            cprint.printGlobalName(decl->getParent(), print);
            print.output() << fmt::nbsp;
        }

        print_parameter_types(decl, print, cprint);

        print_arguments(decl, print, cprint, cmt, true);

        print.end_ctor();
        print.end_ctor();
    }

    void VisitCXXDestructorDecl(const CXXDestructorDecl *decl,
                                CoqPrinter &print, ClangPrinter &cprint,
                                clang::comments::FullComment &cmt) {
        if (auto spec_para = get_tag(cmt, "\\spec")) {
            write_paragraph(print, spec_para);
            return;
        }

        print.ctor("ticptr");
        if (is_raw(cmt)) {
            print.ctor("SMethod");
            cprint.printGlobalName(decl->getParent(), print);
            print.output() << fmt::nbsp;
            cprint.printQualifier(false, false, print);
            print.output() << fmt::nbsp;
            cprint.printQualType(ctxt_.VoidTy, print);
            print.output() << fmt::nbsp;

        } else {
            print.ctor("SDestructor");

            cprint.printGlobalName(decl->getParent(), print);
            print.output() << fmt::nbsp;
        }

        print_arguments(decl, print, cprint, cmt, true);

        print.end_ctor();
        print.end_ctor();
    }

public:
    PrintSpec(ASTContext &ctxt)
        : ctxt_(ctxt), sm_(ctxt.getSourceManager()),
          diag_(ctxt.getDiagnostics()) {}

private:
    ASTContext &ctxt_;
    SourceManager &sm_;
    DiagnosticsEngine &diag_;
};

static void
begin_decl(const NamedDecl *decl, CoqPrinter &print, ClangPrinter &cprint) {
    print.output() << "Definition ";
    cprint.printGlobalName(decl, print, true);
    print.output() << "_spec :=" << fmt::indent;
    print.begin_record();
    print.record_field("s_name");
    cprint.printGlobalName(decl, print);
    print.output() << fmt::line << " ; ";
    print.record_field("s_spec") << fmt::indent;
}

static void
end_decl(const NamedDecl *, CoqPrinter &print, ClangPrinter &) {
    print.output() << fmt::outdent;
    print.end_record();
    print.output() << fmt::outdent << "." << fmt::line;
}

void
write_globals(::Module &mod, CoqPrinter &print, ClangPrinter &cprint) {

    print.output() << "Module _'." << fmt::indent << fmt::line;

    // todo(gmm): i would like to generate function names.
    for (auto i : mod.definitions()) {
        auto def = i.second;
        auto class_name = def->getNameAsString();
        if (const FieldDecl *fd = dyn_cast<FieldDecl>(def)) {
            print.output() << "Notation \"'" << fd->getNameAsString()
                           << "'\" :=" << fmt::nbsp;
            cprint.printField(fd, print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (const RecordDecl *rd = dyn_cast<RecordDecl>(def)) {
            print.output() << "Notation \"'" << class_name
                           << "'\" :=" << fmt::nbsp;
            cprint.printGlobalName(def, print);
            print.output() << "%string (in custom cppglobal at level 0)."
                           << fmt::line;

            for (auto fd : rd->fields()) {
                print.output()
                    << "Notation \"'" << class_name
                    << "::" << fd->getNameAsString() << "'\" :=" << fmt::nbsp;
                cprint.printField(fd, print);
                print.output()
                    << " (in custom cppglobal at level 0)." << fmt::line;
            }
        }
    }

    print.output() << fmt::outdent << "End _'." << fmt::line;
    print.output() << "Import _'." << fmt::line << fmt::line;
}

void
write_spec(::Module *mod, const SpecCollector &specs,
           const clang::TranslationUnitDecl *tu, Filter &filter,
           fmt::Formatter &output) {
    auto &ctxt = tu->getASTContext();
    ClangPrinter cprint(&tu->getASTContext());
    CoqPrinter print(output);
    PrintSpec printer(ctxt);

    NoInclude source(ctxt.getSourceManager());

    print.output() << "(*" << fmt::line << " * Specifications extracted from "
                   << ctxt.getSourceManager()
                          .getFileEntryForID(
                              ctxt.getSourceManager().getMainFileID())
                          ->getName()
                   << fmt::line << " *)" << fmt::line << fmt::line
                   << "Require Import Cpp.Auto." << fmt::line
                   << "Local Open Scope Z_scope." << fmt::line << fmt::line;

    // it would be nice to include a top-level comment.

    // generate all of the record fields
    write_globals(*mod, print, cprint);

    std::list<const NamedDecl *> public_names;
    std::list<const NamedDecl *> internal_names;
    // std::list<const NamedDecl*> imported_names;

    for (auto c : ctxt.getRawCommentList().getComments()) {
        if (!source.isIncluded(c->getBeginLoc())) {
            if (c->isAttached()) {
                // this comment is attached to a declaration
                auto di = specs.decl_for_comment(c);
                assert(di.hasValue());

                const NamedDecl *decl = di.getValue();
                auto comment = ctxt.getCommentForDecl(decl, nullptr);
                if (!printer.has_specification(*comment)) {
                    continue;
                }
                assert(comment && "decl with comment does not have comment");

                output << "(* BEGIN_SOURCE("
                       << comment->getBeginLoc().printToString(
                              ctxt.getSourceManager())
                       << ") *)" << fmt::line;
                begin_decl(decl, print, cprint);
                printer.Visit(decl, print, cprint, *comment);
                end_decl(decl, print, cprint);
                output << "(* END_SOURCE("
                       << comment->getEndLoc().printToString(
                              ctxt.getSourceManager())
                       << ") *)" << fmt::line << fmt::line;

                if (printer.is_internal(*comment)) {
                    internal_names.push_back(decl);
                } else {
                    public_names.push_back(decl);
                }
            } else {
                if (c->getKind() == RawComment::RCK_Qt ||
                    c->getKind() == RawComment::RCK_BCPLExcl) {
                    auto text = c->getRawText(ctxt.getSourceManager());

                    if (text.startswith("/*!coq")) {
                        output << "(* BEGIN_SOURCE("
                               << c->getBeginLoc().printToString(
                                      ctxt.getSourceManager())
                               << ") *)" << fmt::line;
                        output << text.substr(7).drop_back(2).trim()
                               << fmt::line;
                        output << "(* END_SOURCE("
                               << c->getEndLoc().printToString(
                                      ctxt.getSourceManager())
                               << ") *)" << fmt::line << fmt::line;
                    }
                }
            }
        }
    }

    print.output() << fmt::line
                   << "Definition internal_spec : signature :=" << fmt::indent
                   << fmt::line << "make_signature" << fmt::nbsp;
    print.begin_list();
    for (auto d : internal_names) {
        cprint.printGlobalName(d, print, true);
        print.output() << "_spec";
        print.cons();
    }
    print.end_list() << "." << fmt::outdent << fmt::line;

    print.output() << fmt::line
                   << "Definition public_spec : signature :=" << fmt::indent
                   << fmt::line << "make_signature" << fmt::nbsp;
    print.begin_list();
    for (auto d : public_names) {
        cprint.printGlobalName(d, print, true);
        print.output() << "_spec";
        print.cons();
    }
    print.end_list() << "." << fmt::outdent << fmt::line;
}
