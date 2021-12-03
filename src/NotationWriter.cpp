#include "ClangPrinter.hpp"
#include "CommentScanner.hpp"
#include "CoqPrinter.hpp"
#include "DeclVisitorWithArgs.h"
#include "Filter.hpp"
#include "Formatter.hpp"
#include "Logging.hpp"
#include "ModuleBuilder.hpp"
#include "SpecCollector.hpp"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/Version.inc"
#include <algorithm>

// TODO this should be replaced by something else.
void
print_path(CoqPrinter &print, const DeclContext *dc, bool end = true) {
    if (dc == nullptr || isa<TranslationUnitDecl>(dc)) {
        if (end)
            print.output() << "::";
    } else {
        print_path(print, dc->getParent());
        if (auto ts = dyn_cast<ClassTemplateSpecializationDecl>(dc)) {
            print.output() << ts->getNameAsString() << "<";
            bool first = true;
            for (auto i : ts->getTemplateArgs().asArray()) {
                if (!first) {
                    print.output() << ",";
                }
                first = false;
                switch (i.getKind()) {
                case TemplateArgument::ArgKind::Integral:
                    print.output() << i.getAsIntegral();
                    break;
                case TemplateArgument::ArgKind::Type: {
                    auto s = i.getAsType().getAsString();
                    replace(s.begin(), s.end(), ' ', '_');
                    print.output() << s;
                    break;
                }
                default:
                    print.output() << "?";
                }
            }
            print.output() << (end ? ">::" : ">");
        } else if (auto td = dyn_cast<TagDecl>(dc)) {
            if (td->getName() != "") {
                print.output() << td->getNameAsString() << (end ? "::" : "");
            }
        } else if (auto ns = dyn_cast<NamespaceDecl>(dc)) {
            if (!ns->isAnonymousNamespace()) {
                print.output() << ns->getNameAsString() << (end ? "::" : "");
            }
        } else {
            using namespace logging;
            //logging::log() << "unknown declaration while printing path "
            //               << dc->getDeclKindName() << "\n";
        }
    }
}

void
write_globals(::Module &mod, CoqPrinter &print, ClangPrinter &cprint) {
    print.output() << "Module _'." << fmt::indent << fmt::line;

    // todo(gmm): i would like to generate function names.
    for (auto def : mod.definitions()) {
        if (const FieldDecl *fd = dyn_cast<FieldDecl>(def)) {
            print.output() << "Notation \"'";
            print_path(print, fd->getParent(), true);
            print.output() << fd->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printField(fd, print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (const RecordDecl *rd = dyn_cast<RecordDecl>(def)) {
            if (!rd->isAnonymousStructOrUnion() &&
                rd->getNameAsString() != "") {
                print.output() << "Notation \"'";
                print_path(print, rd, false);
                print.output() << "'\" :=" << fmt::nbsp;

                cprint.printTypeName(rd, print);
                print.output()
                    << "%bs (in custom cppglobal at level 0)." << fmt::line;
            }

            for (auto fd : rd->fields()) {
                if (fd->getName() != "") {
                    print.output() << "Notation \"'";
                    print_path(print, rd, true);
                    print.output()
                        << fd->getNameAsString() << "'\" :=" << fmt::nbsp;
                    cprint.printField(fd, print);
                    print.output()
                        << " (in custom cppglobal at level 0)." << fmt::line;
                }
            }
        } else if (const FunctionDecl *fd = dyn_cast<FunctionDecl>(def)) {
            // todo(gmm): skipping due to function overloading
        } else if (const TypedefDecl *td = dyn_cast<TypedefDecl>(def)) {
            print.output() << "Notation \"'";
            print_path(print, td->getDeclContext(), true);
            print.output() << td->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(td->getUnderlyingType(), print);
            print.output() << " (in custom cppglobal at level 0)." << fmt::line;
        } else if (const auto *ta = dyn_cast<TypeAliasDecl>(def)) {
            print.output() << "Notation \"'";
            print_path(print, ta->getDeclContext(), true);
            print.output() << ta->getNameAsString() << "'\" :=" << fmt::nbsp;
            cprint.printQualType(ta->getUnderlyingType(), print);
            print.output() << " (only parsing, in custom cppglobal at level 0)." << fmt::line;
        } else if (isa<VarDecl>(def) || isa<EnumDecl>(def) ||
                   isa<EnumConstantDecl>(def)) {
        } else {
            using namespace logging;
            log(Level::VERBOSE) << "unknown declaration type "
                                << def->getDeclKindName() << "\n";
        }
    }

    print.output() << fmt::outdent << "End _'." << fmt::line;
    print.output() << "Export _'." << fmt::line << fmt::line;
}