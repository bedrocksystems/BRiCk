/*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include "CoqPrinter.hpp"
#include <clang/AST/Expr.h>

using namespace clang;
using namespace fmt;

/**
 * @brief Implement a FSM-based pretty-printer to Coq strings.
 *
 * We use native string notation for ASCII parts of the string, and encoded each
 * character for non-ASCII parts. For instance, "Welcome to BHV™" is encoded as
 * "Welcome to BHV" ++ (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 BS.EmptyString))).
 *
 * In examples like these, we could use native string notation even for ™; but
 * this only works for valid UTF-8 encodings, so we don't bother.
 *
 * Switching between the "native" and "encoded" sections requires care to close
 * and quotes/parens, and output " ++ " if needed.
 * This is handled by StringPrettyPrinter::switch_st.

 * We present the code top-down.
 */
class StringPrettyPrinter {
    CoqPrinter& print;
public:
    StringPrettyPrinter(CoqPrinter& _print) : print(_print) { }

    /**
     * Entry-point: Pretty-print lit into a Coq string.
     */
    void pretty_print(const StringLiteral* lit) {
        for (auto i = lit->getBytes().begin(), end = lit->getBytes().end();
            i != end; ++i) {
            auto c = (unsigned char)*i;
            if (printable(c)) {
                toLit(c);
            } else {
                toEscape(c);
            }
        }
        if (state != PrettyState::NONE) { // Not at the beginning
            close();
            print.output() << fmt::rparen;
        } else {
            // This only happens on empty strings, but we must still output a string token.
            print.output() << "\"\"";
        }
    }

private:
    static bool printable(unsigned char c) {
        return (32 <= c) && (c < 128);
    }

    void toLit(unsigned char c) {
        switch_st(PrettyState::LIT);

        switch (c) {
            case '"':
                print.output() << "\"\"";
                break;
            default:
                print.output() << c;
        }
    }

    /**
     * @brief Pretty-prints a special character c as encoded.
     * For instance, "\xe2" is encoded by printing "(BS.String Byte.xe2", and deferring ")".
     */
    void toEscape(unsigned char c) {
        switch_st(PrettyState::ESCAPE);

        char buf[25];
        snprintf(buf, sizeof buf, "%02x", c);
        print.output() << "(BS.String Byte.x" << buf << " ";
        parens_to_close++;
    }
    // Count open parens to close. The value is -1 iff state is not PrettyState::ESCAPE.
    int parens_to_close{-1};

    enum class PrettyState { NONE, LIT, ESCAPE };
    // We use PrettyState::NONE only at the beginning.
    PrettyState state{PrettyState::NONE};

    /**
     * @brief Switch to new pretty-printing state.
     * If we're switching state, and there is an active section (state !=
     * PrettyState::NONE), we must:
     * - close any open quotes or parentheses.
     * - output " ++ "
     * We must then "open" the new state (output the opening quote, or reset the
     * parenthesis count).
     *
     * @param new_st (not PrettyState::NONE).
     */
    void switch_st(PrettyState new_st) {
        assert(new_st != PrettyState::NONE);
        if (new_st != state) {
            if (state != PrettyState::NONE) { // Not at the beginning
                close();
                print.output() << " ++ ";
            } else {
                print.output() << fmt::lparen;
            }
            open(new_st);
            state = new_st;
        }
    }

    /**
     * @brief Print any closing quotes/parentheses to switch away from the current state.
     */
    void close() {
        switch (state) {
        case PrettyState::NONE:
            assert(false);
            break;
        case PrettyState::LIT:
            print.output() << "\"";
            break;
        case PrettyState::ESCAPE:
            // print.output() << "BS.EmptyString";
            print.output() << "\"\"";

            for (auto i = 0; i < parens_to_close; i++) {
                print.output() << ")";
            }
            parens_to_close = -1;

            break;
        }
    }

    /**
     * @brief Setup for new state.
     */
    void open(PrettyState new_st) {
        switch (new_st) {
        case PrettyState::LIT:
            print.output() << "\"";
            break;
        case PrettyState::ESCAPE:
            assert(parens_to_close == -1);
            parens_to_close = 0;
            break;
        case PrettyState::NONE:
            assert(false);
            break;
        }
    }
};

fmt::Formatter& CoqPrinter::escaped_str(const clang::StringLiteral* lit) {
    StringPrettyPrinter(*this).pretty_print(lit);
    return this->output();
}
