// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2010 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Preproc: Internal header for lex interfacing
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
/// This header provides the interface between the lex proper VPreLex.l/.cpp
/// and the class implementation file VPreProc.cpp
/// It is not intended for user applications.
///
//*************************************************************************

#ifndef _VPREPROCLEX_H_		// Guard
#define _VPREPROCLEX_H_ 1

#include <deque>
#include <stack>

#include "VFileLine.h"

// Token codes
// If changing, see VPreProc.cpp's VPreProcImp::tokenName()
#define VP_EOF		0

#define VP_INCLUDE	256
#define VP_IFDEF	257
#define VP_IFNDEF	258
#define VP_ENDIF	259
#define VP_UNDEF	260
#define VP_DEFINE	261
#define VP_ELSE		262
#define VP_ELSIF	263
#define VP_LINE		264
#define VP_UNDEFINEALL	265

#define VP_SYMBOL	300
#define VP_STRING	301
#define VP_DEFVALUE	302
#define VP_COMMENT	303
#define VP_TEXT		304
#define VP_WHITE	305
#define VP_DEFREF	306
#define VP_DEFARG	307
#define VP_ERROR	308
#define VP_DEFFORM	309


//======================================================================
// Externs created by flex
// We add a prefix so that other lexers/flexers in the same program won't collide.
#ifndef yy_create_buffer
# define yy_create_buffer VPreLex_create_buffer
# define yy_delete_buffer VPreLex_delete_buffer
# define yy_scan_buffer VPreLex_scan_buffer
# define yy_scan_string VPreLex_scan_string
# define yy_scan_bytes VPreLex_scan_bytes
# define yy_flex_debug VPreLex_flex_debug
# define yy_init_buffer VPreLex_init_buffer
# define yy_flush_buffer VPreLex_flush_buffer
# define yy_load_buffer_state VPreLex_load_buffer_state
# define yy_switch_to_buffer VPreLex_switch_to_buffer
# define yyin VPreLexin
# define yyleng VPreLexleng
# define yylex VPreLexlex
# define yyout VPreLexout
# define yyrestart VPreLexrestart
# define yytext VPreLextext
#endif

#ifndef yyourleng
# define yyourleng VPreLexourleng
# define yyourtext VPreLexourtext
#endif

#ifndef YY_BUFFER_STATE
struct yy_buffer_state;
typedef struct yy_buffer_state *YY_BUFFER_STATE;
# define YY_BUF_SIZE 16384
#endif

extern int yylex();
extern void yyrestart(FILE*);

// Accessors, because flex keeps changing the type of yyleng
extern char* yyourtext();
extern size_t yyourleng();
extern void yyourtext(const char* textp, size_t size);  // Must call with static

YY_BUFFER_STATE yy_create_buffer ( FILE *file, int size );
void yy_switch_to_buffer( YY_BUFFER_STATE new_buffer );
void yy_delete_buffer( YY_BUFFER_STATE b );

//======================================================================

#define KEEPCMT_SUB 2
#define KEEPCMT_EXP 3

//======================================================================
// Class entry for each per-lexer state

class VPreLex {
  public:	// Used only by VPreLex.cpp and VPreProc.cpp
    VFileLine*	m_curFilelinep;	///< Current processing point

    // Parse state
    stack<YY_BUFFER_STATE> m_bufferStack;	///< Stack of inserted text above current point
    deque<string>	m_buffers;	///< Buffer of characters to process

    // State to lexer
    static VPreLex* s_currentLexp;	///< Current lexing point
    int		m_keepComments;		///< Emit comments in output text
    int		m_keepWhitespace;	///< Emit all whitespace in output text
    bool	m_pedantic;	///< Obey standard; don't Substitute `error

    // State from lexer
    int		m_formalLevel;	///< Parenthesis counting inside def formals
    int		m_parenLevel;	///< Parenthesis counting inside def args
    bool	m_defCmtSlash;	///< /*...*/ comment in define had \ ending
    string	m_defValue;	///< Definition value being built.

    // CONSTRUCTORS
    VPreLex() {
	m_keepComments = 0;
	m_keepWhitespace = 1;
	m_pedantic = false;
	m_formalLevel = 0;
	m_parenLevel = 0;
	m_defCmtSlash = false;
	initFirstBuffer();
    }
    ~VPreLex() {
	while (!m_bufferStack.empty()) { yy_delete_buffer(m_bufferStack.top()); m_bufferStack.pop(); }
    }
    void initFirstBuffer();

    /// Called by VPreLex.l from lexer
    VFileLine* curFilelinep() { return m_curFilelinep; }
    void curFilelinep(VFileLine* fl) { m_curFilelinep = fl; }
    void appendDefValue(const char* text, size_t len);
    void lineDirective(const char* textp) { curFilelinep(curFilelinep()->lineDirective(textp)); }
    void linenoInc() { curFilelinep(curFilelinep()->create(curFilelinep()->lineno()+1)); }
    /// Called by VPreProc.cpp to inform lexer
    void pushStateDefArg(int level);
    void pushStateDefForm();
    void pushStateDefValue();
    void pushStateIncFilename();
    void scanBytes(const char* strp, size_t len);
    void scanBytesBack(const string& str);
    size_t inputToLex(char* buf, size_t max_size);
    /// Called by VPreProc.cpp to get data from lexer
    YY_BUFFER_STATE currentBuffer();
    int	 currentStartState();
    void dumpSummary();
    void dumpStack();
    void unused();
};

#endif // Guard
