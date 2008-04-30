// $Id$  -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2008 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
/// \file
/// \brief Verilog::Parse: Internal header for lex interfacing
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
/// This header provides the interface between the lex proper VParseLex.l/.cpp
/// and the class implementation file VParse.cpp
/// It is not intended for user applications.
///
//*************************************************************************

#ifndef _VPARSELEX_H_		// Guard
#define _VPARSELEX_H_ 1

#include "VFileLine.h"
#include "VParseGrammar.h"

//======================================================================
// Externs created by flex
// We add a prefix so that other lexers/flexers in the same program won't collide.
#ifndef yy_create_buffer
# define yy_create_buffer VParseLex_create_buffer
# define yy_delete_buffer VParseLex_delete_buffer
# define yy_scan_buffer VParseLex_scan_buffer
# define yy_scan_string VParseLex_scan_string
# define yy_scan_bytes VParseLex_scan_bytes
# define yy_flex_debug VParseLex_flex_debug
# define yy_init_buffer VParseLex_init_buffer
# define yy_flush_buffer VParseLex_flush_buffer
# define yy_load_buffer_state VParseLex_load_buffer_state
# define yy_switch_to_buffer VParseLex_switch_to_buffer
# define yyin VParseLexin
# define yyleng VParseLexleng
# define yylex VParseLexlex
# define yyout VParseLexout
# define yyrestart VParseLexrestart
# define yytext VParseLextext
#endif

#ifndef YY_BUFFER_STATE
struct yy_buffer_state;
typedef struct yy_buffer_state *YY_BUFFER_STATE;
# define YY_BUF_SIZE 16384
#endif

extern int yylex();
extern void yyrestart(FILE*);
extern char* yytext;
extern int yyleng;
YY_BUFFER_STATE yy_create_buffer ( FILE *file, int size );
YY_BUFFER_STATE yy_scan_bytes(const char *bytes, int len);
void yy_switch_to_buffer( YY_BUFFER_STATE new_buffer );
void yy_delete_buffer( YY_BUFFER_STATE b );

class VParse;

//======================================================================
/// Class entry for each lexer state

class VParseLex {
  public:	// Used only by VParseLex.cpp and VParse.cpp
    VParse* 	m_parsep;	///< Current parser
    bool	m_inCellDefine;	///< In a `celldefine

    bool	m_ahead;		///< aheadToken is valid
    int		m_aheadToken;		///< Token we read ahead
    VParseBisonYYSType m_aheadVal;	///< aheadToken's value

    // Parse state
    YY_BUFFER_STATE  m_yyState;	///< flex input state

    // State to lexer
    static VParseLex* s_currentLexp;	///< Current lexing point
    static VParseBisonYYSType* s_yylvalp;

    // CONSTRUCTORS
    VParseLex(VParse* parsep) {
	m_parsep = parsep;
	m_inCellDefine = false;
	m_ahead = false;

	static char buf[YY_BUF_SIZE+2]="\0";
	m_yyState = yy_create_buffer(NULL, YY_BUF_SIZE);
	s_currentLexp = this;
	yyrestart(NULL);
	debug(0);
    }
    ~VParseLex() {
	yy_delete_buffer(m_yyState);
	s_currentLexp = NULL;
    }

    void restart() { yyrestart(NULL); }

    // Internal Utilities
    static bool symEscapeless(const char* textp, int leng) {
	// Are \ escapes needed to print this symbol?
	if (leng<1) return false;  // Probably not a valid identifier, but better than a core dump...
	if (!isalpha(textp[0]) && textp[0] != '_') return false;
	while (leng) {
	    if (!isalnum(*textp) && *textp != '_') return false;
	    leng--; textp++;
	}
	return true;
    }

    /// Called by VParse.cpp to inform lexer
    void unputString(const char* textp);
    void unused();

    void debug(int level);
    int lexToken(VParseBisonYYSType* yylvalp);
    void language(const char* value);
};

#endif // Guard
