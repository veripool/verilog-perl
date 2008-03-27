%option noyywrap align interactive
%option stack
%option noc++
%option prefix="VPreprocLex"
%{
/* $Id$
 ******************************************************************************
 * DESCRIPTION: Verilog Preprocessor Lexer
 * 
 * This file is part of Verilog-Perl.  
 * 
 * Author: Wilson Snyder <wsnyder@wsnyder.org>
 * 
 * Code available from: http://www.veripool.com/systemperl
 * 
 ******************************************************************************
 * 
 * Copyright 2000-2008 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the GNU
 * General Public License or the Perl Artistic License.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 *****************************************************************************
 * Do not use Flex in C++ mode.  It has bugs with yyunput() which result in
 * lost characters.
 *****************************************************************************/

#include "VPreprocLex.h"
#include <stdio.h>
#include <iostream>

VPreprocLex* VPreprocLex::s_currentLexp = NULL;	// Current lexing point

#define linenoInc()  { VPreprocLex::s_currentLexp->linenoInc(); }
bool pedantic() { return VPreprocLex::s_currentLexp->m_pedantic; }
bool keepWhitespace() { return VPreprocLex::s_currentLexp->m_keepWhitespace; }
void yyerror(char* msg) { VPreprocLex::s_currentLexp->m_curFilelinep->error(msg); }
void appendDefValue(char* t,int l) { VPreprocLex::s_currentLexp->appendDefValue(t,l); }

/**********************************************************************/
%}

%x CMTMODE
%x STRMODE
%x DEFMODE
%x ARGMODE
%x INCMODE
%x PRTMODE

/* drop: Drop Ctrl-Z - can't pass thru or may EOF the output too soon */

ws		[ \t\f\r]
wsn		[ \t\f]
crnl		[\r]*[\n]
quote		[\"]
backslash	[\\]
symb		[a-zA-Z_][a-zA-Z0-9_$]*
drop		[\032]

	/**************************************************************/
%%

<INITIAL>^{ws}*"`line"{ws}+.*{crnl}	{ VPreprocLex::s_currentLexp->lineDirective(yytext);
					  return(VP_LINE); }

	/* Special directives we recognize */
<INITIAL>"`include"	{ return(VP_INCLUDE); }
<INITIAL>"`ifdef"	{ return(VP_IFDEF); }
<INITIAL>"`ifndef"	{ return(VP_IFNDEF); }
<INITIAL>"`else"	{ return(VP_ELSE); }
<INITIAL>"`elsif"	{ return(VP_ELSIF); }
<INITIAL>"`endif"	{ return(VP_ENDIF); }
<INITIAL>"`undef"	{ return(VP_UNDEF); }
<INITIAL>"`define"	{ return(VP_DEFINE); }

	/* Optional directives we recognize */
<INITIAL>"`__FILE__"	{ if (!pedantic()) {
	    		     yytext = (char*)VPreprocLex::s_currentLexp->m_curFilelinep->cfilename();
	    		     yyleng = strlen(yytext); return (VP_TEXT);
	                  } else return(VP_DEFREF); }
<INITIAL>"`__LINE__"	{ if (!pedantic()) {
	                     static char buf[10];
			     sprintf(buf, "%d",VPreprocLex::s_currentLexp->m_curFilelinep->lineno());
	                     yytext = buf; yyleng = strlen(yytext); return (VP_TEXT);
	                  } else return(VP_DEFREF); }
<INITIAL>"`error"	{ if (!pedantic()) return (VP_ERROR); else return(VP_DEFREF); }

	/* Pass-through strings */
<INITIAL>{quote}	{ yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>	{ linenoInc(); yyerror("EOF in unterminated string"); yyleng=0; yyterminate(); }
<STRMODE>{crnl}		{ linenoInc(); yyerror("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>[^\"\\]	{ yymore(); }
<STRMODE>{backslash}.	{ yymore(); }
<STRMODE>{quote} 	{ yy_pop_state();
			  if (VPreprocLex::s_currentLexp->m_parenLevel) appendDefValue(yytext,yyleng);
			  else return (VP_STRING); }

	/* Protected blocks */
<INITIAL>"`protected"	{ yy_push_state(PRTMODE); yymore(); }
<PRTMODE><<EOF>>	{ linenoInc(); yyerror("EOF in `protected"); yyleng=0; yyterminate(); }
<PRTMODE>{crnl}		{ linenoInc(); yymore(); }
<PRTMODE>.	 	{ yymore(); }
<PRTMODE>"`endprotected" { yy_pop_state(); return (VP_TEXT); }

	/* Pass-through include <> filenames */
<INCMODE><<EOF>>	{ linenoInc(); yyerror("EOF in unterminated include filename"); yyleng=0; yyterminate(); }
<INCMODE>{crnl}		{ linenoInc(); yyerror("Unterminated include filename"); BEGIN(INITIAL); }
<INCMODE>[^\>\\]	{ yymore(); }
<INCMODE>{backslash}.	{ yymore(); }
<INCMODE>[\>]	 	{ yy_pop_state(); return (VP_STRING); }

	/* Reading definition */
<DEFMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFMODE>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFMODE>{drop}		{ }
<DEFMODE><<EOF>>	{ linenoInc(); yyerror("EOF (missing return?) in define value"); yyleng=0; yyterminate(); }
<DEFMODE>{crnl}		{ linenoInc(); yy_pop_state(); yytext="\n"; yyleng=1; return (VP_DEFVALUE); }
<DEFMODE>[\\]{crnl}	{ linenoInc(); appendDefValue("\n",1); } /* Include return so can maintain output line count */
<DEFMODE>[^\/\*\n\r\\]+	|
<DEFMODE>[\\][^\n\r]	|
<DEFMODE>.		{ appendDefValue(yytext,yyleng); }

	/* Define arguments */
<ARGMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n\r]*	{ return (VP_COMMENT);}
<ARGMODE>{drop}		{ }
<ARGMODE><<EOF>>	{ yyerror("EOF in define argument list\n"); yyleng = 0; yyterminate(); }
<ARGMODE>{crnl}		{ linenoInc(); yytext="\n"; yyleng=1; return(VP_WHITE); }
<ARGMODE>{quote}	{ yy_push_state(STRMODE); yymore(); }
<ARGMODE>[(]		{ VPreprocLex::s_currentLexp->m_parenLevel++;
			  if (VPreprocLex::s_currentLexp->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      return (VP_TEXT);
 			}}
<ARGMODE>[)]		{ VPreprocLex::s_currentLexp->m_parenLevel--;
			  if (VPreprocLex::s_currentLexp->m_parenLevel>0) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
 			}}
<ARGMODE>[,]		{ if (VPreprocLex::s_currentLexp->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
 			}}
<ARGMODE>"`"{symb}	{ return (VP_DEFREF); }  /* defref in defref */
<ARGMODE>[^\/\*\n\r\\(,)\"`]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"[^\n\r]* 	{ return (VP_COMMENT); }

	/* C-style comments. */
<INITIAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTMODE>{crnl}		{ linenoInc(); yymore(); }
<CMTMODE>.		{ yymore(); }
<CMTMODE><<EOF>>	{ yyerror("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }

	/* Define calls */
<INITIAL>"`"{symb}	{ return (VP_DEFREF); }

	/* Generics */
<INITIAL>{crnl}		{ linenoInc(); yytext="\n"; yyleng=1; return(VP_WHITE); }
<INITIAL>{symb}		{ return (VP_SYMBOL); }
<INITIAL>[\r]		{ }
<INITIAL>{wsn}+		{ if (!keepWhitespace()) { yytext=" "; yyleng=1; } return VP_WHITE; }
<INITIAL>{drop}		{ }
<INITIAL>.		{ return (VP_TEXT); }

<*>.|\n			{ yymore(); }	/* Prevent hitting ECHO; */
%%

void VPreprocLex::pushStateDefArg() {
    // Enter define substitution argument state
    yy_push_state(ARGMODE);
    m_parenLevel = 0;
    m_defValue = "";
}

void VPreprocLex::pushStateDefValue() {
    // Enter define value state
    yy_push_state(DEFMODE);
    m_parenLevel = 0;
    m_defValue = "";
}

void VPreprocLex::pushStateIncFilename() {
    // Enter include <> filename state
    yy_push_state(INCMODE);
    yymore();
}

void VPreprocLex::unputString(const char* textp) {
    // Add characters to input stream in back-to-front order
    const char* cp;
    for (cp = textp; *cp; cp++);
    for (cp--; cp >= textp; cp--) {
	unput(*cp);
    }
}

void VPreprocLex::appendDefValue(const char* textp, int len) {
    // Append given text to current definition value being formed
    m_defValue.append(textp,len);
}

void VPreprocLex::unused() {
    if (0) {
	// Prevent unused warnings
	yy_top_state();
    }
}

/*###################################################################
 * Local Variables:
 * mode: C
 * End:
 */
