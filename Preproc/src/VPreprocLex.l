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
 * Copyright 2000-2006 by Wilson Snyder.  This program is free software;
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

ws		[ \t\r\f]
nl		[\n]
quote		[\"]
backslash	[\\]
symb		[a-zA-Z_][a-zA-Z0-9_$]*

	/**************************************************************/
%%

<INITIAL>^{ws}*"`line"{ws}+.*{nl}	{ VPreprocLex::s_currentLexp->lineDirective(yytext); }

	/* Special directives we recognise */
<INITIAL>"`include"	{ return(VP_INCLUDE); }
<INITIAL>"`ifdef"	{ return(VP_IFDEF); }
<INITIAL>"`ifndef"	{ return(VP_IFNDEF); }
<INITIAL>"`else"	{ return(VP_ELSE); }
<INITIAL>"`elsif"	{ return(VP_ELSIF); }
<INITIAL>"`endif"	{ return(VP_ENDIF); }
<INITIAL>"`undef"	{ return(VP_UNDEF); }
<INITIAL>"`define"	{ return(VP_DEFINE); }

	/* Optional directives we recognise */
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
<STRMODE>{nl}		{ linenoInc(); yyerror("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>[^\"\\]	{ yymore(); }
<STRMODE>{backslash}.	{ yymore(); }
<STRMODE>{quote} 	{ yy_pop_state();
			  if (VPreprocLex::s_currentLexp->m_parenLevel) appendDefValue(yytext,yyleng);
			  else return (VP_STRING); }

	/* Pass-through include <> filenames */
<INCMODE><<EOF>>	{ linenoInc(); yyerror("EOF in unterminated include filename"); yyleng=0; yyterminate(); }
<INCMODE>{nl}		{ linenoInc(); yyerror("Unterminated include filename"); BEGIN(INITIAL); }
<INCMODE>[^\>\\]	{ yymore(); }
<INCMODE>{backslash}.	{ yymore(); }
<INCMODE>[\>]	 	{ yy_pop_state(); return (VP_STRING); }

	/* Reading definition */
<DEFMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFMODE>"//"[^\n]*	{ return (VP_COMMENT);}
<DEFMODE><<EOF>>	{ linenoInc(); yyerror("EOF (missing return?) in define value"); yyleng=0; yyterminate(); }
<DEFMODE>{nl}		{ linenoInc();
			  yy_pop_state();
			  return (VP_DEFVALUE); }	/* Note contains a return */
<DEFMODE>[^\/\*\n\m\\]+	|
<DEFMODE>[\\][^\n]	|
<DEFMODE>.		{ appendDefValue(yytext,yyleng); }
<DEFMODE>[\\]{nl}	{ linenoInc(); appendDefValue("\n",1); }

	/* Define arguments */
<ARGMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n]*	{ return (VP_COMMENT);}
<ARGMODE><<EOF>>	{ yyerror("EOF in define argument list\n"); yyleng = 0; yyterminate(); }
<ARGMODE>{nl}		{ yytext="\n"; yyleng=1; return(VP_WHITE); }
<ARGMODE>{quote}	{ yy_push_state(STRMODE); yymore(); }
<ARGMODE>[(]		{ VPreprocLex::s_currentLexp->m_parenLevel++; appendDefValue(yytext,yyleng); }
<ARGMODE>[,)]		{ if (VPreprocLex::s_currentLexp->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			      if (yytext[0]==')') VPreprocLex::s_currentLexp->m_parenLevel--;
			  } else {
			      unput(yytext[0]); yy_pop_state(); return (VP_DEFARG);
 			}}
<ARGMODE>[^\/\*\n\m\\(,)\"]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"[^\n]* 	{ return (VP_COMMENT); }

	/* C-style comments. */
<INITIAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTMODE>{nl}		{ linenoInc(); yymore(); }
<CMTMODE>.		{ yymore(); }
<CMTMODE><<EOF>>	{ yyerror("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }

	/* Define calls */
<INITIAL>"`"{symb}	{ return (VP_DEFREF); }

	/* Generics */
<INITIAL>{symb}		{ return (VP_SYMBOL); }
<INITIAL>{nl}	 	{ linenoInc(); return(VP_WHITE); }
<INITIAL>{ws}+		{ if (!keepWhitespace()) { yytext=" "; yyleng=1; } return VP_WHITE; }
<INITIAL>.		{ return (VP_TEXT); }
%%

void VPreprocLex::setStateDefArg() {
    // Enter define substitution argument state
    yy_push_state(ARGMODE);
    m_parenLevel = 1;
    m_defValue = "";
}

void VPreprocLex::setStateDefValue() {
    // Enter define value state
    yy_push_state(DEFMODE);
    m_parenLevel = 0;
    m_defValue = "";
}

void VPreprocLex::setStateIncFilename() {
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

void VPreprocLex::lineDirective(const char* textp) {
    while (*textp && isspace(*textp)) textp++;
    if (0==strncmp(textp,"`line",strlen("`line"))) textp+=strlen("`line");
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;

    // Grab linenumber
    const char *ln = textp;
    while (*textp && !isspace(*textp)) textp++;
    if (isdigit(*ln)) {
	m_curFilelinep = m_curFilelinep->create(atoi(ln));
    }
    while (*textp && (isspace(*textp) || *textp=='"')) textp++;

    // Grab filename
    const char *fn = textp;
    while (*textp && !(isspace(*textp) || *textp=='"')) textp++;
    if (textp != fn) {
	string newfilename; newfilename.append(fn, (textp-fn));
	m_curFilelinep = m_curFilelinep->create(newfilename, m_curFilelinep->lineno());
    }
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
