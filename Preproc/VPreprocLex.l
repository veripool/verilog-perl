%option noyywrap align interactive
%option stack
%option noc++
%option prefix="VPreprocLex"
%{
/******************************************************************************
 * DESCRIPTION: Verilog Preprocessor Lexer
 *
 * This file is part of Verilog-Perl.
 *
 * Author: Wilson Snyder <wsnyder@wsnyder.org>
 *
 * Code available from: http://www.veripool.org/systemperl
 *
 ******************************************************************************
 *
 * Copyright 2000-2009 by Wilson Snyder.  This program is free software;
 * you can redistribute it and/or modify it under the terms of either the GNU
 * Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
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
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <iostream>

// Flex 2.5.35 has compile warning in ECHO, so we'll default our own rule
#define ECHO yyerrorf("Missing VPreprocLex.l rule: ECHO rule invoked in state %d: %s", YY_START, yytext);

VPreprocLex* VPreprocLex::s_currentLexp = NULL;	// Current lexing point

#define LEXP VPreprocLex::s_currentLexp

#define linenoInc()  { LEXP->linenoInc(); }
bool pedantic() { return LEXP->m_pedantic; }
bool keepWhitespace() { return LEXP->m_keepWhitespace; }
void yyerror(char* msg) { LEXP->m_curFilelinep->error(msg); }
void appendDefValue(const char* t,int l) { LEXP->appendDefValue(t,l); }

void yyerrorf(const char* format, ...) {
    char msg[1024];

    va_list ap;
    va_start(ap,format);
    vsprintf(msg,format,ap);
    va_end(ap);

    yyerror(msg);
}

/**********************************************************************/
%}

%x CMTMODE
%x STRMODE
%x DEFFPAR
%x DEFFORM
%x DEFVAL
%x ARGMODE
%x INCMODE
%x PRTMODE

/* drop: Drop Ctrl-Z - can't pass thru or may EOF the output too soon */

ws		[ \t\f\r]
wsn		[ \t\f]
crnl		[\r]*[\n]
quote		[\"]
backslash	[\\]
symb		([a-zA-Z_][a-zA-Z0-9_$]*|\\[^ \t\f\r\n]+)
drop		[\032]

	/**************************************************************/
%%

<INITIAL>^{ws}*"`line"{ws}+.*{crnl}	{ LEXP->lineDirective(yytext);
					  return(VP_LINE); }

	/* Special directives we recognize */
<INITIAL>"`define"	{ return(VP_DEFINE); }
<INITIAL>"`else"	{ return(VP_ELSE); }
<INITIAL>"`elsif"	{ return(VP_ELSIF); }
<INITIAL>"`endif"	{ return(VP_ENDIF); }
<INITIAL>"`ifdef"	{ return(VP_IFDEF); }
<INITIAL>"`ifndef"	{ return(VP_IFNDEF); }
<INITIAL>"`include"	{ return(VP_INCLUDE); }
<INITIAL>"`undef"	{ return(VP_UNDEF); }
<INITIAL>"`undefineall"	{ return(VP_UNDEFINEALL); }

	/* Optional directives we recognize */
<INITIAL>"`__FILE__"	{ if (!pedantic()) {
			     static string rtnfile;
			     rtnfile = '"'; rtnfile += LEXP->m_curFilelinep->cfilename();
			     rtnfile += '"'; yytext=(char*)rtnfile.c_str(); yyleng = rtnfile.length();
			     return (VP_STRING);
	                  } else return(VP_DEFREF); }
<INITIAL>"`__LINE__"	{ if (!pedantic()) {
	                     static char buf[10];
			     sprintf(buf, "%d",LEXP->m_curFilelinep->lineno());
	                     yytext = buf; yyleng = strlen(yytext); return (VP_TEXT);
	                  } else return(VP_DEFREF); }
<INITIAL>"`error"	{ if (!pedantic()) return (VP_ERROR); else return(VP_DEFREF); }

	/* Pass-through strings */
<INITIAL>{quote}	{ yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated string"); yyleng=0; yyterminate(); }
<STRMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>[^\"\\]	{ yymore(); }
<STRMODE>{backslash}{crnl}	{ linenoInc(); yymore(); }
<STRMODE>{backslash}.	{ yymore(); }
<STRMODE>{quote} 	{ yy_pop_state();
			  if (LEXP->m_parenLevel || LEXP->m_formalLevel) { appendDefValue(yytext,yyleng); yyleng=0; }
			  else return (VP_STRING); }

	/* Protected blocks */
<INITIAL>"`protected"	{ yy_push_state(PRTMODE); yymore(); }
<PRTMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in `protected"); yyleng=0; yyterminate(); }
<PRTMODE>{crnl}		{ linenoInc(); yymore(); }
<PRTMODE>.	 	{ yymore(); }
<PRTMODE>"`endprotected" { yy_pop_state(); return (VP_TEXT); }

	/* Pass-through include <> filenames */
<INCMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated include filename"); yyleng=0; yyterminate(); }
<INCMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated include filename"); BEGIN(INITIAL); }
<INCMODE>[^\>\\]	{ yymore(); }
<INCMODE>{backslash}.	{ yymore(); }
<INCMODE>[\>]	 	{ yy_pop_state(); return (VP_STRING); }

	/* Reading definition formal parenthesis (or not) to begin formal arguments */
	/* Note '(' must IMMEDIATELY follow definition name */
<DEFFPAR>[(]		{ appendDefValue("(",1); LEXP->m_formalLevel=1; BEGIN(DEFFORM); }
<DEFFPAR>{crnl}		{ yy_pop_state(); unput('\n'); yyleng=0; return VP_DEFFORM; } /* DEFVAL will later grab the return */
<DEFFPAR><<EOF>>	{ yy_pop_state(); return VP_DEFFORM; }  /* empty formals */
<DEFFPAR>.		{ yy_pop_state(); unput(yytext[yyleng-1]); yyleng=0; return VP_DEFFORM; }  /* empty formals */

	/* Reading definition formals */
<DEFFORM>[(]		{ appendDefValue(yytext,yyleng); yyleng=0; ++LEXP->m_formalLevel; }
<DEFFORM>[)]		{ appendDefValue(yytext,yyleng); yyleng=0; if ((--LEXP->m_formalLevel)==0) { yy_pop_state(); return VP_DEFFORM; } }
<DEFFORM>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFFORM>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFFORM>{drop}		{ }
<DEFFORM><<EOF>>	{ linenoInc(); yy_pop_state(); yyerrorf("Unterminated ( in define formal arguments."); yyleng=0; return VP_DEFFORM; }
<DEFFORM>{crnl}		{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFFORM>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFFORM>{quote}	{ yy_push_state(STRMODE); yymore(); }
<DEFFORM>[{\[]		{ LEXP->m_formalLevel++; appendDefValue(yytext,yyleng); }
<DEFFORM>[}\]]		{ LEXP->m_formalLevel--; appendDefValue(yytext,yyleng); }
<DEFFORM>[^\/\*\n\r\\(){}\[\]\"]+	|
<DEFFORM>[\\][^\n\r]	|
<DEFFORM>.		{ appendDefValue(yytext,yyleng); }

	/* Reading definition value */
<DEFVAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<DEFVAL>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFVAL>{drop}		{ }
<DEFVAL><<EOF>>		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); } /* Technically illegal, but people complained */
<DEFVAL>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); }
<DEFVAL>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); } /* Include return so can maintain output line count */
<DEFVAL>[^\/\*\n\r\\]+	|
<DEFVAL>[\\][^\n\r]	|
<DEFVAL>.		{ appendDefValue(yytext,yyleng); }

	/* Define arguments */
<ARGMODE>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<ARGMODE>"//"[^\n\r]*	{ return (VP_COMMENT);}
<ARGMODE>{drop}		{ }
<ARGMODE><<EOF>>	{ yyerrorf("EOF in define argument list\n"); yyleng = 0; yyterminate(); }
<ARGMODE>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<ARGMODE>{quote}	{ yy_push_state(STRMODE); yymore(); }
<ARGMODE>[{\[]		{ LEXP->m_parenLevel++; appendDefValue(yytext,yyleng); }
<ARGMODE>[}\]]		{ LEXP->m_parenLevel--; appendDefValue(yytext,yyleng); }
<ARGMODE>[(]		{ LEXP->m_parenLevel++;
			  // Note paren level 0 means before "(" of starting args
			  // Level 1 means "," between arguments
			  // Level 2+ means one argument's internal ()
			  if (LEXP->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      return (VP_TEXT);
			}}
<ARGMODE>[)]		{ LEXP->m_parenLevel--;
			  if (LEXP->m_parenLevel>0) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>[,]		{ if (LEXP->m_parenLevel>1) {
			      appendDefValue(yytext,yyleng);
			  } else {
			      yy_pop_state(); return (VP_DEFARG);
			}}
<ARGMODE>"`"{symb}	{ return (VP_DEFREF); }  /* defref in defref */
<ARGMODE>[^\/\*\n\r\\(,){}\[\]\"`]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"[^\n\r]* 	{ return (VP_COMMENT); }

	/* C-style comments. */
<INITIAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTMODE>{crnl}		{ linenoInc(); yymore(); }
<CMTMODE>.		{ yymore(); }
<CMTMODE><<EOF>>	{ yyerrorf("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }

	/* Define calls */
<INITIAL>"`"{symb}	{ return (VP_DEFREF); }

	/* Generics */
<INITIAL><<EOF>> 	{ yyterminate(); }  /* A "normal" EOF */
<INITIAL>{crnl}		{ linenoInc(); yytext=(char*)"\n"; yyleng=1; return(VP_WHITE); }
<INITIAL>{symb}		{ return (VP_SYMBOL); }
<INITIAL>[\r]		{ }
<INITIAL>{wsn}+		{ if (!keepWhitespace()) { yytext=(char*)" "; yyleng=1; } return VP_WHITE; }
<INITIAL>{drop}		{ }
<INITIAL>.		{ return (VP_TEXT); }

<*>.|\n			{ yymore(); }	/* Prevent hitting ECHO; */
%%

void VPreprocLex::pushStateDefArg(int level) {
    // Enter define substitution argument state
    yy_push_state(ARGMODE);
    m_parenLevel = level;
    m_defValue = "";
}

void VPreprocLex::pushStateDefForm() {
    // Enter define formal arguments state
    yy_push_state(DEFFPAR);  // First is an optional ( to begin args
    m_parenLevel = 0;
    m_defValue = "";
}

void VPreprocLex::pushStateDefValue() {
    // Enter define value state
    yy_push_state(DEFVAL);
    m_parenLevel = 0;
    m_defValue = "";
}

void VPreprocLex::pushStateIncFilename() {
    // Enter include <> filename state
    yy_push_state(INCMODE);
    yymore();
}

void VPreprocLex::scanBytes(const string& strg) {
    yy_scan_bytes(strg.c_str(), strg.length());
    m_bufferStack.push(currentBuffer());  // yy_scan_bytes makes new buffer
}

void VPreprocLex::appendDefValue(const char* textp, int len) {
    // Append given text to current definition value being formed
    m_defValue.append(textp,len);
}

YY_BUFFER_STATE VPreprocLex::currentBuffer() {
    return YY_CURRENT_BUFFER;
}

int VPreprocLex::currentStartState() {
    return YY_START;
}

void VPreprocLex::dumpStack() {
    // For debug use
    stack<YY_BUFFER_STATE> tmpstack = m_bufferStack;
    printf("  bufferStack[%p]:",this);
    while (!tmpstack.empty()) {
	printf(" %p",tmpstack.top());
	tmpstack.pop();
    }
    printf("\n");
}

void VPreprocLex::unused() {
    if (0) {
	// Prevent unused warnings
	yy_top_state();
    }
}

/*###################################################################
 * Local Variables:
 * mode: C++
 * End:
 */
