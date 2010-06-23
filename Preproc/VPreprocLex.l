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
 * Copyright 2000-2010 by Wilson Snyder.  This program is free software;
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
void appendDefValue(const char* t, size_t l) { LEXP->appendDefValue(t,l); }

#define YY_INPUT(buf,result,max_size) \
    result = LEXP->inputToLex(buf,max_size);

// Accessors, because flex keeps changing the type of yyleng
char* yyourtext() { return yytext; }
size_t yyourleng() { return (size_t)yyleng; }
void yyourtext(const char* textp, size_t size) { yytext=(char*)textp; yyleng=size; }

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
%x DEFCMT
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
word		[a-zA-Z0-9_]+
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
<INITIAL>"`__FILE__"	{ static string rtnfile;
			  rtnfile = '"'; rtnfile += LEXP->m_curFilelinep->filename();
			  rtnfile += '"'; yytext=(char*)rtnfile.c_str(); yyleng = rtnfile.length();
			  return (VP_STRING); }
<INITIAL>"`__LINE__"	{ static char buf[10];
			  sprintf(buf, "%d",LEXP->m_curFilelinep->lineno());
	                  yytext = buf; yyleng = strlen(yytext);
			  return (VP_TEXT); }
<INITIAL>"`error"	{ if (!pedantic()) return (VP_ERROR); else return(VP_DEFREF); }

	/* Pass-through strings */
<INITIAL>{quote}	{ yy_push_state(STRMODE); yymore(); }
<STRMODE><<EOF>>	{ linenoInc(); yyerrorf("EOF in unterminated string"); yyleng=0; yyterminate(); }
<STRMODE>{crnl}		{ linenoInc(); yyerrorf("Unterminated string"); BEGIN(INITIAL); }
<STRMODE>{word}		{ yymore(); }
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
<DEFVAL>"/*"		{ LEXP->m_defCmtSlash=false; yy_push_state(DEFCMT); yymore(); }  /* Special comment parser */
<DEFVAL>"//"[^\n\r]*[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); }  /* Spec says // not part of define value */
<DEFVAL>"//"[^\n\r]*	{ return (VP_COMMENT);}
<DEFVAL>{drop}		{ }
<DEFVAL><<EOF>>		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); } /* Technically illegal, but people complained */
<DEFVAL>{crnl}		{ linenoInc(); yy_pop_state(); yytext=(char*)"\n"; yyleng=1; return (VP_DEFVALUE); }
<DEFVAL>[\\]{crnl}	{ linenoInc(); appendDefValue((char*)"\n",1); } /* Return, but not \ is part of define value */
<DEFVAL>[^\/\*\n\r\\]+	|
<DEFVAL>[\\][^\n\r]	|
<DEFVAL>.		{ appendDefValue(yytext,yyleng); }

	/* Comments inside define values - if embedded get added to define value per spec */
	/* - if no \{crnl} ending then the comment belongs to the next line, as a non-embedded comment */
	/* - if all but (say) 3rd line is missing \ then it's indeterminate */
<DEFCMT>"*/"		{ yy_pop_state(); appendDefValue(yytext,yyleng); }
<DEFCMT>[\\]{crnl}	{ linenoInc(); LEXP->m_defCmtSlash=true;
	 		  appendDefValue(yytext,yyleng-2); appendDefValue((char*)"\n",1); }  /* Return but not \ */
<DEFCMT>{crnl}		{ linenoInc(); yymore(); if (LEXP->m_defCmtSlash) yyerrorf("One line of /* ... */ is missing \\ before newline");
			  BEGIN(CMTMODE); }
<DEFCMT>{word}		{ yymore(); }
<DEFCMT>.		{ yymore(); }
<DEFCMT><<EOF>>		{ yyerrorf("EOF in '/* ... */' block comment\n"); yyleng=0; yyterminate(); }

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
<ARGMODE>"`"{symb}	{ appendDefValue(yytext,yyleng); }  /* defref in defref */
<ARGMODE>[^\/\*\n\r\\(,){}\[\]\"`]+	|
<ARGMODE>.		{ appendDefValue(yytext,yyleng); }

	/* One line comments. */
<INITIAL>"//"[^\n\r]* 	{ return (VP_COMMENT); }

	/* C-style comments. */
	/**** See also DEFCMT */
<INITIAL>"/*"		{ yy_push_state(CMTMODE); yymore(); }
<CMTMODE>"*/"		{ yy_pop_state(); return(VP_COMMENT); }
<CMTMODE>{crnl}		{ linenoInc(); yymore(); }
<CMTMODE>{word}		{ yymore(); }
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

void VPreprocLex::initFirstBuffer() {
    // Called from constructor to make first buffer
    // yy_create_buffer also sets yy_fill_buffer=1 so reads from YY_INPUT
    yy_switch_to_buffer(yy_create_buffer(NULL, YY_BUF_SIZE));
    m_bufferStack.push(currentBuffer());
    yyrestart(NULL);
}

size_t VPreprocLex::inputToLex(char* buf, size_t max_size) {
    // We need a custom YY_INPUT because we can't use flex buffers.
    // Flex buffers are limited to 2GB, and we can't chop into 2G pieces
    // because buffers can't end in the middle of tokens.
    // m_buffers only applies to the "base" buffer when there's no scanBytes outstanding
    // It won't be called on scan_buffers as they don't have yy_fill_buffer set.
    //
    //if (debug()) { cout<<"-  pp:inputToLex ITL s="<<max_size<<" bs="<<m_bufferStack.size()<<endl;  dumpSummary(); }
    // For testing, use really small chunks
    //if (max_size > 13) max_size=13;
    size_t got = 0;
    while (got < max_size	// Haven't got enough
	   && !m_buffers.empty()) {	// And something buffered
	string front = m_buffers.front(); m_buffers.pop_front();
	size_t len = front.length();
	if (len > (max_size-got)) {  // Front string too big
	    string remainder = front.substr(max_size-got);
	    front = front.substr(0, max_size-got);
	    m_buffers.push_front(remainder);  // Put back remainder for next time
	    len = (max_size-got);
	}
	strncpy(buf+got, front.c_str(), len);
	got += len;
    }
    //if (debug()) { cout<<"-  pp::inputToLex  got="<<got<<" '"<<string(buf,got)<<"'"<<endl; }
    return got;
}

void VPreprocLex::scanBytes(const char* strp, size_t len) {
    // Note buffers also appended in ::scanBytesBack
    // Not "m_buffers.push_front(string(strp,len))" as we need a `define
    // to take effect immediately, in the middle of the current buffer
    yy_scan_bytes(strp, len);
    m_bufferStack.push(currentBuffer());  // yy_scan_bytes makes new buffer
}

void VPreprocLex::scanBytesBack(const string& str) {
    // Initial creation, that will pull from YY_INPUT==inputToLex
    // Note buffers also appended in ::scanBytes
    m_buffers.push_back(str);
}

void VPreprocLex::appendDefValue(const char* textp, size_t len) {
    // Append given text to current definition value being formed
    m_defValue.append(textp,len);
}

YY_BUFFER_STATE VPreprocLex::currentBuffer() {
    return YY_CURRENT_BUFFER;
}

int VPreprocLex::currentStartState() {
    return YY_START;
}

void VPreprocLex::dumpSummary() {
    cout<<"-  pp::dumpSummary  curBuf="<<(void*)(currentBuffer())
	<<" nBuf="<<m_bufferStack.size()
	<<" yyfill="<<currentBuffer()->yy_fill_buffer<<endl;
}

void VPreprocLex::dumpStack() {
    // For debug use
    dumpSummary();
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
