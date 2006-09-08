// $Id$  -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2006 by Wilson Snyder.  This program is free software;
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
/// \brief Verilog::Preproc: Internal implementation of default preprocessor
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.com/verilog-perl
///
//*************************************************************************

#include <stdio.h>
#include <fstream>
#include <stack>
#include <vector>
#include <map>
#include <assert.h>

#include "VPreproc.h"
#include "VPreprocLex.h"

//#undef yyFlexLexer
//#define yyFlexLexer xxFlexLexer
//#include <FlexLexer.h>

//*************************************************************************
/// Data for a preprocessor instantiation.

struct VPreprocImp : public VPreprocOpaque {
    VPreproc*	m_preprocp;	///< Object we're holding data for
    VFileLine*	m_filelinep;	///< Last token's starting point
    int		m_debug;	///< Debugging level
    VPreprocLex* m_lexp;	///< Current lexer state (NULL = closed)
    stack<VPreprocLex*> m_includeStack;	///< Stack of includers above current m_lexp

    enum ProcState { ps_TOP, ps_DEFNAME, ps_DEFVALUE, ps_DEFPAREN, ps_DEFARG,
		     ps_INCNAME, ps_ERRORNAME };
    ProcState	m_state;	///< Current state of parser
    int		m_stateFor;	///< Token state is parsing for
    int		m_off;		///< If non-zero, ifdef level is turned off, don't dump text
    string	m_lastSym;	///< Last symbol name found.

    // For getRawToken/ `line insertion
    string	m_lineCmt;	///< Line comment(s) to be returned
    int		m_lineAdd;	///< Empty lines to return to maintain line count

    // For defines
    string	m_defName;	///< Define last name being defined
    string	m_defParams;	///< Define parameter list for next expansion
    stack<bool> m_ifdefStack;	///< Stack of true/false emitting evaluations
    vector<string> m_defArgs;	///< List of define arguments
    unsigned	m_defDepth;	///< How many `defines deep

    // For getline()
    string	m_lineChars;	///< Characters left for next line

    VPreprocImp(VFileLine* filelinep) {
	m_filelinep = filelinep;
	m_debug = 0;
	m_lexp = NULL;	 // Closed.
	m_state = ps_TOP;
	m_defName = "";
	m_off = 0;
	m_lineChars = "";
	m_lastSym = "";
	m_lineAdd = 0;
	m_defDepth = 0;
    }
    const char* tokenName(int tok);
    int getRawToken();
    int getToken();
    void parseTop();
    void parseUndef();
    string getline();
    bool isEof() const { return (m_lexp==NULL); }
    void open(string filename, VFileLine* filelinep);
    void insertUnreadback(string text) { m_lineCmt += text; }
private:
    void error(string msg) { m_filelinep->error(msg); }
    void fatal(string msg) { m_filelinep->fatal(msg); }
    int debug() const { return m_debug; }
    void eof();
    string defineSubst();
    void addLineComment(int enter_exit_level);

    void parsingOn() { m_off--; assert(m_off>=0); if (!m_off) addLineComment(0); }
    void parsingOff() { m_off++; }
};

//*************************************************************************
// Creation

VPreproc::VPreproc(VFileLine* filelinep) {
    VPreprocImp* idatap = new VPreprocImp(filelinep);
    m_opaquep = idatap;
    idatap->m_preprocp = this;
}

//*************************************************************************
// VPreproc Methods.  Just call the implementation functions.

void VPreproc::comment(string cmt) { }
void VPreproc::open(string filename, VFileLine* filelinep) {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    idatap->open (filename,filelinep);
}
string VPreproc::getline() {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    return idatap->getline();
}
void VPreproc::debug(int level) {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    idatap->m_debug = level;
}
bool VPreproc::isEof() {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    return idatap->isEof();
}
VFileLine* VPreproc::filelinep() {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    return idatap->m_filelinep;
}
void VPreproc::insertUnreadback(string text) {
    VPreprocImp* idatap = static_cast<VPreprocImp*>(m_opaquep);
    return idatap->insertUnreadback(text);
}

//*************************************************************************

// CALLBACK METHODS
// This probably will want to be overridden for given child users of this class.

void VPreproc::include(string filename) {
    open(filename, filelinep());
}
void VPreproc::undef(string define) {
    cout<<"UNDEF "<<define<<endl;
}
bool VPreproc::defExists(string define) {
    return defParams(define)!="";
}
string VPreproc::defParams(string define) {
    return "";
}
void VPreproc::define(string define, string value, string params) {
    error("Defines not implemented: "+define+"\n");
}
string VPreproc::defValue(string define) {
    error("Define not defined: "+define+"\n");
    return define;
}

//**********************************************************************
// Parser Utilities

const char* VPreprocImp::tokenName(int tok) {
    switch (tok) {
    case VP_EOF		: return("EOF");
    case VP_INCLUDE	: return("INCLUDE");
    case VP_IFDEF	: return("IFDEF");
    case VP_IFNDEF	: return("IFNDEF");
    case VP_ENDIF	: return("ENDIF");
    case VP_UNDEF	: return("UNDEF");
    case VP_DEFINE	: return("DEFINE");
    case VP_ELSE	: return("ELSE");	
    case VP_ELSIF	: return("ELSIF");	
    case VP_SYMBOL	: return("SYMBOL");
    case VP_STRING	: return("STRING");
    case VP_DEFVALUE	: return("DEFVALUE");
    case VP_COMMENT	: return("COMMENT");
    case VP_TEXT	: return("TEXT");	
    case VP_WHITE	: return("WHITE");	
    case VP_DEFREF	: return("DEFREF");
    case VP_DEFARG	: return("DEFARG");
    case VP_ERROR	: return("ERROR");
    default: return("?");
    } 
}

string VPreprocImp::defineSubst() {
    // Substitute out defines in a argumented define reference.
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parametrized define is used many, many times, we could cache the
    // parsed result.
    if (debug()) {
	cout<<"defineSubstIn  `"<<m_defName<<" "<<m_defParams<<endl;
	for (unsigned i=0; i<m_defArgs.size(); i++) {
	    cout<<"defineArg["<<i<<"] = "<<m_defArgs[i]<<endl;
	}
    }
    // Grab value
    string value = m_preprocp->defValue(m_defName);
    if (debug()) cout<<"defineValue    `"<<value<<endl;

    map<string,string> argValueByName;
    {   // Parse argument list into map
	unsigned numArgs=0;
	string argName;
	for (const char* cp=m_defParams.c_str(); *cp; cp++) {
	    if (*cp=='(') {
	    } else if (argName=="" && isspace(*cp)) {
	    } else if (isspace(*cp) || *cp==')' || *cp==',') {
		if (argName!="") {
		    if (m_defArgs.size() >= numArgs) {
			argValueByName[argName] = m_defArgs[numArgs];
		    }
		    numArgs++;
		    //cout << "  arg "<<argName<<endl;
		}
		argName = "";
	    } else if ( isalpha(*cp) || *cp=='_'
			|| (argName!="" && (isdigit(*cp) || *cp=='$'))) {
		argName += *cp;
	    }
	}
	if (m_defArgs.size() != numArgs) {
	    error("Define passed wrong number of arguments: "+m_defName+"\n");
	    return " `"+m_defName+" ";
	}
    }

    string out = " ";
    {   // Parse substitution define using arguments
	string argName;
	string prev;
	bool quote = false;
	// Note we go through the loop once more at the NULL end-of-string
	for (const char* cp=value.c_str(); (*cp) || argName!=""; cp=(*cp?cp+1:cp)) {
	    //cout << "CH "<<*cp<<"  an "<<argName<<"\n";
	    if (!quote) {
		if ( isalpha(*cp) || *cp=='_'
		     || (argName!="" && (isdigit(*cp) || *cp=='$'))) {
		    argName += *cp;
		    continue;
		}
	    }
	    if (argName != "") {
		// Found a possible variable substitution
		map<string,string>::iterator iter = argValueByName.find(argName);
		if (iter != argValueByName.end()) {
		    // Substitute
		    string subst = iter->second;
		    out += subst;
		} else {
		    out += argName;
		}
		argName = "";
	    }
	    if (!quote) {
		// Check for `` only after we've detected end-of-argname
		if (cp[0]=='`' && cp[1]=='`') {
		    //out += "";   // `` means to suppress the ``
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='"') {
		    out += '"';   // `" means to put out a " without enabling quote mode (sort of)
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='\\') {
		    out += '\\';   // `\ means to put out a backslash
		    cp++;
		    continue;
		}
	    }
	    if (cp[0]=='\\' && cp[1]) {
		out += cp[0]; // \{any} Put out literal next character
		out += cp[1];
		cp++;
		continue;
	    }
	    if (*cp=='"') quote=!quote;
	    if (*cp) out += *cp;
	}
    }

    out += " ";
    if (debug()) cout<<"defineSubstOut "<<out<<endl;
    return out;
}

//**********************************************************************
// Parser routines

void VPreprocImp::open(string filename, VFileLine* filelinep) {
    // Open a new file, possibly overriding the current one which is active.
    if (filelinep) {
	m_filelinep = filelinep;
    }

    FILE* fp = fopen (filename.c_str(), "r");
    if (!fp) {
	error("File not found: "+filename+"\n");
	return;
    }

    if (m_lexp) {
	// We allow the same include file twice, because occasionally it pops
	// up, with guards preventing a real recursion.
	if (m_includeStack.size()>VPreproc::INCLUDE_DEPTH_MAX) {
	    error("Recursive inclusion of file: "+filename);
	    return;
	}
	// There's already a file active.  Push it to work on the new one.
	m_includeStack.push(m_lexp);
	addLineComment(0);
    }

    m_lexp = new VPreprocLex (fp);
    m_lexp->m_keepComments = m_preprocp->keepComments();
    m_lexp->m_keepWhitespace = m_preprocp->keepWhitespace();
    m_lexp->m_pedantic = m_preprocp->pedantic();
    m_lexp->m_curFilelinep = m_preprocp->filelinep()->create(filename, 1);
    m_filelinep = m_lexp->m_curFilelinep;  // Remember token start location
    addLineComment(1); // Enter

    yy_switch_to_buffer(m_lexp->m_yyState);
}

void VPreprocImp::addLineComment(int enter_exit_level) {
    if (m_preprocp->lineDirectives()) {
	char numbuf[20]; sprintf(numbuf, "%d", m_lexp->m_curFilelinep->lineno());
	char levelbuf[20]; sprintf(levelbuf, "%d", enter_exit_level);
	string cmt = ((string)"\n`line "+numbuf
		      +" \""+m_lexp->m_curFilelinep->filename()+"\" "
		      +levelbuf+"\n");
	insertUnreadback(cmt);
    }
}

void VPreprocImp::eof() {
    // Remove current lexer
    if (debug()) cout<<m_filelinep<<"EOF!\n";
    addLineComment(2);	// Exit
    delete m_lexp;  m_lexp=NULL;
    // Perhaps there's a parent file including us?
    if (!m_includeStack.empty()) {
	// Back to parent.
	m_lexp = m_includeStack.top(); m_includeStack.pop();
	addLineComment(0);
	yy_switch_to_buffer(m_lexp->m_yyState);
    }
}

int VPreprocImp::getRawToken() {
    // Get a token from the file, whatever it may be.
    while (1) {
      next_tok:
	if (m_lineAdd) {
	    m_lineAdd--;
	    yytext="\n"; yyleng=1;
	    return (VP_TEXT);
	}
	if (m_lineCmt!="") {
	    // We have some `line directive to return to the user.  Do it.
	    static string rtncmt;  // Keep the c string till next call
	    rtncmt = m_lineCmt;
	    yytext=(char*)rtncmt.c_str(); yyleng=rtncmt.length();
	    m_lineCmt = "";
	    if (m_state!=ps_DEFVALUE) return (VP_TEXT);
	    else {
		VPreprocLex::s_currentLexp->appendDefValue(yytext,yyleng); 
		goto next_tok;
	    }
	}
	if (isEof()) return (VP_EOF);
	// Snarf next token from the file
	m_filelinep = m_lexp->m_curFilelinep;  // Remember token start location
	VPreprocLex::s_currentLexp = m_lexp;   // Tell parser where to get/put data
	int tok = yylex();

	if (debug()) {
	    char buf[10000]; strncpy(buf, yytext, yyleng);  buf[yyleng] = '\0';
	    for (char* cp=buf; *cp; cp++) if (*cp=='\n') *cp='$';
	    fprintf (stderr,"%d: RAW %d %d:  %-10s: %s\n",
		     m_filelinep->lineno(), m_off, m_state, tokenName(tok), buf);
	}
    
	// On EOF, try to pop to upper level includes, as needed.
	if (tok==VP_EOF) {
	    eof();
	    goto next_tok;  // Parse parent, or find the EOF.
	}

	return tok;
    }
}

// Sorry, we're not using bison/yacc. It doesn't handle returning white space
// in the middle of parsing other tokens.

int VPreprocImp::getToken() {
    // Return the next user-visible token in the input stream.
    // Includes and such are handled here, and are never seen by the caller.
    while (1) {
      next_tok:
	if (isEof()) return VP_EOF;
	int tok = getRawToken();
	// Always emit white space and comments between tokens.
	if (tok==VP_WHITE) return (tok);
	if (tok==VP_COMMENT) {
	    if (!m_off && m_lexp->m_keepComments) {
		if (m_lexp->m_keepComments == KEEPCMT_SUB
		    || m_lexp->m_keepComments == KEEPCMT_EXP) {
		    string rtn; rtn.assign(yytext,yyleng);
		    m_preprocp->comment(rtn);
		} else {
		    return (tok);
		}
	    }
	    // We're off or processed the comment specially.  If there are newlines
	    // in it, we also return the newlines as TEXT so that the linenumber
	    // count is maintained for downstream tools
	    for (int len=0; len<yyleng; len++) { if (yytext[len]=='\n') m_lineAdd++; }
	    goto next_tok;
	}
	// Deal with some special parser states
	switch (m_state) {
	case ps_TOP: {
	    break;
	}
	case ps_DEFNAME: {
	    if (tok==VP_SYMBOL) {
		m_state = ps_TOP;
		m_lastSym.assign(yytext,yyleng);
		if (m_stateFor==VP_IFDEF
		    || m_stateFor==VP_IFNDEF) {
		    bool enable = m_preprocp->defExists(m_lastSym);
		    if (debug()) cout<<"Ifdef "<<m_lastSym<<(enable?" ON":" OFF")<<endl;
		    if (m_stateFor==VP_IFNDEF) enable = !enable;
		    m_ifdefStack.push(enable);
		    if (!enable) parsingOff();
		}
		else if (m_stateFor==VP_ELSIF) {
		    if (m_ifdefStack.empty()) {
			error("`elsif with no matching `if\n");
		    } else {
			// Handle `else portion
			bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
			if (!lastEnable) parsingOn();
			// Handle `if portion
			bool enable = !lastEnable && m_preprocp->defExists(m_lastSym);
			if (debug()) cout<<"Elsif "<<m_lastSym<<(enable?" ON":" OFF")<<endl;
			m_ifdefStack.push(enable);
			if (!enable) parsingOff();
		    }
		}
		else if (m_stateFor==VP_UNDEF) {
		    if (!m_off) {
			if (debug()) cout<<"Undef "<<m_lastSym<<endl;
			m_preprocp->undef(m_lastSym);
		    }
		}
		else if (m_stateFor==VP_DEFINE) {
		    // m_lastSym already set.
		    m_state = ps_DEFVALUE;
		    m_lexp->setStateDefValue();
		}
		else fatalSrc("Bad case\n");
		goto next_tok;
	    }
	    else {
		error((string)"Expecting define name. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	case ps_DEFVALUE: {
 	    static string newlines;
	    newlines = "\n";  // Always start with trailing return
	    if (tok == VP_DEFVALUE) {
		// Remove returns
		for (unsigned i=0; i<m_lexp->m_defValue.length(); i++) {
		    if (m_lexp->m_defValue[i] == '\n') {
			m_lexp->m_defValue[i] = ' ';
			newlines += "\n";
		    }
		}
		if (!m_off) {
		    string params;
		    if (m_lexp->m_defValue=="" || isspace(m_lexp->m_defValue[0])) {
			// Define without parameters
		    } else if (m_lexp->m_defValue[0] == '(') {
			string::size_type paren = m_lexp->m_defValue.find(")");
			if (paren == string::npos) {
			    error((string)"Missing ) to end define arguments.\n");
			} else {
			    params = m_lexp->m_defValue.substr(0, paren+1);
			    m_lexp->m_defValue.replace(0, paren+1, "");
			}
		    } else {
			error((string)"Missing space or paren to start define value.\n");
		    }
		    // Remove leading whitespace
		    unsigned leadspace = 0;
		    while (m_lexp->m_defValue.length() > leadspace
		    	   && isspace(m_lexp->m_defValue[leadspace])) leadspace++;
		    if (leadspace) m_lexp->m_defValue.erase(0,leadspace);
		    // Remove trailing whitespace
		    unsigned trailspace = 0;
		    while (m_lexp->m_defValue.length() > trailspace
			   && isspace(m_lexp->m_defValue[m_lexp->m_defValue.length()-1-trailspace])) trailspace++;
		    if (trailspace) m_lexp->m_defValue.erase(m_lexp->m_defValue.length()-trailspace,trailspace);
		    // Define it
		    if (debug()) cout<<"Define "<<m_lastSym<<" = "<<m_lexp->m_defValue<<endl;
		    m_preprocp->define(m_lastSym, m_lexp->m_defValue, params);
		}
	    } else {
		fatalSrc("Bad define text\n");
	    }
	    m_state = ps_TOP;
	    // DEFVALUE is terminated by a return, but lex can't return both tokens.
	    // Thus, we emit a return here.
	    yytext=(char*)(newlines.c_str()); yyleng=newlines.length();
	    return(VP_WHITE); 
	}
	case ps_DEFPAREN: {
	    if (tok==VP_TEXT && yyleng==1 && yytext[0]=='(') {
		m_defArgs.clear();
		m_state = ps_DEFARG;
		m_lexp->setStateDefArg();
		goto next_tok;
	    } else {
		m_state = ps_TOP;
		error((string)"Expecting ( to begin argument list for define reference `"+m_defName+"\n");
		goto next_tok;
	    }
	}
	case ps_DEFARG: {
	    if (tok==VP_DEFARG) {
		if (debug()) cout<<"   Defarg "<<m_defName<<" arg="<<m_lexp->m_defValue<<endl;
		goto next_tok;  // Next is a , or )
	    } else if (tok==VP_TEXT && yyleng==1 && yytext[0]==',') {
		m_defArgs.push_back(m_lexp->m_defValue);
		m_state = ps_DEFARG;
		m_lexp->setStateDefArg();
		goto next_tok;
	    } else if (tok==VP_TEXT && yyleng==1 && yytext[0]==')') {
		m_defArgs.push_back(m_lexp->m_defValue);
		string out = defineSubst();
		m_lexp->m_parenLevel = 0;
		m_lexp->unputString(out.c_str());
		// Prepare for next action
		m_defArgs.clear();
		m_state = ps_TOP;
		goto next_tok;
	    } else {
		error((string)"Expecting ) or , to end argument list for define reference. Found: "+tokenName(tok)+"\n");
		m_state = ps_TOP;
		goto next_tok;
	    }
	    goto next_tok;
	}
	case ps_INCNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		if (!m_off) {
		    m_lastSym.assign(yytext,yyleng);
		    if (debug()) cout<<"Include "<<m_lastSym<<endl;
		    // Drop leading and trailing quotes.
		    m_lastSym.erase(0,1);
		    m_lastSym.erase(m_lastSym.length()-1,1);
		    m_preprocp->include(m_lastSym);
		}
		goto next_tok;
	    }
	    else if (tok==VP_TEXT && yyleng==1 && yytext[0]=='<') {
		// include <filename>
		m_state = ps_INCNAME;  // Still
		m_lexp->setStateIncFilename();
		goto next_tok;
	    }
	    else if (tok==VP_DEFREF) {
		// Expand it, then state will come back here
		break;
	    }
	    else {
		m_state = ps_TOP;
		error((string)"Expecting include filename. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	case ps_ERRORNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		if (!m_off) {
		    m_lastSym.assign(yytext,yyleng);
		    error(m_lastSym);
		}
		goto next_tok;
	    }
	    else {
		m_state = ps_TOP;
		error((string)"Expecting `error string. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	default: fatalSrc("Bad case\n");
	}
	// Default is to do top level expansion of some tokens
	switch (tok) {
	case VP_INCLUDE:
	    m_state = ps_INCNAME;  m_stateFor = tok;
	    goto next_tok;
	case VP_UNDEF:
	case VP_DEFINE:
	case VP_IFDEF:
	case VP_IFNDEF:
	case VP_ELSIF:
	    m_state = ps_DEFNAME;  m_stateFor = tok;
	    goto next_tok;
	case VP_ELSE:
	    if (m_ifdefStack.empty()) {
		error("`else with no matching `if\n");
	    } else {
		bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
		bool enable = !lastEnable;
		if (debug()) cout<<"Else "<<(enable?" ON":" OFF")<<endl;
		m_ifdefStack.push(enable);
		if (!lastEnable) parsingOn();
		if (!enable) parsingOff();
	    }
	    goto next_tok;
	case VP_ENDIF:
	    if (m_ifdefStack.empty()) {
		error("`endif with no matching `if\n");
	    } else {
		bool lastEnable = m_ifdefStack.top(); m_ifdefStack.pop();
		if (debug()) cout<<"Endif "<<endl;
		if (!lastEnable) parsingOn();
	    }
	    goto next_tok;

	case VP_DEFREF: {
	    if (!m_off) {
		string name; name.append(yytext+1,yyleng-1);
		if (debug()) cout<<"DefRef "<<name<<endl;
		if (m_defDepth++ > VPreproc::DEFINE_RECURSION_LEVEL_MAX) {
		    error("Recursive `define substitution: `"+name);
		    goto next_tok;
		}
		//
		string params = m_preprocp->defParams(name);
		if (params=="") {   // Not found, return original string as-is
		    m_defDepth = 0;
		    if (debug()) cout<<"Defref `"<<name<<" => not_defined"<<endl;
		    return (VP_TEXT);
		}
		else if (params=="0") {  // Found, as simple substitution
		    // Pack spaces around the define value, as there must be token boundaries around it.
		    // It also makes it more obvious where defines got substituted.
		    string out = " "+m_preprocp->defValue(name)+" ";
		    if (debug()) cout<<"Defref `"<<name<<" => "<<out<<endl;
		    m_lexp->unputString(out.c_str());
		    goto next_tok;
		}
		else {  // Found, with parameters
		    if (debug()) cout<<"Defref `"<<name<<" => parametrized"<<endl;
		    m_defName = name;
		    m_defParams = params;
		    m_state = ps_DEFPAREN;  m_stateFor = tok;
		    goto next_tok;
		}
		fatalSrc("Bad case\n");
	    }
	    else goto next_tok;
	}
	case VP_ERROR: {
	    m_state = ps_ERRORNAME;  m_stateFor = tok;
	    goto next_tok;
	}
	case VP_EOF:
	    if (!m_ifdefStack.empty()) {
		error("`ifdef not terminated at EOF\n");
	    }
	    return tok;
	case VP_SYMBOL:
	case VP_STRING:
	case VP_TEXT:
	    m_defDepth = 0;
	    if (!m_off) return tok;
	    else goto next_tok;
	case VP_WHITE:		// Handled at top of loop
	case VP_COMMENT:	// Handled at top of loop
	case VP_DEFVALUE:	// Handled by m_state=ps_DEFVALUE;
	default:
	    fatalSrc("Internal error: Unexpected token.\n");
	    break;
	}
	return tok;
    }
}

string VPreprocImp::getline() {
    // Get a single line from the parse stream.  Buffer unreturned text until the newline.
    if (isEof()) return "";
    while (1) {
	char* rtnp;
	bool gotEof = false;
	while (NULL==(rtnp=strchr(m_lineChars.c_str(),'\n'))) {
	    int tok = getToken();
	    if (debug()) {
		char buf[100000];
		strncpy(buf, yytext, yyleng);
		buf[yyleng] = '\0';
		for (char* cp=buf; *cp; cp++) if (*cp=='\n') *cp='$';
		fprintf (stderr,"%d: GETFETC:  %-10s: %s\n",
			 m_filelinep->lineno(), tokenName(tok), buf);
	    }
	    if (tok==VP_EOF) {
		// Add a final newline, in case the user forgot the final \n.
		m_lineChars.append("\n");
		gotEof = true;
	    }
	    else {
		m_lineChars.append(yytext,0,yyleng);
	    }
	}

	// Make new string with data up to the newline.
	int len = rtnp-m_lineChars.c_str()+1;
	string theLine(m_lineChars, 0, len);
	m_lineChars = m_lineChars.erase(0,len);	// Remove returned characters

	if (!m_preprocp->keepWhitespace() && !gotEof) {
	    const char* cp=theLine.c_str();
	    for (; *cp && (isspace(*cp) || *cp=='\n'); cp++) {}
	    if (!*cp) continue;
	}

	if (debug()) fprintf (stderr,"%d: GETLINE:  %s\n", m_filelinep->lineno(), theLine.c_str());
	return theLine;
    }
}
