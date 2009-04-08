// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2009 by Wilson Snyder.  This program is free software;
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
/// \brief Verilog::Preproc: Internal implementation of default preprocessor
///
/// Authors: Wilson Snyder
///
/// Code available from: http://www.veripool.org/verilog-perl
///
//*************************************************************************

#include <cstdio>
#include <fstream>
#include <cstring>
#include <stack>
#include <vector>
#include <map>
#include <cassert>

#include "VPreproc.h"
#include "VPreprocLex.h"

//#undef yyFlexLexer
//#define yyFlexLexer xxFlexLexer
//#include <FlexLexer.h>

//*************************************************************************

class VPreDefRef {
    // One for each pending define substitution
    string	m_name;		// Define last name being defined
    string	m_params;	// Define parameter list for next expansion
    string	m_nextarg;	// String being built for next argument
    int		m_parenLevel;	// Parenthesis counting inside def args

    vector<string> m_args;	// List of define arguments
public:
    string name() const { return m_name; }
    string params() const { return m_params; }
    string nextarg() const { return m_nextarg; }
    void nextarg(const string& value) { m_nextarg = value; }
    int parenLevel() const { return m_parenLevel; }
    vector<string>& args() { return m_args; }
    VPreDefRef(const string& name, const string& params, int pl)
	: m_name(name), m_params(params), m_parenLevel(pl) {}
    ~VPreDefRef() {}
};

//*************************************************************************
/// Data for parsing on/off

class VPreIfEntry {
    // One for each pending ifdef/ifndef
    bool	m_on;		// Current parse for this ifdef level is "on"
    bool	m_everOn;	// Some if term in elsif tree has been on
public:
    bool on() const { return m_on; }
    bool everOn() const { return m_everOn; }
    VPreIfEntry(bool on, bool everOn)
	: m_on(on), m_everOn(everOn || on) {}  // Note everOn includes new state
    ~VPreIfEntry() {}
};

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
    bool	m_lineCmtNl;	///< Newline needed before inserting lineCmt
    int		m_lineAdd;	///< Empty lines to return to maintain line count
    bool	m_rawAtBol;	///< Last rawToken left us at beginning of line

    // For defines
    stack<VPreDefRef> m_defRefs; // Pending definine substitution
    stack<VPreIfEntry> m_ifdefStack;	///< Stack of true/false emitting evaluations
    unsigned	m_defDepth;	///< How many `defines deep

    // For getline()
    string	m_lineChars;	///< Characters left for next line

    VPreprocImp(VFileLine* filelinep) {
	m_filelinep = filelinep;
	m_debug = 0;
	m_lexp = NULL;	 // Closed.
	m_state = ps_TOP;
	m_off = 0;
	m_lineChars = "";
	m_lastSym = "";
	m_lineAdd = 0;
	m_lineCmtNl = false;
	m_rawAtBol = true;
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
    void insertUnreadback(const string& text) { m_lineCmt += text; }
    void insertUnreadbackAtBol(const string& text);
private:
    void error(string msg) { m_filelinep->error(msg); }
    void fatal(string msg) { m_filelinep->fatal(msg); }
    int debug() const { return m_debug; }
    void eof();
    string defineSubst(VPreDefRef* refp);
    void addLineComment(int enter_exit_level);
    string trimWhitespace(const string& strg);

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
    case VP_LINE	: return("LINE");
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

string VPreprocImp::trimWhitespace(const string& strg) {
    string out = strg;
    while (out.length()>0 && isspace(out[0])) {
	out.erase(0,1);
    }
    return out;
}

string VPreprocImp::defineSubst(VPreDefRef* refp) {
    // Substitute out defines in a argumented define reference.
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parametrized define is used many, many times, we could cache the
    // parsed result.
    if (debug()) {
	cout<<"defineSubstIn  `"<<refp->name()<<" "<<refp->params()<<endl;
	for (unsigned i=0; i<refp->args().size(); i++) {
	    cout<<"defineArg["<<i<<"] = "<<refp->args()[i]<<endl;
	}
    }
    // Grab value
    string value = m_preprocp->defValue(refp->name());
    if (debug()) cout<<"defineValue    '"<<value<<"'"<<endl;

    map<string,string> argValueByName;
    {   // Parse argument list into map
	unsigned numArgs=0;
	string argName;
	for (const char* cp=refp->params().c_str(); *cp; cp++) {
	    if (*cp=='(') {
	    } else if (argName=="" && isspace(*cp)) {
	    } else if (isspace(*cp) || *cp==')' || *cp==',') {
		if (argName!="") {
		    if (refp->args().size() > numArgs) {
			// A call `def( a ) must be equivelent to `def(a ), so trimWhitespace
			// Note other sims don't trim trailing whitespace, so we don't either.
			argValueByName[argName] = trimWhitespace(refp->args()[numArgs]);
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
	if (refp->args().size() != numArgs) {
	    error("Define passed wrong number of arguments: "+refp->name()+"\n");
	    return " `"+refp->name()+" ";
	}
    }

    string out = "";
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

    if (debug()) cout<<"defineSubstOut '"<<out<<"'"<<endl;
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

void VPreprocImp::insertUnreadbackAtBol(const string& text) {
    // Insert insuring we're at the beginning of line, for `line
    // We don't always add a leading newline, as it may result in extra unreadback(newlines).
    if (m_lineCmt == "") { m_lineCmtNl = true; }
    else if (m_lineCmt[m_lineCmt.length()-1]!='\n') {
	insertUnreadback("\n");
    }
    insertUnreadback(text);
}

void VPreprocImp::addLineComment(int enter_exit_level) {
    if (m_preprocp->lineDirectives()) {
	char numbuf[20]; sprintf(numbuf, "%d", m_lexp->m_curFilelinep->lineno());
	char levelbuf[20]; sprintf(levelbuf, "%d", enter_exit_level);
	string cmt = ((string)"`line "+numbuf
		      +" \""+m_lexp->m_curFilelinep->filename()+"\" "
		      +levelbuf+"\n");
	insertUnreadbackAtBol(cmt);
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
	    m_rawAtBol = true;
	    yytext=(char*)"\n"; yyleng=1;
	    return (VP_TEXT);
	}
	if (m_lineCmt!="") {
	    // We have some `line directive to return to the user.  Do it.
	    static string rtncmt;  // Keep the c string till next call
	    rtncmt = m_lineCmt;
	    if (m_lineCmtNl) {
		if (!m_rawAtBol) rtncmt = "\n"+rtncmt;
		m_lineCmtNl = false;
	    }
	    yytext=(char*)rtncmt.c_str(); yyleng=rtncmt.length();
	    m_lineCmt = "";
	    if (yyleng) m_rawAtBol = (yytext[yyleng-1]=='\n');
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
	    string buf = string (yytext, yyleng);
	    string::size_type pos;
	    while ((pos=buf.find("\n")) != string::npos) { buf.replace(pos, 1, "\\n"); }
	    while ((pos=buf.find("\r")) != string::npos) { buf.replace(pos, 1, "\\r"); }
	    fprintf (stderr, "%d: RAW %s s%d dr%d:  %-10s: %s\n",
		     m_filelinep->lineno(), m_off?"of":"on", m_state, (int)m_defRefs.size(),
		     tokenName(tok), buf.c_str());
	}

	// On EOF, try to pop to upper level includes, as needed.
	if (tok==VP_EOF) {
	    eof();
	    goto next_tok;  // Parse parent, or find the EOF.
	}

	if (yyleng) m_rawAtBol = (yytext[yyleng-1]=='\n');
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
	if (tok==VP_LINE) {
	    addLineComment(0);
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
		    m_ifdefStack.push(VPreIfEntry(enable,false));
		    if (!enable) parsingOff();
		}
		else if (m_stateFor==VP_ELSIF) {
		    if (m_ifdefStack.empty()) {
			error("`elsif with no matching `if\n");
		    } else {
			// Handle `else portion
			VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
			if (!lastIf.on()) parsingOn();
			// Handle `if portion
			bool enable = !lastIf.everOn() && m_preprocp->defExists(m_lastSym);
			if (debug()) cout<<"Elsif "<<m_lastSym<<(enable?" ON":" OFF")<<endl;
			m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
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
		    m_lexp->pushStateDefValue();
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
		    if (debug()) cout<<"Define "<<m_lastSym<<" = '"<<m_lexp->m_defValue<<"'"<<endl;
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
		m_state = ps_DEFARG;
		goto next_tok;
	    } else {
		m_state = ps_TOP;
		if (m_defRefs.empty()) error("InternalError: Shouldn't be in DEFPAREN w/o active defref");
		VPreDefRef* refp = &(m_defRefs.top());
		error((string)"Expecting ( to begin argument list for define reference `"+refp->name()+"\n");
		goto next_tok;
	    }
	}
	case ps_DEFARG: {
	    if (m_defRefs.empty()) error("InternalError: Shouldn't be in DEFARG w/o active defref");
	    VPreDefRef* refp = &(m_defRefs.top());
	    refp->nextarg(refp->nextarg()+m_lexp->m_defValue); m_lexp->m_defValue="";
	    if (tok==VP_DEFARG && yyleng==1 && yytext[0]==',') {
		refp->args().push_back(refp->nextarg());
		m_state = ps_DEFARG;
		m_lexp->pushStateDefArg(1);
		refp->nextarg("");
		goto next_tok;
	    } else if (tok==VP_DEFARG && yyleng==1 && yytext[0]==')') {
		refp->args().push_back(refp->nextarg());
		string out = defineSubst(refp);
		// Substitute in and prepare for next action
		// Similar code in non-parenthesized define (Search for END_OF_DEFARG)
		m_defRefs.pop();
		m_lexp->unputString(out.c_str());
		if (m_defRefs.empty()) {
		    m_state = ps_TOP;
		    m_lexp->m_parenLevel = 0;
		}
		else {  // Finished a defref inside a upper defref
		    refp = &(m_defRefs.top());  // We popped, so new top
		    m_lexp->m_parenLevel = refp->parenLevel();
		    m_state = ps_DEFARG;
		}
		goto next_tok;
	    } else if (tok==VP_DEFREF) {
		// Expand it, then state will come back here
		// Value of building argument is data before the lower defref
		// we'll append it when we push the argument.
		break;
	    } else if (tok==VP_SYMBOL || tok==VP_STRING || VP_TEXT || VP_WHITE) {
		string rtn; rtn.assign(yytext,yyleng);
		refp->nextarg(refp->nextarg()+rtn);
		goto next_tok;
	    } else {
		error((string)"Expecting ) or , to end argument list for define reference. Found: "+tokenName(tok));
		m_state = ps_TOP;
		goto next_tok;
	    }
	}
	case ps_INCNAME: {
	    if (tok==VP_STRING) {
		m_state = ps_TOP;
		m_lastSym.assign(yytext,yyleng);
		if (debug()) cout<<"Include "<<m_lastSym<<endl;
		// Drop leading and trailing quotes.
		m_lastSym.erase(0,1);
		m_lastSym.erase(m_lastSym.length()-1,1);
		m_preprocp->include(m_lastSym);
		goto next_tok;
	    }
	    else if (tok==VP_TEXT && yyleng==1 && yytext[0]=='<') {
		// include <filename>
		m_state = ps_INCNAME;  // Still
		m_lexp->pushStateIncFilename();
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
	    if (!m_off) {
		m_state = ps_INCNAME;  m_stateFor = tok;
	    }
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
		VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
		bool enable = !lastIf.everOn();
		if (debug()) cout<<"Else "<<(enable?" ON":" OFF")<<endl;
		m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
		if (!lastIf.on()) parsingOn();
		if (!enable) parsingOff();
	    }
	    goto next_tok;
	case VP_ENDIF:
	    if (debug()) cout<<"Endif "<<endl;
	    if (m_ifdefStack.empty()) {
		error("`endif with no matching `if\n");
	    } else {
		VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
		if (!lastIf.on()) parsingOn();
		// parsingOn() really only enables parsing if
		// all ifdef's above this want it on
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
		    string out = m_preprocp->defValue(name);
		    if (debug()) cout<<"Defref `"<<name<<" => '"<<out<<"'"<<endl;
		    // Similar code in parenthesized define (Search for END_OF_DEFARG)
		    if (m_defRefs.empty()) {
			// Just output the substitution
			m_lexp->unputString(out.c_str());
		    } else {
			// Inside another define.  Can't subst now, or
			// `define a x,y
			// foo(`a,`b)  would break because a contains comma
			VPreDefRef* refp = &(m_defRefs.top());
			refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue="";
		    }
		    goto next_tok;
		}
		else {  // Found, with parameters
		    if (debug()) cout<<"Defref `"<<name<<" => parametrized"<<endl;
		    m_defRefs.push(VPreDefRef(name, params, m_lexp->m_parenLevel));
		    m_state = ps_DEFPAREN;  m_stateFor = tok;
		    m_lexp->pushStateDefArg(0);
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
	case VP_TEXT: {
	    m_defDepth = 0;
	    if (!m_off) return tok;
	    else goto next_tok;
	}
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
	const char* rtnp;
	bool gotEof = false;
	while (NULL==(rtnp=strchr(m_lineChars.c_str(),'\n')) && !gotEof) {
	    int tok = getToken();
	    if (debug()) {
		string buf = string (yytext, yyleng);
		string::size_type pos;
		while ((pos=buf.find("\n")) != string::npos) { buf.replace(pos, 1, "\\n"); }
		while ((pos=buf.find("\r")) != string::npos) { buf.replace(pos, 1, "\\r"); }
		fprintf (stderr,"%d: GETFETC:  %-10s: %s\n",
			 m_filelinep->lineno(), tokenName(tok), buf.c_str());
	    }
	    if (tok==VP_EOF) {
		// Add a final newline, if the user forgot the final \n.
		// Note tok==VP_EOF isn't always seen by us, as isEof() may be set earlier
		if (m_lineChars != "" && m_lineChars[m_lineChars.length()-1] != '\n') {
		    m_lineChars.append("\n");
		}
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
