// -*- C++ -*-
//*************************************************************************
//
// Copyright 2000-2017 by Wilson Snyder.  This program is free software;
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
#include <cstdlib>
#include <fstream>
#include <cstring>
#include <stack>
#include <vector>
#include <map>
#include <list>
#include <cassert>
#include <cerrno>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

#include "VPreProc.h"
#include "VPreLex.h"

//#undef yyFlexLexer
//#define yyFlexLexer xxFlexLexer
//#include <FlexLexer.h>

//*************************************************************************

class VPreDefRef {
    // One for each pending define substitution
    string	m_name;		// Define last name being defined
    string	m_params;	// Define parameter list for next expansion
    string	m_nextarg;	// String being built for next argument
    int		m_parenLevel;	// Parenthesis counting inside def args (for PARENT not child)

    vector<string> m_args;	// List of define arguments
public:
    string name() const { return m_name; }
    string params() const { return m_params; }
    string nextarg() const { return m_nextarg; }
    void nextarg(const string& value) { m_nextarg = value; }
    int parenLevel() const { return m_parenLevel; }
    void parenLevel(int value) { m_parenLevel = value; }
    vector<string>& args() { return m_args; }
    VPreDefRef(const string& name, const string& params)
	: m_name(name), m_params(params), m_parenLevel(0) {}
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

class VPreProcImp : public VPreProcOpaque {
public:
    typedef list<string> StrList;

    VPreProc*	m_preprocp;	///< Object we're holding data for
    int		m_debug;	///< Debugging level
    VPreLex*	m_lexp;		///< Current lexer state (NULL = closed)

    enum ProcState { ps_TOP,
		     ps_DEFNAME_UNDEF, ps_DEFNAME_DEFINE,
		     ps_DEFNAME_IFDEF, ps_DEFNAME_IFNDEF, ps_DEFNAME_ELSIF,
		     ps_DEFFORM, ps_DEFVALUE, ps_DEFPAREN, ps_DEFARG,
		     ps_INCNAME, ps_ERRORNAME, ps_JOIN, ps_STRIFY };
    const char* procStateName(ProcState s) {
	static const char* states[]
	    = {"ps_TOP",
	       "ps_DEFNAME_UNDEF", "ps_DEFNAME_DEFINE",
	       "ps_DEFNAME_IFDEF", "ps_DEFNAME_IFNDEF", "ps_DEFNAME_ELSIF",
	       "ps_DEFFORM", "ps_DEFVALUE", "ps_DEFPAREN", "ps_DEFARG",
	       "ps_INCNAME", "ps_ERRORNAME", "ps_JOIN", "ps_STRIFY" };
	return states[s];
    };

    stack<ProcState>	m_states; ///< Current state of parser
    int		m_off;		///< If non-zero, ifdef level is turned off, don't dump text
    string	m_lastSym;	///< Last symbol name found.
    string	m_formals;	///< Last formals found

    // For getRawToken/ `line insertion
    string	m_lineCmt;	///< Line comment(s) to be returned
    bool	m_lineCmtNl;	///< Newline needed before inserting lineCmt
    int		m_lineAdd;	///< Empty lines to return to maintain line count
    bool	m_rawAtBol;	///< Last rawToken left us at beginning of line

    // For getFinalToken
    bool	m_finAhead;	///< Have read a token ahead
    int		m_finToken;	///< Last token read
    string	m_finBuf;	///< Last yytext read
    bool	m_finAtBol;	///< Last getFinalToken left us at beginning of line
    VFileLine*	m_finFilelinep;	///< Location of last returned token (internal only)

    // For stringification
    string	m_strify;	///< Text to be stringified

    // For defines
    stack<VPreDefRef> m_defRefs; // Pending definine substitution
    stack<VPreIfEntry> m_ifdefStack;	///< Stack of true/false emitting evaluations
    unsigned	m_defDepth;	///< How many `defines deep
    bool	m_defPutJoin;	///< Insert `` after substitution

    // For `` join
    stack<string> m_joinStack;	///< Text on lhs of join

    // For getline()
    string	m_lineChars;	///< Characters left for next line

    VPreProcImp() {
	m_debug = 0;
	m_states.push(ps_TOP);
	m_off = 0;
	m_lineChars = "";
	m_lastSym = "";
	m_lineAdd = 0;
	m_lineCmtNl = false;
	m_rawAtBol = true;
	m_finAhead = false;
	m_finAtBol = true;
	m_defDepth = 0;
	m_defPutJoin = false;
	m_finToken = 0;
	m_finFilelinep = NULL;
	m_lexp = NULL;
	m_preprocp = NULL;
    }
    void configure(VFileLine* filelinep, VPreProc* preprocp) {
	// configure() separate from constructor to avoid calling abstract functions
	m_preprocp = preprocp;
	m_finFilelinep = filelinep->create(1);
	// Create lexer
	m_lexp = new VPreLex (this, filelinep);
	m_lexp->m_keepComments = m_preprocp->keepComments();
	m_lexp->m_keepWhitespace = m_preprocp->keepWhitespace();
	m_lexp->m_pedantic = m_preprocp->pedantic();
	m_lexp->m_synthesis = m_preprocp->synthesis();
	m_lexp->debug(debug()>=10 ? debug() : 0);  // See also VPreProc::debug() method
    }
    ~VPreProcImp() {
	if (m_lexp) { delete m_lexp; m_lexp = NULL; }
    }
    const char* tokenName(int tok);
    void debugToken(int tok, const char* cmtp);
    void parseTop();
    void parseUndef();
    string getparseline(bool stop_at_eol, size_t approx_chunk);
    bool isEof() const { return m_lexp->curStreamp()->m_eof; }
    bool readWholefile(const string& filename, StrList& outl);
    void openFile(string filename, VFileLine* filelinep);
    void insertUnreadback(const string& text) { m_lineCmt += text; }
    void insertUnreadbackAtBol(const string& text);
    void addLineComment(int enter_exit_level);
private:
    void error(string msg) { m_lexp->m_tokFilelinep->error(msg); }
    void fatal(string msg) { m_lexp->m_tokFilelinep->fatal(msg); }
    int debug() const { return m_debug; }
    void endOfOneFile();
    string defineSubst(VPreDefRef* refp);
    string trimWhitespace(const string& strg, bool trailing);
    void unputString(const string& strg);
    void unputDefrefString(const string& strg);

    void parsingOn() {
	m_off--;
	if (m_off<0) fatalSrc("Underflow of parsing cmds");
	// addLineComment no longer needed; getFinalToken will correct.
    }
    void parsingOff() { m_off++; }

    int getRawToken();
    int getStateToken(string& buf);
    int getFinalToken(string& buf);

    void statePush(ProcState state) {
	m_states.push(state);
    }
    void statePop() {
	m_states.pop();
	if (m_states.empty()) {
	    error("InternalError: Pop of parser state with nothing on stack");
	    m_states.push(ps_TOP);
	}
    }
    void stateChange(ProcState state) {
	statePop(); statePush(state);
    }

};

//*************************************************************************
// Creation

VPreProc::VPreProc() {
    VPreProcImp* idatap = new VPreProcImp();
    m_opaquep = idatap;
    // Below overridden by configure()
    m_keepComments = true;
    m_keepWhitespace = true;
    m_lineDirectives = true;
    m_pedantic = false;
    m_synthesis = false;
}

void VPreProc::configure(VFileLine* filelinep) {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    idatap->configure(filelinep, this);
}

VPreProc::~VPreProc() {
    if (m_opaquep) { delete m_opaquep; m_opaquep = NULL; }
}

//*************************************************************************
// VPreProc Methods.  Just call the implementation functions.

void VPreProc::comment(string cmt) { }
void VPreProc::openFile(string filename, VFileLine* filelinep) {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    idatap->openFile (filename,filelinep);
}
string VPreProc::getline() {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    return idatap->getparseline(true,0);
}
string VPreProc::getall(size_t approx_chunk) {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    return idatap->getparseline(false,approx_chunk);
}
void VPreProc::debug(int level) {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    idatap->m_debug = level;
    // To see "accepting rule" debug, Makefile.PL must be changed to enable flex debug
    // export VERILOGPERL_FLEX_DEBUG=1
    idatap->m_lexp->debug(level>=10 ? level : 0);
}
bool VPreProc::isEof() {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    return idatap->isEof();
}
VFileLine* VPreProc::fileline() {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    return idatap->m_lexp->m_tokFilelinep;
}
void VPreProc::insertUnreadback(string text) {
    VPreProcImp* idatap = static_cast<VPreProcImp*>(m_opaquep);
    return idatap->insertUnreadback(text);
}

//**********************************************************************
// Parser Utilities

const char* VPreProcImp::tokenName(int tok) {
    switch (tok) {
    case VP_BACKQUOTE	: return("BACKQUOTE");
    case VP_COMMENT	: return("COMMENT");
    case VP_DEFARG	: return("DEFARG");
    case VP_DEFFORM	: return("DEFFORM");
    case VP_DEFINE	: return("DEFINE");
    case VP_DEFREF	: return("DEFREF");
    case VP_DEFREF_JOIN	: return("DEFREF_JOIN");
    case VP_DEFVALUE	: return("DEFVALUE");
    case VP_ELSE	: return("ELSE");
    case VP_ELSIF	: return("ELSIF");
    case VP_ENDIF	: return("ENDIF");
    case VP_EOF		: return("EOF");
    case VP_ERROR	: return("ERROR");
    case VP_IFDEF	: return("IFDEF");
    case VP_IFNDEF	: return("IFNDEF");
    case VP_INCLUDE	: return("INCLUDE");
    case VP_LINE	: return("LINE");
    case VP_PSL		: return("PSL");
    case VP_STRIFY	: return("STRIFY");
    case VP_STRING	: return("STRING");
    case VP_SYMBOL	: return("SYMBOL");
    case VP_SYMBOL_JOIN	: return("SYMBOL_JOIN");
    case VP_TEXT	: return("TEXT");
    case VP_UNDEF	: return("UNDEF");
    case VP_UNDEFINEALL	: return("UNDEFINEALL");
    case VP_WHITE	: return("WHITE");
    default: return("?");
    }
}

void VPreProcImp::unputString(const string& strg) {
    // Note: The preliminary call in ::openFile bypasses this function
    // We used to just m_lexp->unputString(strg.c_str());
    // However this can lead to "flex scanner push-back overflow"
    // so instead we scan from a temporary buffer, then on EOF return.
    // This is also faster than the old scheme, amazingly.
    if (m_lexp->m_bufferState!=m_lexp->currentBuffer()) {
	fatalSrc("bufferStack missing current buffer; will return incorrectly");
	// Hard to debug lost text as won't know till much later
    }
    m_lexp->scanBytes(strg);
}

void VPreProcImp::unputDefrefString(const string& strg) {
    int multiline = 0;
    for (size_t i=0; i<strg.length(); i++) {
	if (strg[i] == '\n') multiline++;
    }
    unputString(strg);
    // A define that inserts multiple newlines are really attributed to one source line,
    // so temporarily don't increment lineno.
    m_lexp->curStreamp()->m_ignNewlines += multiline;  // Must be after unput - applies to new stream
}

string VPreProcImp::trimWhitespace(const string& strg, bool trailing) {
    // Remove leading whitespace
    string out = strg;
    string::size_type leadspace = 0;
    while (out.length() > leadspace
	   && isspace(out[leadspace])) leadspace++;
    if (leadspace) out.erase(0,leadspace);
    // Remove trailing whitespace
    if (trailing) {
	string::size_type trailspace = 0;
	while (out.length() > trailspace
	       && isspace(out[out.length()-1-trailspace])) trailspace++;
	// Don't remove \{space_or_newline}
	if (trailspace && out.length() > trailspace && out[out.length()-1-trailspace]=='\\')
	    trailspace--;
	if (trailspace) out.erase(out.length()-trailspace,trailspace);
    }
    return out;
}

string VPreProcImp::defineSubst(VPreDefRef* refp) {
    // Substitute out defines in a define reference.
    // (We also need to call here on non-param defines to handle `")
    // We could push the define text back into the lexer, but that's slow
    // and would make recursive definitions and parameter handling nasty.
    //
    // Note we parse the definition parameters and value here.  If a
    // parametrized define is used many, many times, we could cache the
    // parsed result.
    if (debug()>=5) {
	cout<<"defineSubstIn  `"<<refp->name()<<" "<<refp->params()<<endl;
	for (unsigned i=0; i<refp->args().size(); i++) {
	    cout<<"defineArg["<<i<<"] = '"<<refp->args()[i]<<"'"<<endl;
	}
    }
    // Grab value
    string value = m_preprocp->defValue(refp->name());
    if (debug()>=5) cout<<"defineValue    '"<<VPreLex::cleanDbgStrg(value)<<"'"<<endl;

    map<string,string> argValueByName;
    {   // Parse argument list into map
	unsigned numArgs=0;
	string argName;
	int paren = 1;  // (), {} and [] can use same counter, as must be matched pair per spec
	string token;
	bool quote = false;
	bool haveDefault = false;
	// Note there's a leading ( and trailing ), so parens==1 is the base parsing level
	string params = refp->params();  // Must keep str in scope to get pointer
	const char* cp=params.c_str();
	if (*cp == '(') cp++;
	for (; *cp; cp++) {
	    //if (debug()>=5) cout <<"   Parse  Paren="<<paren<<"  Arg="<<numArgs<<"  token='"<<token<<"'  Parse="<<cp<<endl;
	    if (!quote && paren==1) {
		if (*cp==')' || *cp==',') {
		    string value;
		    if (haveDefault) { value=token; } else { argName=token; }
		    argName = trimWhitespace(argName,true);
		    if (debug()>=5) cout<<"    Got Arg="<<numArgs<<"  argName='"<<argName<<"'  default='"<<value<<"'"<<endl;
		    // Parse it
		    if (argName!="") {
			if (refp->args().size() > numArgs) {
			    // A call `def( a ) must be equivelent to `def(a ), so trimWhitespace
			    // At one point we didn't trim trailing whitespace, but this confuses `"
			    string arg = trimWhitespace(refp->args()[numArgs], true);
			    if (arg != "") value = arg;
			} else if (!haveDefault) {
			    error("Define missing argument '"+argName+"' for: "+refp->name()+"\n");
			    return " `"+refp->name()+" ";
			}
			numArgs++;
		    }
		    argValueByName[argName] = value;
		    // Prepare for next
		    argName = "";
		    token = "";
		    haveDefault = false;
		    continue;
		}
		else if (*cp=='=') {
		    haveDefault = true;
		    argName = token;
		    token = "";
		    continue;
		}
	    }
	    if (cp[0]=='\\' && cp[1]) {
		token += cp[0]; // \{any} Put out literal next character
		token += cp[1];
		cp++;
		continue;
	    }
	    if (!quote) {
		if (*cp=='(' || *cp=='{' || *cp=='[') paren++;
		else if (*cp==')' || *cp=='}' || *cp==']') paren--;
	    }
	    if (*cp=='"') quote=!quote;
	    if (*cp) token += *cp;
	}
	if (refp->args().size() > numArgs
	    // `define X() is ok to call with nothing
	    && !(refp->args().size()==1 && numArgs==0 && trimWhitespace(refp->args()[0],false)=="")) {
	    error("Define passed too many arguments: "+refp->name()+"\n");
	    return " `"+refp->name()+" ";
	}
    }

    string out = "";
    {   // Parse substitution define using arguments
	string argName;
	string prev;
	bool quote = false;
	bool backslashesc = false;  // In \.....{space} block
	// Note we go through the loop once more at the NULL end-of-string
	for (const char* cp=value.c_str(); (*cp) || argName!=""; cp=(*cp?cp+1:cp)) {
	    //cout << "CH "<<*cp<<"  an "<<argName<<"\n";
	    if (!quote && *cp == '\\') { backslashesc = true; }
	    else if (isspace(*cp)) { backslashesc = false; }
	    // We don't check for quotes; some simulators expand even inside quotes
	    if ( isalpha(*cp) || *cp=='_'
		 || *cp=='$' // Won't replace system functions, since no $ in argValueByName
		 || (argName!="" && (isdigit(*cp) || *cp=='$'))) {
		argName += *cp;
		continue;
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
		    if (backslashesc) {
			// Don't put out the ``, we're forming an escape which will not expand further later
		    } else {
			out += "``";   // `` must get removed later, as `FOO```BAR must pre-expand FOO and BAR
		    }
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='"') {
		    out += "`\"";  // `" means to put out a " without enabling quote mode (sort of)
		    // however we must expand any macro calls inside it first.
		    // So keep it `", so we don't enter quote mode.
		    cp++;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='\\' && cp[2]=='`' && cp[3]=='"') {
		    out += "`\\`\"";   // `\`" means to put out a backslash quote
		    // Leave it literal until we parse the VP_STRIFY string
		    cp+=3;
		    continue;
		}
		else if (cp[0]=='`' && cp[1]=='\\') {
		    out += '\\';   // `\ means to put out a backslash
		    cp++;
		    continue;
		}
		else if (cp[0]=='\\' && cp[1]=='\n') {
		    // We kept the \\n when we lexed because we don't want whitespace
		    // trimming to mis-drop the final \\n
		    // At replacement time we need the standard newline.
		    out += "\n";	 // \\n newline
		    cp++;
		    continue;
		}
	    }
	    if (cp[0]=='\\' && cp[1]=='\"') {
		out += cp[0]; // \{any} Put out literal next character
		out += cp[1];
		cp++;
		continue;
	    }
	    else if (cp[0]=='\\') {
		// Normally \{any} would put out literal next character
		// Instead we allow "`define A(nm) \nm" to expand, per proposed mantis1537
		out += cp[0];
		continue;
	    }
	    if (*cp=='"') quote=!quote;
	    if (*cp) out += *cp;
	}
    }

    if (debug()>=5) cout<<"defineSubstOut '"<<VPreLex::cleanDbgStrg(out)<<"'"<<endl;
    return out;
}

//**********************************************************************
// Parser routines

bool VPreProcImp::readWholefile(const string& filename, StrList& outl) {
// If change this code, run a test with the below size set very small
//#define INFILTER_IPC_BUFSIZ 16
#define INFILTER_IPC_BUFSIZ 64*1024
    char buf[INFILTER_IPC_BUFSIZ];

    FILE* fp = NULL;
    int fd;
    bool eof = false;

    ssize_t position = filename.find_last_of(".");
    if (filename.length()>3 && 0==filename.compare(filename.length()-3, 3, ".gz")) {
	string cmd = "gunzip -c "+filename;
        if ((fp = popen(cmd.c_str(), "r")) == NULL) {
            return false;
        }
        fd = fileno (fp);
    } else {
        fd = open (filename.c_str(), O_RDONLY);
        if (fd<0) return false;
    }
    while (!eof) {
	ssize_t todo = INFILTER_IPC_BUFSIZ;
	errno = 0;
	ssize_t got = read (fd, buf, todo);
	if (got>0) {
	    outl.push_back(string(buf, got));
	}
	else if (errno == EINTR || errno == EAGAIN
#ifdef EWOULDBLOCK
		 || errno == EWOULDBLOCK
#endif
	    ) {
	} else { eof = true; break; }
    }

    if (fp) { pclose(fp); fp=NULL; }
    else close(fd);
    return true;
}

void VPreProcImp::openFile(string filename, VFileLine* filelinep) {
    // Open a new file, possibly overriding the current one which is active.

    // Read a list<string> with the whole file.
    StrList wholefile;
    bool ok = readWholefile(filename, wholefile/*ref*/);
    if (!ok) {
	error("File not found: "+filename+"\n");
	return;
    }

    if (!m_preprocp->isEof()) {  // IE not the first file.
	// We allow the same include file twice, because occasionally it pops
	// up, with guards preventing a real recursion.
	if (m_lexp->m_streampStack.size()>VPreProc::INCLUDE_DEPTH_MAX) {
	    error("Recursive inclusion of file: "+filename);
	    return;
	}
	// There's already a file active.  Push it to work on the new one.
	addLineComment(0);
    }

    // Create new stream structure
    m_lexp->scanNewFile(m_preprocp->fileline()->create(filename, 1));
    addLineComment(1); // Enter

    // Filter all DOS CR's en-mass.  This avoids bugs with lexing CRs in the wrong places.
    // This will also strip them from strings, but strings aren't supposed to be multi-line without a "\"
    for (StrList::iterator it=wholefile.begin(); it!=wholefile.end(); ++it) {
	// We don't end-loop at \0 as we allow and strip mid-string '\0's (for now).
	bool strip = false;
	const char* sp = it->data();
	const char* ep = sp + it->length();
	// Only process if needed, as saves extra string allocations
	for (const char* cp=sp; cp<ep; cp++) {
	    if (*cp == '\r' || *cp == '\0') {
		strip = true; break;
	    }
	}
	if (strip) {
	    string out;  out.reserve(it->length());
	    for (const char* cp=sp; cp<ep; cp++) {
		if (!(*cp == '\r' || *cp == '\0')) {
		    out += *cp;
		}
	    }
	    *it = out;
	}

	// Push the data to an internal buffer.
	m_lexp->scanBytesBack(*it);
	// Reclaim memory; the push saved the string contents for us
	*it = "";
    }
}

void VPreProcImp::insertUnreadbackAtBol(const string& text) {
    // Insert insuring we're at the beginning of line, for `line
    // We don't always add a leading newline, as it may result in extra unreadback(newlines).
    if (m_lineCmt == "") { m_lineCmtNl = true; }
    else if (m_lineCmt[m_lineCmt.length()-1]!='\n') {
	insertUnreadback("\n");
    }
    insertUnreadback(text);
}

void VPreProcImp::addLineComment(int enter_exit_level) {
    if (m_preprocp->lineDirectives()) {
	insertUnreadbackAtBol(m_lexp->curFilelinep()->lineDirectiveStrg(enter_exit_level));
    }
}

int VPreProcImp::getRawToken() {
    // Get a token from the file, whatever it may be.
    while (1) {
      next_tok:
	if (m_lineAdd) {
	    m_lineAdd--;
	    m_rawAtBol = true;
	    yyourtext("\n",1);
	    if (debug()>=5) debugToken(VP_WHITE, "LNA");
	    return (VP_WHITE);
	}
	if (m_lineCmt!="") {
	    // We have some `line directive or other processed data to return to the user.
	    static string rtncmt;  // Keep the c string till next call
	    rtncmt = m_lineCmt;
	    if (m_lineCmtNl) {
		if (!m_rawAtBol) rtncmt = "\n"+rtncmt;
		m_lineCmtNl = false;
	    }
	    yyourtext(rtncmt.c_str(), rtncmt.length());
	    m_lineCmt = "";
	    if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
	    if (m_states.top()==ps_DEFVALUE) {
		VPreLex::s_currentLexp->appendDefValue(yyourtext(),yyourleng());
		goto next_tok;
	    } else {
		if (debug()>=5) debugToken(VP_TEXT, "LCM");
		return (VP_TEXT);
	    }
	}
	if (isEof()) return (VP_EOF);

	// Snarf next token from the file
	int tok = m_lexp->lex();

	if (debug()>=5) debugToken(tok, "RAW");

	// A EOF on an include, so we can print `line and detect mis-matched "s
	if (tok==VP_EOF) {
	    goto next_tok;  // find the EOF, after adding needed lines
	}

	if (yyourleng()) m_rawAtBol = (yyourtext()[yyourleng()-1]=='\n');
	return tok;
    }
}

void VPreProcImp::debugToken(int tok, const char* cmtp) {
    if (debug()>=5) {
	string buf = string (yyourtext(), yyourleng());
	string::size_type pos;
	while ((pos=buf.find("\n")) != string::npos) { buf.replace(pos, 1, "\\n"); }
	while ((pos=buf.find("\r")) != string::npos) { buf.replace(pos, 1, "\\r"); }
	fprintf (stderr, "%d: %s %s %s(%d) dr%d:  <%d>%-10s: %s\n",
		 m_lexp->m_tokFilelinep->lineno(), cmtp, m_off?"of":"on",
		 procStateName(m_states.top()), (int)m_states.size(), (int)m_defRefs.size(),
		 m_lexp->currentStartState(), tokenName(tok), buf.c_str());
    }
}

// Sorry, we're not using bison/yacc. It doesn't handle returning white space
// in the middle of parsing other tokens.

int VPreProcImp::getStateToken(string& buf) {
    // Return the next state-determined token
    while (1) {
      next_tok:
	if (isEof()) {
	    buf = string (yyourtext(), yyourleng());
	    return VP_EOF;
	}
	int tok = getRawToken();
	ProcState state = m_states.top();

	// Most states emit white space and comments between tokens. (Unless collecting a string)
	if (tok==VP_WHITE && state !=ps_STRIFY) {
	    buf = string (yyourtext(), yyourleng());
	    return (tok);
	}
	if (tok==VP_BACKQUOTE && state !=ps_STRIFY) { tok = VP_TEXT; }
	if (tok==VP_COMMENT) {
	    if (!m_off) {
		if (m_lexp->m_keepComments == KEEPCMT_SUB
		    || m_lexp->m_keepComments == KEEPCMT_EXP) {
		    string rtn; rtn.assign(yyourtext(),yyourleng());
		    m_preprocp->comment(rtn);
		    // Need to insure "foo/**/bar" becomes two tokens
		    insertUnreadback (" ");
		} else if (m_lexp->m_keepComments) {
		    buf = string (yyourtext(), yyourleng());
		    return (tok);
		} else {
		    // Need to insure "foo/**/bar" becomes two tokens
		    insertUnreadback (" ");
		}
	    }
	    // We're off or processed the comment specially.  If there are newlines
	    // in it, we also return the newlines as TEXT so that the linenumber
	    // count is maintained for downstream tools
	    for (size_t len=0; len<(size_t)yyourleng(); len++) { if (yyourtext()[len]=='\n') m_lineAdd++; }
	    goto next_tok;
	}
	if (tok==VP_LINE) {
	    addLineComment(m_lexp->m_enterExit);
	    goto next_tok;
	}

	if (tok==VP_DEFREF_JOIN) {
	    // Here's something fun and unspecified as yet:
	    // The existance of non-existance of a base define changes `` expansion
	    //	`define QA_b zzz
	    //	`define Q1 `QA``_b
	    //	 1Q1 -> zzz
	    //	`define QA a
	    //	 `Q1 -> a_b
	    // Note parenthesis make this unambiguous
	    //	`define Q1 `QA()``_b  // -> a_b
	    // This may be a side effect of how `UNDEFINED remains as `UNDEFINED,
	    // but it screws up our method here.  So hardcode it.
	    string name (yyourtext()+1,yyourleng()-1);
	    if (m_preprocp->defExists(name)) {   // JOIN(DEFREF)
		// Put back the `` and process the defref
		if (debug()>=5) cout<<"```: define "<<name<<" exists, expand first\n";
		m_defPutJoin = true;  // After define, unputString("``").  Not now as would loose yyourtext()
		if (debug()>=5) cout<<"TOKEN now DEFREF\n";
		tok = VP_DEFREF;
	    } else {  // DEFREF(JOIN)
		if (debug()>=5) cout<<"```: define "<<name<<" doesn't exist, join first\n";
		// FALLTHRU, handle as with VP_SYMBOL_JOIN
	    }
	}
	if (tok==VP_SYMBOL_JOIN || tok==VP_DEFREF_JOIN) {  // not else if, can fallthru from above if()
	    // a`` -> string doesn't include the ``, so can just grab next and continue
	    string out (yyourtext(),yyourleng());
	    if (debug()>=5) cout<<"`` LHS:"<<out<<endl;
	    // a``b``c can have multiple joins, so we need a stack
	    m_joinStack.push(out);
	    statePush(ps_JOIN);
	    goto next_tok;
	}

	// Deal with some special parser states
	switch (state) {
	case ps_TOP: {
	    break;
	}
	case ps_DEFNAME_UNDEF:	// FALLTHRU
	case ps_DEFNAME_DEFINE:	// FALLTHRU
	case ps_DEFNAME_IFDEF:	// FALLTHRU
	case ps_DEFNAME_IFNDEF:	// FALLTHRU
	case ps_DEFNAME_ELSIF: {
	    if (tok==VP_SYMBOL) {
		m_lastSym.assign(yyourtext(),yyourleng());
		if (state==ps_DEFNAME_IFDEF
		    || state==ps_DEFNAME_IFNDEF) {
		    bool enable = m_preprocp->defExists(m_lastSym);
		    if (debug()>=5) cout<<"Ifdef "<<m_lastSym<<(enable?" ON":" OFF")<<endl;
		    if (state==ps_DEFNAME_IFNDEF) enable = !enable;
		    m_ifdefStack.push(VPreIfEntry(enable,false));
		    if (!enable) parsingOff();
		    statePop();
		    goto next_tok;
		}
		else if (state==ps_DEFNAME_ELSIF) {
		    if (m_ifdefStack.empty()) {
			error("`elsif with no matching `if\n");
		    } else {
			// Handle `else portion
			VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
			if (!lastIf.on()) parsingOn();
			// Handle `if portion
			bool enable = !lastIf.everOn() && m_preprocp->defExists(m_lastSym);
			if (debug()>=5) cout<<"Elsif "<<m_lastSym<<(enable?" ON":" OFF")<<endl;
			m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
			if (!enable) parsingOff();
		    }
		    statePop();
		    goto next_tok;
		}
		else if (state==ps_DEFNAME_UNDEF) {
		    if (!m_off) {
			if (debug()>=5) cout<<"Undef "<<m_lastSym<<endl;
			m_preprocp->undef(m_lastSym);
		    }
		    statePop();
		    goto next_tok;
		}
		else if (state==ps_DEFNAME_DEFINE) {
		    // m_lastSym already set.
		    stateChange(ps_DEFFORM);
		    m_lexp->pushStateDefForm();
		    goto next_tok;
		}
		else fatalSrc("Bad case\n");
		goto next_tok;
	    }
	    else if (tok==VP_TEXT) {
		// IE, something like comment between define and symbol
		if (!m_off) {
		    buf = string (yyourtext(), yyourleng());
		    return tok;
		}
		else goto next_tok;
	    }
	    else if (tok==VP_DEFREF) {
		// IE, `ifdef `MACRO(x): Substitue and come back here when state pops.
		break;
	    }
	    else {
		error((string)"Expecting define name. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	case ps_DEFFORM: {
	    if (tok==VP_DEFFORM) {
		m_formals = m_lexp->m_defValue;
		if (debug()>=5) cout<<"DefFormals='"<<VPreLex::cleanDbgStrg(m_formals)<<"'\n";
		stateChange(ps_DEFVALUE);
		m_lexp->pushStateDefValue();
		goto next_tok;
	    } else if (tok==VP_TEXT) {
		// IE, something like comment in formals
		if (!m_off) {
		    buf = string (yyourtext(), yyourleng());
		    return tok;
		}
		else goto next_tok;
	    } else {
		error((string)"Expecting define formal arguments. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	case ps_DEFVALUE: {
	    static string newlines;
	    newlines = "\n";  // Always start with trailing return
	    if (tok == VP_DEFVALUE) {
		if (debug()>=5) cout<<"DefValue='"<<VPreLex::cleanDbgStrg(m_lexp->m_defValue)
				    <<"'  formals='"<<VPreLex::cleanDbgStrg(m_formals)<<"'\n";
		// Add any formals
		string formals = m_formals;
		string value = m_lexp->m_defValue;
		// Remove returns
		// Not removing returns in values has two problems,
		// 1. we need to correct line numbers with `line after each substitution
		// 2. Substituting in " .... " with embedded returns requires \ escape.
		//    This is very difficult in the presence of `", so we keep the \ before the newline.
		for (size_t i=0; i<formals.length(); i++) {
		    if (formals[i] == '\n') {
			newlines += "\n";
		    }
		}
		for (size_t i=0; i<value.length(); i++) {
		    if (value[i] == '\n') {
			newlines += "\n";
		    }
		}
		if (!m_off) {
		    // Remove leading and trailing whitespace
		    value = trimWhitespace(value, true);
		    // Define it
		    if (debug()>=5) cout<<"Define "<<m_lastSym<<" "<<formals
					<<" = '"<<VPreLex::cleanDbgStrg(value)<<"'"<<endl;
		    m_preprocp->define(m_lastSym, value, formals);
		}
	    } else {
		string msg = string("Bad define text, unexpected ")+tokenName(tok)+"\n";
		fatalSrc(msg);
	    }
	    statePop();
	    // DEFVALUE is terminated by a return, but lex can't return both tokens.
	    // Thus, we emit a return here.
	    buf = newlines;
	    return(VP_WHITE);
	}
	case ps_DEFPAREN: {
	    if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='(') {
		stateChange(ps_DEFARG);
		goto next_tok;
	    } else {
		if (m_defRefs.empty()) fatalSrc("Shouldn't be in DEFPAREN w/o active defref");
		VPreDefRef* refp = &(m_defRefs.top());
		error((string)"Expecting ( to begin argument list for define reference `"+refp->name()+"\n");
		statePop();
		goto next_tok;
	    }
	}
	case ps_DEFARG: {
	    if (m_defRefs.empty()) fatalSrc("Shouldn't be in DEFARG w/o active defref");
	    VPreDefRef* refp = &(m_defRefs.top());
	    refp->nextarg(refp->nextarg()+m_lexp->m_defValue); m_lexp->m_defValue="";
	    if (debug()>=5) cout<<"defarg++ "<<refp->nextarg()<<endl;
	    if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==',') {
		refp->args().push_back(refp->nextarg());
		stateChange(ps_DEFARG);
		m_lexp->pushStateDefArg(1);
		refp->nextarg("");
		goto next_tok;
	    } else if (tok==VP_DEFARG && yyourleng()==1 && yyourtext()[0]==')') {
		// Substitute in and prepare for next action
		// Similar code in non-parenthesized define (Search for END_OF_DEFARG)
		refp->args().push_back(refp->nextarg());
		string out;
		if (!m_off) {
		    out = defineSubst(refp);
		    out = m_preprocp->defSubstitute(out);
		}
		m_defRefs.pop();  refp=NULL;
		if (m_defRefs.empty()) {
		    statePop();
		    if (!m_off) unputDefrefString(out);
		    m_lexp->m_parenLevel = 0;
		}
		else {  // Finished a defref inside a upper defref
		    // Can't subst now, or
		    // `define a(ign) x,y
		    // foo(`a(ign),`b)  would break because a contains comma
		    refp = &(m_defRefs.top());  // We popped, so new top
		    refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue="";
		    m_lexp->m_parenLevel = refp->parenLevel();
		    statePop();  // Will go to ps_DEFARG, as we're under another define
		}
		goto next_tok;
	    } else if (tok==VP_DEFREF) {
		// Expand it, then state will come back here
		// Value of building argument is data before the lower defref
		// we'll append it when we push the argument.
		break;
	    } else if (tok==VP_SYMBOL || tok==VP_STRING || VP_TEXT || VP_WHITE || VP_PSL) {
		string rtn; rtn.assign(yyourtext(),yyourleng());
		refp->nextarg(refp->nextarg()+rtn);
		goto next_tok;
	    } else {
		error((string)"Expecting ) or , to end argument list for define reference. Found: "+tokenName(tok));
		statePop();
		goto next_tok;
	    }
	}
	case ps_INCNAME: {
	    if (tok==VP_STRING) {
		statePop();
		m_lastSym.assign(yyourtext(),yyourleng());
		if (debug()>=5) cout<<"Include "<<m_lastSym<<endl;
		// Drop leading and trailing quotes.
		m_lastSym.erase(0,1);
		m_lastSym.erase(m_lastSym.length()-1,1);
		m_preprocp->include(m_lastSym);
		goto next_tok;
	    }
	    else if (tok==VP_TEXT && yyourleng()==1 && yyourtext()[0]=='<') {
		// include <filename>
		stateChange(ps_INCNAME);  // Still
		m_lexp->pushStateIncFilename();
		goto next_tok;
	    }
	    else if (tok==VP_DEFREF
		     || tok==VP_STRIFY) {
		// Expand it, then state will come back here
		break;
	    }
	    else {
		statePop();
		error((string)"Expecting include filename. Found: "+tokenName(tok)+"\n");
		goto next_tok;
	    }
	}
	case ps_ERRORNAME: {
	    if (tok==VP_STRING) {
		if (!m_off) {
		    m_lastSym.assign(yyourtext(),yyourleng());
		    error(m_lastSym);
		}
		statePop();
		goto next_tok;
	    }
	    else {
		error((string)"Expecting `error string. Found: "+tokenName(tok)+"\n");
		statePop();
		goto next_tok;
	    }
	}
	case ps_JOIN: {
	    if (tok==VP_SYMBOL || tok==VP_TEXT) {
		if (m_joinStack.empty()) fatalSrc("`` join stack empty, but in a ``");
		string lhs = m_joinStack.top(); m_joinStack.pop();
		if (debug()>=5) cout<<"`` LHS:"<<lhs<<endl;
		string rhs (yyourtext(),yyourleng());
		if (debug()>=5) cout<<"`` RHS:"<<rhs<<endl;
		string out = lhs+rhs;
		if (debug()>=5) cout<<"`` Out:"<<out<<endl;
		unputString(out);
		statePop();
		goto next_tok;
	    } else if (tok==VP_EOF || tok==VP_WHITE || tok == VP_COMMENT || tok==VP_STRING) {
		error((string)"Expecting symbol to terminate ``; whitespace etc cannot follow ``. Found: "+tokenName(tok)+"\n");
		statePop();
		goto next_tok;
	    } else {
		// `define, etc, fall through and expand.  Pop back here.
		break;
	    }
	}
	case ps_STRIFY: {
	    if (tok==VP_STRIFY) {
		// Quote what's in the middle of the stringification
		// Note a `" MACRO_WITH(`") `" doesn't need to be handled (we don't need a stack)
		// That behavior isn't specified, and other simulators vary widely
		string out = m_strify;
		m_strify = "";
		// Convert any newlines to spaces, so we don't get a multiline "..." without \ escapes
		// The spec is silent about this either way; simulators vary
		string::size_type pos;
		while ((pos=out.find("\n")) != string::npos) {
		    out.replace(pos, 1, " ");
		}
		unputString((string)"\""+out+"\"");
		statePop();
		goto next_tok;
	    }
	    else if (tok==VP_EOF) {
		error("`\" not terminated at EOF\n");
	    }
	    else if (tok==VP_BACKQUOTE) {
		m_strify += "\\\"";
		goto next_tok;
	    }
	    else if (tok==VP_DEFREF) {
		// Spec says to expand macros inside `"
		// Substitue it into the stream, then return here
		break;
	    }
	    else {
		// Append token to eventual string
		m_strify.append(yyourtext(),yyourleng());
		goto next_tok;
	    }
	}
	default: fatalSrc("Bad case\n");
	}
	// Default is to do top level expansion of some tokens
	switch (tok) {
	case VP_INCLUDE:
	    if (!m_off) {
		statePush(ps_INCNAME);
	    }
	    goto next_tok;
	case VP_UNDEF:
	    statePush(ps_DEFNAME_UNDEF);
	    goto next_tok;
	case VP_DEFINE:
	    // No m_off check here, as a `ifdef NEVER `define FOO(`endif)  should work
	    statePush(ps_DEFNAME_DEFINE);
	    goto next_tok;
	case VP_IFDEF:
	    statePush(ps_DEFNAME_IFDEF);
	    goto next_tok;
	case VP_IFNDEF:
	    statePush(ps_DEFNAME_IFNDEF);
	    goto next_tok;
	case VP_ELSIF:
	    statePush(ps_DEFNAME_ELSIF);
	    goto next_tok;
	case VP_ELSE:
	    if (m_ifdefStack.empty()) {
		error("`else with no matching `if\n");
	    } else {
		VPreIfEntry lastIf = m_ifdefStack.top(); m_ifdefStack.pop();
		bool enable = !lastIf.everOn();
		if (debug()>=5) cout<<"Else "<<(enable?" ON":" OFF")<<endl;
		m_ifdefStack.push(VPreIfEntry(enable, lastIf.everOn()));
		if (!lastIf.on()) parsingOn();
		if (!enable) parsingOff();
	    }
	    goto next_tok;
	case VP_ENDIF:
	    if (debug()>=5) cout<<"Endif "<<endl;
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
	    // m_off not right here, but inside substitution, to make this work: `ifdef NEVER `DEFUN(`endif)
	    string name (yyourtext()+1,yyourleng()-1);
	    if (debug()>=5) cout<<"DefRef "<<name<<endl;
	    if (m_defPutJoin) { m_defPutJoin = false; unputString("``"); }
	    if (m_defDepth++ > VPreProc::DEFINE_RECURSION_LEVEL_MAX) {
		error("Recursive `define substitution: `"+name);
		goto next_tok;
	    }
	    // Substitute
	    string params = m_preprocp->defParams(name);
	    if (params=="") {   // Not found, return original string as-is
		m_defDepth = 0;
		if (debug()>=5) cout<<"Defref `"<<name<<" => not_defined"<<endl;
		if (m_off) {
		    goto next_tok;
		} else {
		    buf = string (yyourtext(), yyourleng());
		    return (VP_TEXT);
		}
	    }
	    else if (params=="0") {  // Found, as simple substitution
		if (m_off) {
		    goto next_tok;
		}
		else {
		    VPreDefRef tempref(name, "");
		    string out = defineSubst(&tempref);
		    // Similar code in parenthesized define (Search for END_OF_DEFARG)
		    out = m_preprocp->defSubstitute(out);
		    if (m_defRefs.empty()) {
			// Just output the substitution
			unputDefrefString(out);
		    } else {  // Inside another define.
			// Can't subst now, or
			// `define a x,y
			// foo(`a,`b)  would break because a contains comma
			VPreDefRef* refp = &(m_defRefs.top());
			refp->nextarg(refp->nextarg()+m_lexp->m_defValue+out); m_lexp->m_defValue="";
		    }
		    goto next_tok;
		}
	    }
	    else {  // Found, with parameters
		if (debug()>=5) cout<<"Defref `"<<name<<" => parametrized"<<endl;
		// The CURRENT macro needs the paren saved, it's not a property of the child macro
		if (!m_defRefs.empty()) m_defRefs.top().parenLevel(m_lexp->m_parenLevel);
		m_defRefs.push(VPreDefRef(name, params));
		statePush(ps_DEFPAREN);
		m_lexp->pushStateDefArg(0);
		goto next_tok;
	    }
	    fatalSrc("Bad case\n");
	}
	case VP_ERROR: {
	    statePush(ps_ERRORNAME);
	    goto next_tok;
	}
	case VP_EOF:
	    if (!m_ifdefStack.empty()) {
		error("`ifdef not terminated at EOF\n");
	    }
	    buf = string (yyourtext(), yyourleng());
	    return tok;
	case VP_UNDEFINEALL:
	    if (!m_off) {
		if (debug()>=5) cout<<"Undefineall "<<endl;
		m_preprocp->undefineall();
	    }
	    goto next_tok;
	case VP_STRIFY:
	    // We must expand macros in the body of the stringification
	    // Then, when done, form a final string to return
	    // (it could be used as a include filename, for example, so need the string token)
	    statePush(ps_STRIFY);
	    goto next_tok;
	case VP_SYMBOL:
	case VP_STRING:
	case VP_PSL:
	case VP_TEXT: {
	    m_defDepth = 0;
	    if (!m_off) {
		buf = string (yyourtext(), yyourleng());
		return tok;
	    }
	    else goto next_tok;
	}
	case VP_WHITE:		// Handled at top of loop
	case VP_COMMENT:	// Handled at top of loop
	case VP_DEFFORM:	// Handled by state=ps_DEFFORM;
	case VP_DEFVALUE:	// Handled by state=ps_DEFVALUE;
	default:
	    fatalSrc((string)"Internal error: Unexpected token "+tokenName(tok)+"\n");
	    break;
	}
	buf = string (yyourtext(), yyourleng());
	return tok;
    }
}

int VPreProcImp::getFinalToken(string& buf) {
    // Return the next user-visible token in the input stream.
    // Includes and such are handled here, and are never seen by the caller.
    if (!m_finAhead) {
	m_finAhead = true;
	m_finToken = getStateToken(m_finBuf);
    }
    int tok = m_finToken;
    buf = m_finBuf;
    if (0 && debug()>=5) {
	string bufcln = VPreLex::cleanDbgStrg(buf);
	fprintf (stderr,"%d: FIN:      %-10s: %s\n",
		 m_lexp->m_tokFilelinep->lineno(), tokenName(tok), bufcln.c_str());
    }
    // Track `line
    const char* bufp = buf.c_str();
    while (*bufp == '\n') bufp++;
    if ((tok == VP_TEXT || tok == VP_LINE) && 0==strncmp(bufp,"`line ",6)) {
	int enter;
	m_finFilelinep = m_finFilelinep->lineDirective(bufp, enter/*ref*/);
    }
    else {
	if (m_finAtBol && !(tok==VP_TEXT && buf=="\n")
	    && m_preprocp->lineDirectives()) {
	    if (int outBehind = m_lexp->m_tokFilelinep->lineno() - m_finFilelinep->lineno()) {
		if (debug()>=5) fprintf(stderr,"%d: FIN: readjust, fin at %d  request at %d\n",
					m_lexp->m_tokFilelinep->lineno(),
					m_finFilelinep->lineno(), m_lexp->m_tokFilelinep->lineno());
		m_finFilelinep = m_finFilelinep->create(m_lexp->m_tokFilelinep->filename(),m_lexp->m_tokFilelinep->lineno());
		if (outBehind > 0 && outBehind <= (int)VPreProc::NEWLINES_VS_TICKLINE) {
		    // Output stream is behind, send newlines to get back in sync
		    // (Most likely because we're completing a disabled `endif)
		    if (m_preprocp->keepWhitespace()) {
			buf = string(outBehind,'\n');
			return VP_TEXT;
		    }
		} else {
		    // Need to backup, use `line
		    buf = m_finFilelinep->lineDirectiveStrg(0);
		    return VP_LINE;
		}
	    }
	}
	// Track newlines in prep for next token
	for (string::iterator cp=buf.begin(); cp!=buf.end(); ++cp) {
	    if (*cp == '\n') {
		m_finAtBol = true;
		m_finFilelinep->linenoIncInPlace();  // Increment in place to avoid new/delete calls.  It's private data.
	    } else {
		m_finAtBol = false;
	    }
	}
    }
    m_finAhead = false;  // Consumed the token
    return tok;
}

string VPreProcImp::getparseline(bool stop_at_eol, size_t approx_chunk) {
    // Get a single line from the parse stream.  Buffer unreturned text until the newline.
    if (isEof()) return "";
    while (1) {
	const char* rtnp = NULL;
	bool gotEof = false;
	while ((stop_at_eol
		? (NULL==(rtnp=strchr(m_lineChars.c_str(),'\n')))
		: (approx_chunk==0 || (m_lineChars.length() < approx_chunk)))
	       && !gotEof) {
	    string buf;
	    int tok = getFinalToken(buf/*ref*/);
	    if (debug()>=5) {
		string bufcln = VPreLex::cleanDbgStrg(buf);
		fprintf (stderr,"%d: GETFETC:  %-10s: %s\n",
			 m_lexp->m_tokFilelinep->lineno(), tokenName(tok), bufcln.c_str());
	    }
	    if (tok==VP_EOF) {
		// Add a final newline, if the user forgot the final \n.
		if (m_lineChars != "" && m_lineChars[m_lineChars.length()-1] != '\n') {
		    m_lineChars.append("\n");
		}
		gotEof = true;
	    }
	    else if (tok==VP_PSL) {
		m_lineChars.append(" psl ");
	    }
	    else {
		m_lineChars.append(buf);
	    }
	}

	// Make new string with data up to the newline.
	size_t len = stop_at_eol ? (rtnp-m_lineChars.c_str()+1) : m_lineChars.length();
	string theLine(m_lineChars, 0, len);
	m_lineChars = m_lineChars.erase(0,len);	// Remove returned characters

	if (!m_preprocp->keepWhitespace() && !gotEof) {
	    const char* cp=theLine.c_str();
	    for (; *cp && (isspace(*cp) || *cp=='\n'); cp++) {}
	    if (!*cp) continue;
	}

	if (debug()>=4) {
	    string lncln = VPreLex::cleanDbgStrg(theLine);
	    fprintf (stderr,"%d: GETLINE:  %s\n",
		     m_lexp->m_tokFilelinep->lineno(), lncln.c_str());
	}
	return theLine;
    }
}
