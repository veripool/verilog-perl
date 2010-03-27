#/* Verilog.xs -- Verilog Booter  -*- C++ -*-
#*********************************************************************
#*
#* DESCRIPTION: Verilog::Preproc Perl XS interface
#*
#* Author: Wilson Snyder <wsnyder@wsnyder.org>
#*
#* Code available from: http://www.veripool.org/
#*
#*********************************************************************
#*
#* Copyright 2000-2010 by Wilson Snyder.  This program is free software;
#* you can redistribute it and/or modify it under the terms of either the GNU
#* Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
#*
#* This program is distributed in the hope that it will be useful,
#* but WITHOUT ANY WARRANTY; without even the implied warranty of
#* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#* GNU General Public License for more details.
#*
#* You should have received a copy of the Perl Artistic License
#* along with this module; see the file COPYING.  If not, see
#* www.cpan.org
#*
#***********************************************************************
#* Note with C++ XS libraries, the CLASS parameter is implied...
#***********************************************************************/

/* Mine: */
#include "VPreproc.h"
#include <deque>

/* Perl */
extern "C" {
# include "EXTERN.h"
# include "perl.h"
# include "XSUB.h"
}

#ifdef open
# undef open	/* Perl 64 bit on solaris has a nasty hack that redefines open */
#endif

class VFileLineXs;

#//**********************************************************************
#// Preprocessor derived classes, so we can override the callbacks to call perl.

class VPreprocXs : public VPreproc {
public:
    SV*		m_self;	// Class called from (the hash, not SV pointing to the hash)
    int		m_keepComments;
    int		m_keepWhitespace;
    bool	m_lineDirectives;
    bool	m_pedantic;
    deque<VFileLineXs*> m_filelineps;

    VPreprocXs(VFileLine* filelinep) : VPreproc(filelinep) {}
    virtual ~VPreprocXs();

    // Control methods
    virtual int  keepComments() { return m_keepComments; }	// Return comments
    virtual int  keepWhitespace() { return m_keepWhitespace; }	// Return extra whitespace
    virtual bool lineDirectives() { return m_lineDirectives; }	// Insert `line directives
    virtual bool pedantic() { return m_pedantic; }		// Obey standard; Don't substitute `error

    // Callback methods
    virtual void comment(string filename);	// Comment for keepComments=>sub
    virtual void include(string filename);	// Request a include file be processed
    virtual void define(string name, string value, string params); // `define with parameters
    virtual void undef(string name);		// Remove a definition
    virtual void undefineall();			///< Remove all non-command-line definitions
    virtual string defParams(string name);	// Return parameter list if define exists
    virtual string defValue(string name);	// Return value of given define (should exist)
    virtual string defSubstitute(string substitute);	///< Return value to substitute for given post-parameter value

    void call(string* rtnStrp, int params, const char* method, ...);
    void unreadback(char* text);
};

class VFileLineXs : public VFileLine {
    VPreprocXs*	m_vPreprocp;		// Parser handling the errors
public:
    VFileLineXs(VPreprocXs* pp) : VFileLine(true), m_vPreprocp(pp) { if (pp) pushFl(); }
    virtual ~VFileLineXs() { }
    virtual VFileLine* create(const string& filename, int lineno) {
	VFileLineXs* filelp = new VFileLineXs(m_vPreprocp);
	filelp->init(filename, lineno);
	return filelp;
    }
    virtual void error(const string& msg);	// Report a error at given location
    void setPreproc(VPreprocXs* pp) {
	m_vPreprocp=pp;
	pushFl(); // The very first construction used pp=NULL, as pp wasn't created yet so make it now
    }
    // Record the structure so we can delete it later
    void pushFl() { m_vPreprocp->m_filelineps.push_back(this); }
};

#//**********************************************************************
#// Overrides error handling virtual functions to invoke callbacks

void VFileLineXs::error(const string& msg) {
    static string holdmsg; holdmsg = msg;
    m_vPreprocp->call(NULL, 1,"error",holdmsg.c_str());
}

#//**********************************************************************
#// VPreprocXs functions

VPreprocXs::~VPreprocXs() {
    for (deque<VFileLineXs*>::iterator it=m_filelineps.begin(); it!=m_filelineps.end(); ++it) {
	delete *it;
    }
}

#//**********************************************************************
#// Overrides of virtual functions to invoke callbacks

void VPreprocXs::comment(string cmt) {
    static string holdcmt; holdcmt = cmt;
    call(NULL, 1,"comment",holdcmt.c_str());
}
void VPreprocXs::include(string filename) {
    static string holdfilename; holdfilename = filename;
    call(NULL, 1,"include",holdfilename.c_str());
}
void VPreprocXs::undef(string define) {
    static string holddefine; holddefine = define;
    call(NULL, 1,"undef", holddefine.c_str());
}
void VPreprocXs::undefineall() {
    call(NULL, 0,"undefineall");
}
void VPreprocXs::define(string define, string value, string params) {
    static string holddefine; holddefine = define;
    static string holdvalue; holdvalue = value;
    static string holdparams; holdparams = params;
    // 4th argument is cmdline; always undef from here
    call(NULL, 3,"define", holddefine.c_str(), holdvalue.c_str(), holdparams.c_str());
}
string VPreprocXs::defParams(string define) {
    static string holddefine; holddefine = define;
    string paramStr;
    call(&paramStr, 1,"def_params", holddefine.c_str());
    return paramStr;
}
string VPreprocXs::defValue(string define) {
    static string holddefine; holddefine = define;
    string valueStr;
    call(&valueStr, 1,"def_value", holddefine.c_str());
    return valueStr;
}
string VPreprocXs::defSubstitute(string subs) {
    static string holdsubs; holdsubs = subs;
    string outStr;
    call(&outStr, 1, "def_substitute", holdsubs.c_str());
    return outStr;
}

void VPreprocXs::call (
    string* rtnStrp,	/* If non-null, load return value here */
    int params,		/* Number of parameters.  Negative frees the parameters */
    const char* method,	/* Name of method to call */
    ...)		/* Arguments to pass to method's @_ */
{
    // Call $perlself->method (passedparam1, parsedparam2)
    va_list ap;
    va_start(ap, method);
    {
	dSP;				/* Initialize stack pointer */
	ENTER;				/* everything created after here */
	SAVETMPS;			/* ...is a temporary variable. */
	PUSHMARK(SP);			/* remember the stack pointer */
	SV* selfsv = newRV_inc(m_self);	/* $self-> */
	XPUSHs(sv_2mortal(selfsv));

	while (params--) {
	    char* text = va_arg(ap, char *);
	    SV* sv;
	    if (text) {
		sv = sv_2mortal(newSVpv (text, 0));
	    } else {
		sv = &PL_sv_undef;
	    }
	    XPUSHs(sv);			/* token */
	}

	PUTBACK;			/* make local stack pointer global */

	if (rtnStrp) {
	    int rtnCount = perl_call_method ((char*)method, G_SCALAR);
	    SPAGAIN;			/* refresh stack pointer */
	    if (rtnCount > 0) {
		SV* sv = POPs;
		//printf("RTN %ld %d %s\n", SvTYPE(sv),SvTRUE(sv),SvPV_nolen(sv));
#ifdef SvPV_nolen	// Perl 5.6 and later
		*rtnStrp = SvPV_nolen(sv);
#else
		*rtnStrp = SvPV(sv,PL_na);
#endif
	    }
	    PUTBACK;
	} else {
	    perl_call_method ((char*)method, G_DISCARD | G_VOID);
	}

	FREETMPS;			/* free that return value */
	LEAVE;				/* ...and the XPUSHed "mortal" args.*/
    }
    va_end(ap);
}

#//**********************************************************************

MODULE = Verilog::Preproc  PACKAGE = Verilog::Preproc

#//**********************************************************************
#// self->_new (class, keepcmt, keepwhite, linedir, pedantic)

static VPreprocXs *
VPreprocXs::_new (SELF, keepcmt, keepwhite, linedir, pedantic)
SV *SELF
int keepcmt
int keepwhite
int linedir
int pedantic
PROTOTYPE: $$$$$
CODE:
{
    if (CLASS) {}  /* Prevent unused warning */
    if (!SvROK(SELF)) { warn("${Package}::$func_name() -- SELF is not a hash reference"); }
    VFileLineXs* filelinep = new VFileLineXs(NULL/*ok,for initial*/);
    VPreprocXs* preprocp = new VPreprocXs(filelinep);
    filelinep->setPreproc(preprocp);
    preprocp->m_self = SvRV(SELF);
    preprocp->m_keepComments = keepcmt;
    preprocp->m_keepWhitespace = keepwhite;
    preprocp->m_lineDirectives = linedir;
    preprocp->m_pedantic = pedantic;
    RETVAL = preprocp;
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->_DESTROY()

void
VPreprocXs::_DESTROY()
PROTOTYPE: $
CODE:
{
    delete THIS;
}
#//**********************************************************************
#// self->debug()

void
VPreprocXs::_debug (level)
int level
PROTOTYPE: $$
CODE:
{
    THIS->debug(level);
}

#//**********************************************************************
#// self->lineno()

int
VPreprocXs::lineno ()
PROTOTYPE: $
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    RETVAL = (THIS->filelinep()->lineno());
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->filename()

const char *
VPreprocXs::filename ()
PROTOTYPE: $
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    RETVAL = THIS->filelinep()->filename().c_str();
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->unreadback()

void
VPreprocXs::unreadback (text)
char* text
PROTOTYPE: $$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    THIS->insertUnreadback((string)text);
}

#//**********************************************************************
#// self->getall()

const char *
VPreprocXs::getall (approx_chunk=0)
size_t approx_chunk
PROTOTYPE: $;$
CODE:
{
    static string holdline;
    if (!THIS || THIS->isEof()) XSRETURN_UNDEF;
    if (approx_chunk==0) { approx_chunk = 1;  approx_chunk <<= 62; }
    string lastline = THIS->getall(approx_chunk);
    holdline = lastline;	/* Stash it so c_str() doesn't disappear immediately */
    RETVAL = lastline.c_str();
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->getline()

const char *
VPreprocXs::getline ()
PROTOTYPE: $
CODE:
{
    static string holdline;
    if (!THIS || THIS->isEof()) XSRETURN_UNDEF;
    string lastline = THIS->getline();
    holdline = lastline;	/* Stash it so c_str() doesn't disappear immediately */
    RETVAL = lastline.c_str();
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->eof()

int
VPreprocXs::eof ()
PROTOTYPE: $
CODE:
{
    RETVAL = THIS->isEof();
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->_open (filename)

int
VPreprocXs::_open (filename)
const char *filename
PROTOTYPE: $$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    THIS->openFile(filename);
    RETVAL = 1;
}
OUTPUT: RETVAL

