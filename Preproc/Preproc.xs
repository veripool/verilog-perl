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
#* Copyright 2000-2009 by Wilson Snyder.  This program is free software;
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

/* Perl */
extern "C" {
# include "EXTERN.h"
# include "perl.h"
# include "XSUB.h"
}

#ifdef open
# undef open	/* Perl 64 bit on solaris has a nasty hack that redefines open */
#endif

#//**********************************************************************
#// Preprocessor derived classes, so we can override the callbacks to call perl.

class VPreprocXs : public VPreproc {
public:
    SV*		m_self;	// Class called from
    int		m_keepComments;
    int		m_keepWhitespace;
    bool	m_lineDirectives;
    bool	m_pedantic;

    VPreprocXs(VFileLine* filelinep) : VPreproc(filelinep) {}
    virtual ~VPreprocXs() {}

    // Control methods
    virtual int  keepComments() { return m_keepComments; }	// Return comments
    virtual int  keepWhitespace() { return m_keepWhitespace; }	// Return extra whitespace
    virtual bool lineDirectives() { return m_lineDirectives; }	// Insert `line directives
    virtual bool pedantic() { return m_pedantic; }		// Obey standard; Don't substitute `__FILE__ and `__LINE__

    // Callback methods
    virtual void comment(string filename);	// Comment for keepComments=>sub
    virtual void include(string filename);	// Request a include file be processed
    virtual void define(string name, string value, string params); // `define with parameters
    virtual void undef(string name);		// Remove a definition
    virtual string defParams(string name);	// Return parameter list if define exists
    virtual string defValue(string name);	// Return value of given define (should exist)

    void call(string* rtnStrp, int params, const char* method, ...);
    void unreadback(char* text);
};

class VFileLineXs : public VFileLine {
    VPreprocXs*	m_vPreprocp;		// Parser handling the errors
public:
    VFileLineXs(int called_only_for_default) : VFileLine(called_only_for_default) {}
    virtual ~VFileLineXs() { }
    virtual VFileLine* create(const string filename, int lineno);
    virtual void error(const string msg);	// Report a error at given location
    void setPreproc(VPreprocXs* pp) { m_vPreprocp=pp; }
};

#//**********************************************************************
#// Overrides error handling virtual functions to invoke callbacks

VFileLine* VFileLineXs::create(const string filename, int lineno) {
    VFileLineXs* filelp = new VFileLineXs(true);
    filelp->init(filename, lineno);
    filelp->m_vPreprocp = m_vPreprocp;
    return filelp;
}

void VFileLineXs::error(string msg) {
    static string holdmsg; holdmsg = msg;
    m_vPreprocp->call(NULL, 1,"error",holdmsg.c_str());
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
void VPreprocXs::define(string define, string value, string params) {
    static string holddefine; holddefine = define;
    static string holdvalue; holdvalue = value;
    static string holdparams; holdparams = params;
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
	XPUSHs(m_self);			/* $self-> */

	while (params--) {
	    char *text;
	    SV *sv;
	    text = va_arg(ap, char *);
	    sv = newSVpv (text, 0);
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
    VFileLineXs* filelinep = new VFileLineXs(1/*ok,for initial*/);
    VPreprocXs* preprocp = new VPreprocXs(filelinep);
    filelinep->setPreproc(preprocp);
    preprocp->m_self = newSVsv(SELF);
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
    THIS->open(filename);
    RETVAL = 1;
}
OUTPUT: RETVAL

