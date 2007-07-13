#/* Verilog.xs -- Verilog Booter  -*- C++ -*-
#* $Id$
#*********************************************************************
#*
#* DESCRIPTION: Verilog::Parser Perl XS interface
#* 
#* Author: Wilson Snyder <wsnyder@wsnyder.org>
#* 
#* Code available from: http://www.veripool.com/
#* 
#*********************************************************************
#* 
#* Copyright 2000-2007 by Wilson Snyder.  This program is free software;
#* you can redistribute it and/or modify it under the terms of either the GNU
#* General Public License or the Perl Artistic License.
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
#include "VParse.h"

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
#// Parseressor derived classes, so we can override the callbacks to call perl.

class VParserXs : public VParse {
public:
    SV*		m_self;	// Class called from
    VFileLine*	m_cbFilelinep;	///< Last callback's starting point

    VFileLine* cbFilelinep() const { return m_cbFilelinep; }
    void cbFileline(const string& filename, int lineno) { m_cbFilelinep = m_cbFilelinep->create(filename, lineno); }
    void cbFileline(VFileLine* filelinep) { m_cbFilelinep = filelinep; }

    VParserXs(VFileLine* filelinep, bool sigparser, bool useUnreadbackFlag)
	: VParse(filelinep, sigparser, useUnreadbackFlag)
	  , m_cbFilelinep(filelinep)
	{}
    virtual ~VParserXs() {}

    // Verilog::Parser Callback methods
    virtual void attributeCb(VFileLine* fl, const string& text);
    virtual void commentCb(VFileLine* fl, const string& text);
    virtual void keywordCb(VFileLine* fl, const string& text);
    virtual void numberCb(VFileLine* fl, const string& text);
    virtual void operatorCb(VFileLine* fl, const string& text);
    virtual void preprocCb(VFileLine* fl, const string& text);
    virtual void stringCb(VFileLine* fl, const string& text);
    virtual void symbolCb(VFileLine* fl, const string& text);
    virtual void sysfuncCb(VFileLine* fl, const string& text);

    // Verilog::SigParser Callback methods
    virtual void attributeCb(VFileLine* fl, const string& kwd, const string& text);
    virtual void functionCb(VFileLine* fl, const string& kwd, const string& name, const string& type);
    virtual void instantCb(VFileLine* fl, const string& mod, const string& cell, const string& range);
    virtual void moduleCb(VFileLine* fl, const string& kwd, const string& name, bool celldefine);
    virtual void paramPinCb(VFileLine* fl, const string& name, const string& conn, int number);
    virtual void pinCb(VFileLine* fl, const string& name, const string& conn, int number);
    virtual void portCb(VFileLine* fl, const string& name);
    virtual void signalCb(VFileLine* fl, const string& kwd, const string& name,
			  const string& vec, const string& mem, const string& signd,
			  const string& value,
			  bool inFunc);
    virtual void taskCb(VFileLine* fl, const string& kwd, const string& name);

    void call(string* rtnStrp, int params, const char* method, ...);
};

class VFileLineParseXs : public VFileLine {
    VParserXs*	m_vParserp;		// Parser handling the errors
public:
    VFileLineParseXs(int called_only_for_default) : VFileLine(called_only_for_default) {}
    virtual ~VFileLineParseXs() { }
    virtual VFileLine* create(const string filename, int lineno);
    virtual void error(const string msg);	// Report a error at given location
    void setParser(VParserXs* pp) { m_vParserp=pp; }
};

#//**********************************************************************
#// Overrides error handling virtual functions to invoke callbacks

VFileLine* VFileLineParseXs::create(const string filename, int lineno) {
    VFileLineParseXs* filelp = new VFileLineParseXs(true);
    filelp->init(filename, lineno);
    filelp->m_vParserp = m_vParserp;
    return filelp;
}

void VFileLineParseXs::error(string msg) {
    static string holdmsg; holdmsg = msg;
    m_vParserp->cbFileline(this);
    m_vParserp->call(NULL, 1,"error",holdmsg.c_str());
}

#//**********************************************************************
#// Overrides of virtual functions to invoke callbacks

// Verilog::Parser Callback methods
void VParserXs::attributeCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"attribute",hold1.c_str());
}
void VParserXs::commentCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"comment",hold1.c_str());
}
void VParserXs::keywordCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"keyword",hold1.c_str());
}
void VParserXs::numberCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"number",hold1.c_str());
}
void VParserXs::operatorCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"operator",hold1.c_str());
}
void VParserXs::preprocCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"preproc",hold1.c_str());
}
void VParserXs::stringCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"string",hold1.c_str());
}
void VParserXs::symbolCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"symbol",hold1.c_str());
}
void VParserXs::sysfuncCb(VFileLine* fl, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = text;
    call(NULL, 1,"sysfunc",hold1.c_str());
}

// Verilog::SigParser Callback methods
void VParserXs::attributeCb(VFileLine* fl, const string& kwd, const string& text) {
    cbFileline(fl);
    static string hold1; hold1 = kwd;
    static string hold2; hold2 = text;
    call(NULL, 2,"attribute",hold1.c_str(), hold2.c_str());
}
void VParserXs::functionCb(VFileLine* fl, const string& kwd, const string& name, const string& type) {
    cbFileline(fl);
    static string hold1; hold1 = kwd;
    static string hold2; hold2 = name;
    static string hold3; hold3 = type;
    call(NULL, 3,"function",hold1.c_str(), hold2.c_str(), hold3.c_str());
}
void VParserXs::instantCb(VFileLine* fl, const string& mod, const string& cell, const string& range) {
    cbFileline(fl);
    static string hold1; hold1 = mod;
    static string hold2; hold2 = cell;
    static string hold3; hold3 = range;
    call(NULL, 3,"instant",hold1.c_str(), hold2.c_str(), hold3.c_str());
}
void VParserXs::moduleCb(VFileLine* fl, const string& kwd, const string& name, bool celldefine) {
    cbFileline(fl);
    static string hold1; hold1 = kwd;
    static string hold2; hold2 = name;
    //Unused
    static string hold4; hold4 = celldefine?"1":"0";
    call(NULL, 4,"module",hold1.c_str(), hold2.c_str(), NULL, hold4.c_str());
}
void VParserXs::paramPinCb(VFileLine* fl, const string& name, const string& conn, int number) {
    cbFileline(fl);
    static string hold1; hold1 = name;
    static string hold2; hold2 = conn;
    static char num3[100]; sprintf(num3,"%d",number);
    static string hold3; hold3 = num3;
    call(NULL, 3,"parampin",hold1.c_str(), hold2.c_str(), hold3.c_str());
}
void VParserXs::pinCb(VFileLine* fl, const string& name, const string& conn, int number) {
    cbFileline(fl);
    static string hold1; hold1 = name;
    static string hold2; hold2 = conn;
    static char num3[100]; sprintf(num3,"%d",number);
    static string hold3; hold3 = num3;
    call(NULL, 3,"pin",hold1.c_str(), hold2.c_str(), hold3.c_str());
}
void VParserXs::portCb(VFileLine* fl, const string& name) {
    cbFileline(fl);
    static string hold1; hold1 = name;
    call(NULL, 1,"port",hold1.c_str());
}
void VParserXs::signalCb(VFileLine* fl, const string& kwd, const string& name,
			 const string& vec, const string& mem, const string& signd,
			 const string& value,
			 bool inFunc) {
    cbFileline(fl);
    static string hold1; hold1 = kwd;
    static string hold2; hold2 = name;
    static string hold3; hold3 = vec;
    static string hold4; hold4 = mem;
    static string hold5; hold5 = signd;
    static string hold6; hold6 = value;
    call(NULL, 6, (inFunc?"funcsignal":"signal_decl"),
	 hold1.c_str(), hold2.c_str(),
	 hold3.c_str(), hold4.c_str(), hold5.c_str(), hold6.c_str());
}
void VParserXs::taskCb(VFileLine* fl, const string& kwd, const string& name) {
    cbFileline(fl);
    static string hold1; hold1 = kwd;
    static string hold2; hold2 = name;
    call(NULL, 2,"task",hold1.c_str(), hold2.c_str());
}


void VParserXs::call (
    string* rtnStrp,	/* If non-null, load return value here */
    int params,		/* Number of parameters */
    const char* method,	/* Name of method to call */
    ...)		/* Arguments to pass to method's @_ */
{
    // Call $perlself->method (passedparam1, parsedparam2)
    if (debug()) cout << "CALLBACK "<<method<<endl;
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
	    if (text) {
		sv = newSVpv (text, 0);
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

MODULE = Verilog::Parser  PACKAGE = Verilog::Parser

#//**********************************************************************
#// self->_new (class, sigparser)

static VParserXs *
VParserXs::_new (SV* SELF, bool sigparser, bool useUnreadback)
PROTOTYPE: $$
CODE:
{
    if (CLASS) {}  /* Prevent unused warning */
    VFileLineParseXs* filelinep = new VFileLineParseXs(1/*ok,for initial*/);
    VParserXs* parserp = new VParserXs(filelinep, sigparser, useUnreadback);
    filelinep->setParser(parserp);
    parserp->m_self = newSVsv(SELF);
    RETVAL = parserp;
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->_DESTROY()

void
VParserXs::_DESTROY()
CODE:
{
    delete THIS;
}
#//**********************************************************************
#// self->debug()

void
VParserXs::_debug (level)
int level
PROTOTYPE: $$
CODE:
{
    THIS->debug(level);
}

#//**********************************************************************
#// self->eof()

void
VParserXs::eof ()
PROTOTYPE: $
CODE:
{
    THIS->setEof();
}
#//**********************************************************************
#// self->filename([setit])

const char *
VParserXs::filename (const char* flagp="")
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    if (items > 1) {
	THIS->inFileline(flagp, THIS->inFilelinep()->lineno());
	THIS->cbFileline(flagp, THIS->inFilelinep()->lineno());
    }
    RETVAL = THIS->cbFilelinep()->filename().c_str();
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->lineno([setit])

int
VParserXs::lineno (int flag=0)
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    if (items > 1) {
	THIS->inFileline(THIS->inFilelinep()->filename(), flag);
	THIS->cbFileline(THIS->inFilelinep()->filename(), flag);
    }
    RETVAL = (THIS->cbFilelinep()->lineno());
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->parse()

void
VParserXs::parse (const char* textp)
PROTOTYPE: $$
CODE:
{
    THIS->parse(textp);
}

#//**********************************************************************
#// self->unreadback()

SV*
VParserXs::unreadback (const char* flagp="")
PROTOTYPE: $;$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    // Set RETVAL to a SV before we replace with the new value, and c_str may change
    RETVAL = newSVpv(THIS->unreadback().c_str(), THIS->unreadback().length());
    if (items > 1) {
	THIS->unreadback(flagp);
    }
}
OUTPUT: RETVAL

#//**********************************************************************
#// self->unreadbackCat()

void
VParserXs::unreadbackCat (SV* textsvp)
PROTOTYPE: $$
CODE:
{
    if (!THIS) XSRETURN_UNDEF;
    STRLEN textlen;
    const char* textp = SvPV(textsvp, textlen);
    THIS->unreadbackCat(textp, textlen);
}
