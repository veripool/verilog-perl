#$Id$
######################################################################
#
# Copyright 2001-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Preproc;
use Carp;
use Verilog::Getopt;

require DynaLoader;
@ISA = qw(DynaLoader);

use strict;
use vars qw($VERSION);

$VERSION = '2.316';

######################################################################
#### Configuration Section

bootstrap Verilog::Preproc;

######################################################################
#### Accessors

sub new {
    my $class = shift;  $class = ref $class if ref $class;
    my $self = {keep_comments=>1,
		line_directives=>1,
		pedantic=>0,
		options=>Verilog::Getopt->new(),	# If the user didn't give one, still work!
		@_};
    bless $self, $class;
    # Sets $self->{_cthis}
    $self->{keep_comments} = 2 if ($self->{keep_comments} eq 'sub');
    $self->_new(
		$self,
		$self->{keep_comments},
		$self->{line_directives},
		$self->{pedantic},
		);
    #use Data::Dumper; print Dumper($self);
    return $self;
}

sub open {
    my $self = shift;
    my $filename = shift;
    # Allow user to put `defined names on the command line instead of filenames,
    # then convert them properly.
    $filename = $self->remove_defines($filename);
    printf ("Perl open $filename\n") if $self->{debug};
    $filename = $self->{options}->file_path($filename);
    printf ("Perl openfp $filename\n") if $self->{debug};
    if (!-r $filename) {
	$self->error("Cannot open $filename");
    } else {
	$self->_open($filename);
    }
}

sub debug {
    my $self = shift;
    my $level = shift;
    $self->{debug} = $level;
    $self->_debug($level);
}

#In Preproc.xs:
# sub _new (class, keepcmt, linedir, pedantic)
# sub _open (class)
# sub getline (class)
# sub eof (class)
# sub filename (class)
# sub lineno (class)
# sub unreadback (class, text)

######################################################################
#### Utilities

sub remove_defines {
    my $self = shift;
    my $sym = shift;
    my $val = "x";
    while (defined $val) {
	last if $sym eq $val;
	(my $xsym = $sym) =~ s/^\`//;
	$val = $self->{options}->defvalue_nowarn($xsym);  #Undef if not found
	$sym = $val if defined $val;
    }
    return $sym;
}

sub fileline {
    my $self = shift;
    return ($self->filename||"").":".($self->lineno||"");
}

######################################################################
#### Called by the parser

sub error {
    my ($self,$text,$token)=@_;
    my $fileline = $self->filename.":".$self->lineno;
    croak ("%Error: $fileline: $text\n"
	   ."Stopped");
}

sub comment {}

sub include {
    my ($self,$filename)=@_;
    print "INCLUDE $filename\n" if $self->{debug};
    $self->open($filename);
}

# Note rather then overriding these, a derived Verilog::Getopt class can
# accomplish the same thing.

sub undef {
    my $self = shift;
    $self->{options}->undef(@_);
}
sub define {
    my $self = shift;
    #print "DEFINE @_\n";
    $self->{options}->fileline($self->filename.":".$self->lineno);
    $self->{options}->define(@_);
}
sub def_params {
    # Return define parameters
    my $self = shift;
    my $val = $self->{options}->defparams(@_);
    #printf "DEFEXISTS @_ -> %s\n", $val if $self->{debug};
    $val = "" if !defined $val;
    return $val;
}
sub def_value {
    # Return value
    my $self = shift;
    #printf "DEFVALUE @_ -> %s\n", $self->{options}->defvalue_nowarn(@_);
    return $self->{options}->defvalue(@_);
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Preproc - Preprocess Verilog files

=head1 SYNOPSIS

    use Verilog::Getopt;

    my $vp = Verilog::Preproc->new(I<parameters>);
    $vp->open("verilog_file.v");
    my $line = $vp->getline();

=head1 EXAMPLE

    # This is a complete verilog pre-parser!
    # For a command line version, see vppp
    use Verilog::Getopt;
    use Verilog::Preproc;

    my $opt = new Verilog::Getopt;
    @ARGV = $opt->parameter(@ARGV);

    my $vp = Verilog::Preproc->new(options=>$opt,);
    $vp->open("verilog_file.v");
    while (defined (my $line = $vp->getline())) {
       print $line;
    }

=head1 DESCRIPTION

L<Verilog::Preproc> reads Verilog files, and preprocesses them according
to the Verilog 2001 specification.  Programs can be easily converted from
reading a IO::File into reading preprocessed output from Verilog::Preproc.

=head1 MEMBER FUNCTIONS

=over 4

=item $self->eof()

Returns true at the end of the file.

=item $self->filename()

Returns the filename of the most recently returned getline().  May not match
the filename passed on the command line, as `line directives are honored.

=item $self->getline()

Return the next line of text.  Returns undef at EOF.  (Just like
IO::File->getline().)

=item $self->lineno()

Returns the line number of the last getline().  Note that the line number
may change several times between getline(), for example when traversing
multiple include files.

=item $self->new(I<parameters>)

Creates a new preprocessor.  See the PARAMETERS section for the options
that may be passed to new.

=item $self->open(I<filename>)

Opens the specified file.  If called before a file is completely parsed,
the new file will be parsed completely before returning to the previously
open file.  (As if it was an include file.)

=item $self->unreadback(I<text>)

Insert text into the input stream at the given point.  The text will not
be parsed, just returned to the application.  This lets comment() callbacks
insert special code into the output stream.

=back

=head1 PARAMETERS

The following named parameters may be passed to the new constructor.

=over 4

=item keep_comments=>0

With keep_comments set to zero, strip all comments.  When set to one (the
default), insert comments in output streams.  When set to 'sub', call the
comment() function so that meta-comments can be processed outside of the
output stream.  Note that some programs use meta-comments to embed useful
information (synthesis and lint), so use this with caution if feeding to
tools other then your own.  Defaults to 1.

=item line_directives=>0

With line_directives set to zero, suppress "`line" comments which indicate
filename and line number changes.  Use the lineno() and filename() methods
instead to retrieve this information. Defaults true.

=item options=>Verilog::Getopt object

Specifies the object to be used for resolving filenames and defines.  Other
classes may be used, as long as their interface matches that of Getopt.

=item pedantic=>1

With pedantic set, rigorously obey the Verilog pedantic.  This disables
the `__FILE__ and `__LINE__ features, and may disable other features that
are not specified in the language pedantic. Defaults false.

=back

=head1 CALLBACKS

Default callbacks are implemented that are suitable for most applications.
Derived classes may override these callbacks as needed.

=over 4

=item $self->comment(I<comment>)

Called with each comment, when keep_comments=>'sub' is used.  Defaults to
do nothing.

=item $self->undef(I<defname>)

Called with each `undef.  Defaults to use options object.

=item $self->define(I<defname>, I<value>, I<params>)

Called with each `define.  Defaults to use options object.

=item $self->def_exists(I<defname>)

Called to determine if the define exists.  Return true if the define
exists, or argument list with leading parenthesis if the define has
arguments.  Defaults to use options object.

=item $self->def_value(I<defname>)

Called to return value to substitute for specified define.  Defaults to use
options object.

=item $self->error(I<message>)

Called on errors, with the error message as an argument.  Defaults
to die.

=item $self->include(I<filename>)

Specifies a include file has been found.  Defaults to call $self->open
after resolving the filename with the options parameter.

=back

=head1 COMPLIANCE

The preprocessor supports the constructs defined in the Verilog 2001 and
SystemVerilog 3.1 standards.

Verilog::Preproc adds the following features (unless the pedantic parameter
is set.):

=over 4

=item `__FILE__  will be replaced by the current filename. (Like C++ __FILE__.)

=item `__LINE__  will be replaced by the current line number. (Like C++ __LINE__.)

=item `error I<"string"> will be reported whenever it is encountered. (Like C++ #error.)

These are useful for error macros, similar to assert() in C++.

=back

=head1 DISTRIBUTION

The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2006 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Language>, L<Verilog::Getopt>

L<IO::File> 

This package is layered on a C++ interface which may be found in the kit.

=cut
