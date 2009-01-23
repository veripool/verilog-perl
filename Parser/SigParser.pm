# Verilog::SigParser.pm -- Verilog signal parsing
# See copyright, etc in below POD section.
######################################################################

package Verilog::SigParser;
require 5.000;

use strict;
use vars qw($VERSION $Debug);
use Carp;
use Verilog::Parser;
use base qw(Verilog::Parser);

######################################################################
#### Configuration Section

$VERSION = '3.100';

#######################################################################

# parse, parse_file, etc are inherited from Verilog::Parser
sub new {
    my $class = shift;

    my $self = $class->SUPER::new(_sigparser => 1,
				  use_unreadback => 0,
				  @_);
    bless $self, $class;
    $self->debug($Debug) if $Debug;
    $self->{metacomment} = {} unless defined $self->{metacomment};
    return $self;
}

sub metacomment {
    my $self = shift;
    return $self->{metacomment};
}

#######################################################################
# Parser callbacks - backward compatibility

sub comment {
    my $self = shift;
    my $text = shift;	# Includes comment delimiters
    if ($text =~ m!^(/.)\s* ([\$A-Za-z]\w*)\s+ (\w+) !x) {
	my ($delim, $category, $name) = ($1, $2, $3);
	if ($self->{metacomment}->{$category}) {
	    print "GotaMeta $category $name\n"    if ($Debug);
	    if ($delim eq "/*") { $text =~ s!\s*\*/$!!; }
	    else { $text =~ s!\s+$!!; }
	    $text =~ s!^/.\s*!!;
	    $self->attribute( $text );
	}
    }
    $self->SUPER::comment($text);
}

#######################################################################
# Null callbacks

# The my's aren't needed since we do nothing, but are useful if the
# user copies them from here to their program.

sub endcell {
    my $self = shift;
}

sub endinterface {
    my $self = shift;
}

sub endtaskfunc {
    my $self = shift;
}

sub endmodule {
    my $self = shift;
}

sub function {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $type = shift;
}

sub instant {
    my $self = shift;
    my $module = shift;
    my $cell = shift;
    my $range = shift;
}

sub interface {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
}

sub module {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    shift;  # Ignored
    my $in_celldefine = shift;
}

sub pin {
    my $self = shift;
    my $name = shift;
    my $conn = shift;
    my $number = shift;
}

sub parampin {
    my $self = shift;
    my $name = shift;
    my $conn = shift;
    my $number = shift;
}

sub port {
    my $self = shift;
    my $name = shift;
}

sub ppdefine {
    my $self = shift;
    my $defvar = shift;
    my $definition = shift;
}

sub signal_decl {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $vector = shift;
    my $mem = shift;
    my $signed = shift;
    my $value = shift;
}

sub funcsignal {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $vector = shift;
    my $mem = shift;
    my $signed = shift;
    my $value = shift;
}

sub task {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
}

######################################################################
### Package return
1;
__END__
=pod

=head1 NAME

Verilog::SigParser - Signal Parsing for Verilog language files

=head1 SYNOPSIS

  use Verilog::Preproc;
  use Verilog::SigParser;

  my $pp = Verilog::Preproc->new(keep_comments=>0,);

  my $parser = new Verilog::SigParser;
  $parser->parse_preproc_file ($pp);
  # The below described callbacks are then invoked

=head1 DESCRIPTION

Verilog::SigParser builds upon the Verilog::Parser module to provide
callbacks for when a signal is declared, a module instantiated, or a module
defined.

See the "Which Package" section of L<Verilog::Language> if you are unsure
which parsing package to use for a new application.  For a higher level
interface to this package, see L<Verilog::Netlist>.

=head1 METHODS

The method interface to Verilog::SigParser is described in the
Verilog::Parser module which this package inherits.  You will probably want
to use the preprocessing option of Verilog::Parser with this package.

=head1 CALLBACKS

In order to make the parser do anything interesting, you must make a
subclass where you override one or more of the following methods as
appropriate:

=over 4

=item $self->attribute ( $text )

Scanned an attribute or meta-comment.  The parser inspects the first word
of each comment line (C<//key rest> to end of line) or comment block
(C</*key rest */).  It calls C<$self->attribute( meta_text )>
if the first word has a true value in hash C<$self->metacomment>.

=item $self->endcell ( $token )

This method is called at the end of defining a cell. It is useful for
writing clean up routines.

=item $self->endinterface ( $token )

This method is called at a endinterface keyword. It is useful for writing
clean up routines.

=item $self->endtaskfunc ( $token )

This method is called at a endfunction or endtask keyword.  It is useful
for writing clean up routines.

=item $self->endmodule ( $token )

This method is called at a endmodule keyword. It is useful for writing
clean up routines.

=item $self->funcsignal ( $keyword, $signame, $vector, $mem, $signed, $value )

This method is called when a signal/variable is declared inside a function.
See signal_decl for more details.

=item $self->function ( $keyword, $name, $type )

This method is called when a function is defined.  Type is the output size
or typename, plus "signed", for example "", "[3:0]", "integer", or "signed
[2:0]".

=item $self->instant ( $module, $cell, $range )

This method is called when a instantiation is defined.  The first parameter
is the name of the module being instantiated. The second parameter is the
name of the cell, which may be "" for primitives.  The third is the range
if the cell was arrayed.

Prior to version 3.000, the name of the parameters were also included in
this callback. This has been replaced with the parampin callback.

=item $self->interface ( $keyword, $name )

This method is called when an interface is defined.

=item $self->module ( $keyword, $name, ignored, $in_celldefine )

This method is called when a module is defined.

=item $self->parampin ( $name, $connection, $index )

This method is called when a parameter is connected to an instantiation, IE
the "#(...)" syntax.  It is also used for UDP delays (Three calls for
"#(delay0,delay1,delay2)"), as the parser does not know if the
instantiation is for an UDP versus a module.

=item $self->pin ( $name, $connection, $index )

This method is called when a pin on a instant is defined.  If a pin name
was not provided and the connection is by position, name will be '' or
undef.

=item $self->port ( $name )

This method is called when a module port is defined.

=item $self->ppdefine ( $defvar, $definition )

This method is called when a preprocessor definition is encountered.

=item $self->signal_decl ( $keyword, $signame, $vector, $mem, $signed, $value )

This method is called when a signal or variable is declared.  The first
argument, $keyword is a direction ('input', 'output', 'inout'), or a type
('reg', 'trireg', 'integer', 'parameter'), the second argument is the name
of the signal.  The third argument is the vector bits or "".  The fourth
argument is the memory bits or "".  The fifth argument is "signed" if it is
signed.  The sixth argument is the value it is assigned to for "parameter"
or "wire".

Note this may be called twice for signals that are declared with both a
direction and a type.  (IE 'output reg' results in a call with 'output' and
a call with 'reg'.)

=item $self->task ( $keyword, $name )

This method is called when a module is defined.

=back

=head1 BUGS

This is being distributed as a baseline for future contributions.  Don't
expect a lot, the Parser is still naive, and there are many awkward cases
that aren't covered.

Note the SigParser is focused on extracting signal information.  It does
NOT extract enough information to derive general interconnect; for example
the contents of 'assign' statements are not parsed.

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2009 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Parser>,
L<Verilog::Language>,
L<Verilog::Netlist>,
L<Verilog::Getopt>

=cut
