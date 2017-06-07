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

$VERSION = '3.427';

our @_Callback_Names = qw(
  attribute
  class
  contassign
  covergroup
  defparam
  endcell
  endclass
  endgroup
  endinterface
  endmodport
  endmodule
  endpackage
  endprogram
  endtaskfunc
  function
  import
  instant
  interface
  modport
  module
  package
  parampin
  pin
  port
  program
  task
  var
  );

#######################################################################

# parse, parse_file, etc are inherited from Verilog::Parser
sub new {
    my $class = shift;

    my $self = $class->SUPER::new(_sigparser => 1,
				  use_unreadback => 0,
				  use_protected => 0,
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
# Accessors

sub callback_names {
    my @out = sort @_Callback_Names;
    return @out;
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

sub contassign {
    my $self = shift;
    my $lhs = shift;
    my $rhs = shift;
}

sub class {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $virtual = shift;
}

sub covergroup {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
}

sub defparam {
    my $self = shift;
    my $lhs = shift;
    my $rhs = shift;
}

sub endclass {
    my $self = shift;
}

sub endcell {
    my $self = shift;
}

sub endgroup {
    my $self = shift;
}

sub endinterface {
    my $self = shift;
}

sub endmodport {
    my $self = shift;
}

sub endtaskfunc {
    my $self = shift;
}

sub endmodule {
    my $self = shift;
}

sub endpackage {
    my $self = shift;
}

sub endprogram {
    my $self = shift;
}

sub function {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $data_type = shift;
}

sub import {
    my $self = shift;
    my $module = shift;
    my $name = shift;
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

sub modport {
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

sub package {
    my $self = shift;
    my $kwd = shift;
    my $name = shift;
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
    my $objof = shift;
    my $direction = shift;
    my $data_type = shift;
    my $array = shift;
    my $pinnum = shift;
}

sub ppdefine {
    my $self = shift;
    my $defvar = shift;
    my $definition = shift;
}

sub program {
    my $self = shift;
    my $kwd = shift;
    my $name = shift;
}

sub task {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
}

sub var {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $objof = shift;
    my $net_type = shift;
    my $data_type = shift;
    my $array = shift;
    my $value = shift;
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
appropriate.

Note Verilog::Parser callbacks also are invoked when SigParser is parsing.

=over 4

=item $self->attribute ( $text )

Scanned an attribute or meta-comment.  The parser inspects the first word
of each comment line (C<//key rest> to end of line) or comment block
(C</*key rest */).  It calls C<$self->attribute( meta_text )>
if the first word has a true value in hash C<$self->metacomment>.

=item $self->class ( $token, $name, $virtual )

This method is called at a class.

=item $self->covergroup ( $token, $name )

This method is called at a covergroup.

=item $self->contassign ( $token, $lhs, $rhs )

This method is called at a continuous "assign" keyword, with the left and
right hand part of the assignment.  Note that "wire" initializations are
not considered assignments; those are received via the var callback's value
parameter.

=item $self->defparam ( $token, $lhs, $rhs )

This method is called at a "defparam" keyword, with the left and right hand
part of the assignment.

=item $self->endcell ( $token )

This method is called at the end of defining a cell. It is useful for
writing clean up routines.

=item $self->endgroup ( $token )

This method is called at the end of defining a covergroup. It is useful for
writing clean up routines.

=item $self->endinterface ( $token )

This method is called at a endinterface keyword. It is useful for writing
clean up routines.

=item $self->endclass ( $token )

This method is called at a endclass keyword.  It is useful for writing
clean up routines.

=item $self->endtaskfunc ( $token )

This method is called at a endfunction or endtask keyword.  It is useful
for writing clean up routines.

=item $self->endmodport ( $token )

This method is called at a endmodport keyword. It is useful for writing
clean up routines.

=item $self->endmodule ( $token )

This method is called at a endmodule keyword. It is useful for writing
clean up routines.

=item $self->endpackage ( $token )

This method is called at a endpackage keyword. It is useful for writing
clean up routines.

=item $self->endprogram ( $token )

This method is called at a endprogram keyword. It is useful for writing
clean up routines.

=item $self->function ( $keyword, $name, $data-type )

This method is called when a function is defined.  Type is the output size
or typename, plus "signed", for example "", "[3:0]", "integer", or "signed
[2:0]".

=item $self->import ( $package, $id )

This method is called when an import is defined.

=item $self->instant ( $module, $cell, $range )

This method is called when a instantiation is defined.  The first parameter
is the name of the module being instantiated. The second parameter is the
name of the cell, which may be "" for primitives.  The third is the range
if the cell was arrayed.

Prior to version 3.000, the name of the parameters were also included in
this callback. This has been replaced with the parampin callback.

=item $self->interface ( $keyword, $name )

This method is called when an interface is defined.

=item $self->modport ( $keyword, $name )

This method is called when an interface modport is defined.

=item $self->module ( $keyword, $name, ignored, $in_celldefine )

This method is called when a module is defined.

=item $self->package ( $keyword, $name )

This method is called when a package is defined.

=item $self->parampin ( $name, $connection, $index )

This method is called when a parameter is connected to an instantiation, IE
the "#(...)" syntax.  It is also used for UDP delays (Three calls for
"#(delay0,delay1,delay2)"), as the parser does not know if the
instantiation is for an UDP versus a module.

=item $self->pin ( $name, $connection, $index )

This method is called when a pin on a instant is defined.  If a pin name
was not provided and the connection is by position, name will be '' or
undef.

If you do not need the pin nor var nor port callbacks, consider the
"$self->new (... use_vars=>0 ...)"  option to accelerate parsing.

=item $self->port ( $name, $objof, $direction, $data_type, $array, $pinnum )

This method is called when a module port is defined.  It may be called
twice on a port if the 1995 style is used; the first call is made at the
port header, the second call at the input/output declaration.

The first argument $name, is the name of the port.  $objof is what the port
is an object of ('module', 'function', etc).  $direction is the port
direction ('input', 'output', 'inout', 'ref', 'const ref', or 'interface').
$data_type is the data type ('reg', 'user_type_t', 'signed [31:0]', etc, or
for interfaces the "{interface_id}.{modport_name}").  $array is the
arraying of the port ('[1:0][2:0]', '', etc).  $pinnum is set to the pin
number for ANSI style declarations, and 0 for Verilog 1995 declarations
made outside the port list.

If you do not need the pin nor var nor port callbacks, consider the
"$self->new (... use_vars=>0 ...)"  option to accelerate parsing.

=item $self->ppdefine ( $defvar, $definition )

This method is called when a preprocessor definition is encountered.

=item $self->program ( $keyword, $name )

This method is called when a program is defined.

=item $self->signal_decl ( $keyword, $signame, $vector, $mem, $signed, $value )

This method is no longer used, see $self->var.

=item $self->task ( $keyword, $name )

This method is called when a task is defined.

=item $self->var ( $kwd, $name, $objof, $nettype, $data_type, $array, $value )

This method is called when a variable or net is defined.

The first argument $kwd is how it was declared ('port', 'var', 'genvar',
'parameter', 'localparam', 'typedef') or if applicable a net type
('supply0', 'wire', etc). $name is the name of the variable.  $objof is
what the variable is an object of ('module', 'function', etc).  $nettype is
the net type if any was defined ('', 'supply0', 'wire', 'tri', etc).
$data_type is the data type ('user_type_t', '[31:0] signed', etc).  $array
is the arraying of the variable which is the text AFTER the variable name
('[1:0][2:0]', '', etc).  $value is what the variable was assigned to ('',
or expression).

Note typedefs are included here, because "parameter type" is both a
variable and a type declaration.

If you do not need the pin nor var nor port callbacks, consider the
"$self->new (... use_vars=>0 ...)"  option to accelerate parsing.

Below are some example declarations and the callbacks:

   reg [4:0]  vect = 5'b10100;
   # VAR  'var' 'vect' 'module' '' 'reg [4:0]' '' '5'b10100'
   wire (weak0, weak1) value = pullval;
   # VAR  'net' 'value' 'module' 'wire' '' '' 'pullval'
   reg [1:0] mem [12:2];
   # VAR  'var' 'mem' 'module' '' 'reg [1:0]' '[12:2]' ''
   int n[1:2][1:3] = '{'{0,1,2}, '{3{4}}};
   # verilog/parser_sv.v:121: VAR  'var' 'n' 'module' '' 'int' '[1:2][1:3]' ''{'{0,1,2},'{3}}'
   module ( output logic [SZ-1:0] o_sized );
   # VAR  'port' 'o_sized' 'module' '' 'logic [SZ-1:0]' '' ''
   struct packed signed { bit [7:0] m_b; };
   # VAR  'member' 'm_b' 'struct' '' 'bit [7:0]' '' ''

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

Copyright 2000-2017 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Parser>,
L<Verilog::Language>,
L<Verilog::Netlist>,
L<Verilog::Getopt>

=cut
