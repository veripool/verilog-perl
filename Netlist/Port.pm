# Verilog - Verilog Perl Interface
# $Revision: 1.35 $$Date$$Author$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2005 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::Port;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::Port::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.316';
use strict;

structs('new',
	'Verilog::Netlist::Port::Struct'
	=>[name     	=> '$', #'	# Name of the port
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   direction	=> '$', #'	# Direction (in/out/inout)
	   type	 	=> '$', #'	# C++ Type (bool/int)
	   comment	=> '$', #'	# Comment provided by user
	   array	=> '$', #'	# Vectorization
	   module	=> '$', #'	# Module entity belongs to
	   # below only after links()
	   net		=> '$', #'	# Net port connects
	   # below only after autos()
	   sp_autocreated	=> '$', #'	# Created by /*AUTOINOUT*/
	   ]);

sub _link {
    my $self = shift;
    if (!$self->net) {
	my $net = $self->module->find_net ($self->name);
	if (!$net) {
	    $net = $self->module->new_net
		(name=>$self->name,
		 filename=>$self->filename, lineno=>$self->lineno,
		 type=>$self->type, array=>$self->array,
		 comment=>undef,
		 );
	    $net->attributes($self->attributes);  # Copy attributes across
	}
	if ($net && $net->port && $net->port != $self) {
	    $self->error ("Port redeclares existing port: ",$self->name,"\n");
	}
	$self->net($net);
	$self->net->port($self);
	# A input to the module is actually a "source" or thus "out" of the net.
	$self->net->_used_in_inc()    if ($self->direction() eq 'out');
	$self->net->_used_out_inc()   if ($self->direction() eq 'in');
	$self->net->_used_inout_inc() if ($self->direction() eq 'inout');
    }
}
sub lint {}

sub verilog_text {
    my $self = shift;
    return $self->name;
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Port:",$self->name(),"  Dir:",$self->direction()
	,"  Type:",$self->type(),"  Array:",$self->array()||"","\n";
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Port - Port for a Verilog Module

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $port = $module->find_port ('pinname');
  print $port->name;

=head1 DESCRIPTION

Verilog::Netlist creates a port for every connection to the outside
world in the current module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->array

Any array declaration for the port.

=item $self->comment

Any comment the user placed on the same line as the port.

=item $self->direction

The direction of the port: "in", "out", or "inout".

=item $self->module

Reference to the Verilog::Netlist::Module the port is in.

=item $self->name

The name of the port.

=item $self->net

Reference to the Verilog::Netlist::Net the port connects to.  Only valid
after the netlist is linked.

=item $self->type

The C++ type of the port.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->dump

Prints debugging information for this port.

=back

=head1 DISTRIBUTION

The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2005 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
