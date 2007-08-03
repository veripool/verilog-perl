# Verilog - Verilog Perl Interface
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
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
$VERSION = '3.011';
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

sub netlist { return $_[0]->module->netlist; }

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

A Verilog::Netlist::Port object is created by Verilog::Netlist::Module for
every port connection in the module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->array

Any array declaration for the port.  This only applies to Verilog 1995
style ports which can declare port bits independently from the signal
declarations.  When using Verilog 2001 style ports, see the matching net
declaration's lsb and msb methods instead, for example
C<$module->find_net($port->name)->msb>.

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

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

Verilog-Perl is part of the L<http://www.veripool.com/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2007 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
