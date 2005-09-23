# Verilog - Verilog Perl Interface
# $Id$
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

package Verilog::Netlist::Pin;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Port;
use Verilog::Netlist::Net;
use Verilog::Netlist::Cell;
use Verilog::Netlist::Module;
use Verilog::Netlist::Pin;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::Pin::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.330';
use strict;

structs('new',
	'Verilog::Netlist::Pin::Struct'
	=>[name     	=> '$', #'	# Pin connection
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   netname	=> '$', #'	# Net connection
	   portname 	=> '$', #'	# Port connection name
	   portnumber   => '$', #'	# Position of name in call
	   pinnamed 	=> '$', #'	# True if name assigned
	   cell     	=> '$', #'	# Cell reference
	   # below only after link()
	   net		=> '$', #'	# Net connection reference
	   port		=> '$', #'	# Port connection reference
	   # SystemPerl: below only after autos()
	   sp_autocreated => '$', #'	# Created by auto()
	   # below by accessor computation
	   #module
	   #submod
	   ]);

sub delete {
    my $self = shift;
    my $h = $self->cell->_pins;
    delete $h->{$self->name};
    return undef;
}

######################################################################
#### Methods

sub module {
    return $_[0]->cell->module;
}
sub submod {
    return $_[0]->cell->submod;
}
sub netlist {
    return $_[0]->cell->module->netlist;
}

sub _link {
    my $self = shift;
    my $change;
    if (!$self->net
	&& $self->netname) {
	$self->net($self->module->find_net($self->netname));
	$change = 1;
    }
    if (!$self->port
	&& $self->portname && $self->submod && !$self->cell->byorder ) {
	$self->port($self->submod->find_port($self->portname));
	$change = 1;
    }
    elsif (!$self->port
	&& $self->submod) {
	$self->port($self->submod->find_port_by_index($self->portnumber));
	# changing name from pin# to actual port name
	$self->name($self->port->name()) if $self->port;
	$change = 1;
    }
    if ($change && $self->net && $self->port) {
	$self->net->_used_in_inc()    if ($self->port->direction() eq 'in');
	$self->net->_used_out_inc()   if ($self->port->direction() eq 'out');
	$self->net->_used_inout_inc() if ($self->port->direction() eq 'inout');
    }
}

sub type_match {
    my $self = shift;
    return $self->net->type eq $self->port->type;
}

sub lint {
    my $self = shift;
    if (!$self->net && !$self->netlist->{implicit_wires_ok}) {
        $self->error ("Pin's net declaration not found: ",$self->netname,"\n");
    }
    if (!$self->port && $self->submod) {
        $self->error ($self,"Port not found in module ",$self->submod->name,": ",$self->portname,"\n");
    }
    if ($self->port && $self->net) {
	my $nettype = $self->net->type;
	my $porttype = $self->port->type;
	if (!$self->type_match) {
	    $self->error("Port pin type $porttype != Net type $nettype: "
			 ,$self->name,"\n");
	}
	my $netdir = "net";
	$netdir = $self->net->port->direction if $self->net->port;
	my $portdir = $self->port->direction;
	if (($netdir eq "in" && $portdir eq "out")
	    #Legal: ($netdir eq "in" && $portdir eq "inout")
	    #Legal: ($netdir eq "out" && $portdir eq "inout")
	    ) {
	    $self->error("Port is ${portdir}put from submodule, but ${netdir}put from this module: "
			 ,$self->name,"\n");
	    #$self->cell->module->netlist->dump;
	}
    }
}

sub verilog_text {
    my $self = shift;
    if ($self->port) {  # Even if it was by position, after linking we can write it as if it's by name.
	return ".".$self->port->name."(".$self->netname.")";
    } elsif ($self->pinnamed) {
	return ".".$self->name."(".$self->netname.")";
    } else { # not by name, and unlinked
	return $self->netname;
    }
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Pin:",$self->name(),"  Net:",$self->netname(),"\n";
    if ($self->port) {
	$self->port->dump($indent+10, 'norecurse');
    }
    if ($self->net) {
	$self->net->dump($indent+10, 'norecurse');
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Pin - Pin on a Verilog Cell

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $pin = $cell->find_pin ('pinname');
  print $pin->name;

=head1 DESCRIPTION

Verilog::Netlist creates a pin for every pin connection on a cell.  A Pin
connects a net in the current design to a port on the instantiated cell's
module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->cell

Reference to the Verilog::Netlist::Cell the pin is under.

=item $self->delete

Delete the pin from the cell it's under.

=item $self->module

Reference to the Verilog::Netlist::Module the pin is in.

=item $self->name

The name of the pin.  May have extra characters to make vectors connect,
generally portname is a more readable version.  There may be multiple pins
with the same portname, only one pin has a given name.

=item $self->net

Reference to the Verilog::Netlist::Net the pin connects to.  Only valid after a link.

=item $self->netlist

Reference to the Verilog::Netlist the pin is in.

=item $self->netname

The net name the pin connects to.

=item $self->portname

The name of the port connected to.

=item $self->port

Reference to the Verilog::Netlist::Port the pin connects to.  Only valid after a link.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->lint

Checks the pin for errors.  Normally called by Verilog::Netlist::lint.

=item $self->dump

Prints debugging information for this pin.

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
