# Verilog - Verilog Perl Interface
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::Module;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Port;
use Verilog::Netlist::Net;
use Verilog::Netlist::Cell;
use Verilog::Netlist::Pin;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::Module::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.341';
use strict;

structs('new',
	'Verilog::Netlist::Module::Struct'
	=>[name     	=> '$', #'	# Name of the module
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   netlist	=> '$', #'	# Netlist is a member of
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   attrs	=> '@',		# list of "category name[ =](.*)" strings
	   _ports	=> '%',		# hash of Verilog::Netlist::Ports
	   _portsordered=> '@',		# list of Verilog::Netlist::Ports as ordered in list of ports   
	   _nets	=> '%',		# hash of Verilog::Netlist::Nets
	   _cells	=> '%',		# hash of Verilog::Netlist::Cells
	   _celldecls	=> '%',		# hash of declared cells (for autocell only)
	   _cellarray	=> '%',		# hash of declared cell widths (for autocell only)
	   is_top	=> '$', #'	# Module is at top of hier (not a child)
	   is_libcell	=> '$', #'	# Module is a library cell
	   # SystemPerl:
	   _autocovers  => '%', #'	# Hash of covers found in code
	   _autosignal	=> '$', #'	# Module has /*AUTOSIGNAL*/ in it
	   _autosubcells=> '$', #'	# Module has /*AUTOSUBCELL_DECL*/ in it
	   _autotrace	=> '%', #'	# Module has /*AUTOTRACE*/ in it
	   _autoinoutmod=> '$', #'	# Module has /*AUTOINOUT_MODULE*/ in it
	   _pintemplates=> '@', #'	# Module SP_TEMPLATEs
	   _ctor	=> '$', #'	# Module has SC_CTOR in it
	   _code_symbols=> '$', #'	# Hash ref of symbols found in raw code
	   lesswarn     => '$',	#'	# True if some warnings should be disabled
	   ]);

sub modulename_from_filename {
    my $filename = shift;
    (my $module = $filename) =~ s/.*\///;
    $module =~ s/\.[a-z]+$//;
    return $module;
}

sub find_port {
    my $self = shift;
    my $search = shift;
    return $self->_ports->{$search};
}
sub find_port_by_index {
    my $self = shift;
    my $myindex = shift;
    # @{$self->_portsordered}[$myindex-1] returns the name of
    # the port in the module at this index.  Then, this is
    # used to find the port reference via the port hash
    return $self->_ports->{@{$self->_portsordered}[$myindex-1]}; 
}
sub find_cell {
    my $self = shift;
    my $search = shift;
    return $self->_cells->{$search};
}
sub find_net {
    my $self = shift;
    my $search = shift;
    my $rtn = $self->_nets->{$search}||"";
    #print "FINDNET ",$self->name, " SS $search  $rtn\n";
    return $self->_nets->{$search};
}

sub attrs_sorted {
    return (sort {$a cmp $b} @{$_[0]->attrs});
}
sub nets {
    return (values %{$_[0]->_nets});
}
sub nets_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_nets}));
}
sub ports {
    return (values %{$_[0]->_ports});
}
sub ports_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_ports}));
}
sub ports_ordered {
    return ( @{$_[0]->_portsordered});
}
sub cells {
    return (values %{$_[0]->_cells});
}
sub cells_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_cells}));
}
sub nets_and_ports_sorted {
    my $self = shift;
    my @list = ($self->nets, $self->ports,);
    my @outlist; my $last = "";
    # Eliminate duplicates
    foreach my $e (sort {$a->name() cmp $b->name()} (@list)) {
	next if $e eq $last;
	push @outlist, $e;
	$last = $e;
    }
    return (@outlist);
}

sub new_net {
    my $self = shift;
    # @_ params
    # Create a new net under this module
    my $netref = new Verilog::Netlist::Net (direction=>'net', @_, module=>$self, );
    $self->_nets ($netref->name(), $netref);
    return $netref;
}

sub new_attr {
    my $self = shift;
    my $clean_text = shift;
    push @{$self->attrs}, $clean_text;
}

sub new_port {
    my $self = shift;
    # @_ params
    # Create a new port under this module
    my $portref = new Verilog::Netlist::Port (@_, module=>$self,);
    $self->_ports ($portref->name(), $portref);
    return $portref;
}

sub new_cell {
    my $self = shift;
    # @_ params
    # Create a new cell under this module
    my $cellref = new Verilog::Netlist::Cell (@_, module=>$self,);
    $self->_cells ($cellref->name(), $cellref);
    return $cellref;
}

sub link {
    my $self = shift;
    # Ports create nets, so link ports before nets
    foreach my $portref ($self->ports) {
	$portref->_link();
    }
    foreach my $netref ($self->nets) {
	$netref->_link();
    }
    foreach my $cellref ($self->cells) {
	$cellref->_link();
    }
}

sub lint {
    my $self = shift;
    if (!$self->netlist->{skip_pin_interconnect}) {
	foreach my $portref ($self->ports) {
	    $portref->lint();
	}
	foreach my $netref ($self->nets) {
	    $netref->lint();
	}
    }
    foreach my $cellref ($self->cells) {
	$cellref->lint();
    }
}

sub verilog_text {
    my $self = shift;
    my @out = "module ".$self->name." (\n";
    my $indent = "   ";
    # Port list
    my $comma="";
    push @out, $indent;
    foreach my $portref ($self->ports_sorted) {
	push @out, $comma, $portref->verilog_text;
	$comma = ", ";
    }
    push @out, ");\n";

    # Signal list
    foreach my $netref ($self->nets_sorted) {
	push @out, $indent, $netref->verilog_text, "\n";
    }

    # Cell list
    foreach my $cellref ($self->cells_sorted) {
	push @out, $indent, $cellref->verilog_text, "\n";
    }
    push @out, "endmodule\n";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"Module:",$self->name(),"  File:",$self->filename(),"\n";
    if (!$norecurse) {
	foreach my $portref ($self->ports_sorted) {
	    $portref->dump($indent+2);
	}
	foreach my $netref ($self->nets_sorted) {
	    $netref->dump($indent+2);
	}
	foreach my $cellref ($self->cells_sorted) {
	    $cellref->dump($indent+2);
	}
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Module - Module within a Verilog Netlist

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $module = $netlist->find_module('modname');
  my $cell = $self->find_cell('name')
  my $port =  $self->find_port('name')
  my $net =  $self->find_net('name')

=head1 DESCRIPTION

Verilog::Netlist creates a module for every file in the design.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->cells

Returns list of references to Verilog::Netlist::Cell in the module.

=item $self->cells_sorted

Returns list of name sorted references to Verilog::Netlist::Cell in the module.

=item $self->find_port_by_index

Returns the port name associated with the given index.

=item $self->is_top

Returns true if the module has no cells referencing it (is at the top of the hierarchy.)

=item $self->name

The name of the module.

=item $self->netlist

Reference to the Verilog::Netlist the module is under.

=item $self->nets

Returns list of references to Verilog::Netlist::Net in the module.

=item $self->nets_sorted

Returns list of name sorted references to Verilog::Netlist::Net in the module.

=item $self->nets_and_ports_sorted

Returns list of name sorted references to Verilog::Netlist::Net and
Verilog::Netlist::Port in the module.

=item $self->ports

Returns list of references to Verilog::Netlist::Port in the module.

=item $self->ports_sorted

Returns list of name sorted references to Verilog::Netlist::Port in the module.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->autos

Updates the AUTOs for the module.

=item $self->find_cell(I<name>)

Returns Verilog::Netlist::Cell matching given name.

=item $self->find_port(I<name>)

Returns Verilog::Netlist::Port matching given name.

=item $self->find_net(I<name>)

Returns Verilog::Netlist::Net matching given name.

=item $self->lint

Checks the module for errors.

=item $self->link

Creates interconnections between this module and other modules.

=item $self->modulename_from_filename

Uses a rough algorithm (drop the extension) to convert a filename to the
module that is expected to be inside it.

=item $self->new_cell

Creates a new Verilog::Netlist::Cell.

=item $self->new_port

Creates a new Verilog::Netlist::Port.

=item $self->new_net

Creates a new Verilog::Netlist::Net.

=item $self->dump

Prints debugging information for this module.

=item $self->verilog_text

Returns verilog code which represents this module.  Returned as an array
that must be joined together to form the final text string.

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

L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
