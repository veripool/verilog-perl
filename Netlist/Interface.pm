# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Interface;

use Verilog::Netlist;
use Verilog::Netlist::ModPort;
use Verilog::Netlist::Net;
use Verilog::Netlist::Pin;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Interface::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.458';

structs('new',
	'Verilog::Netlist::Interface::Struct'
	=>[name     	=> '$', #'	# Name of the module
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   netlist	=> '$', #'	# Netlist is a member of
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   comment	=> '$', #'	# Comment provided by user
	   _cells	=> '%',		# hash of Verilog::Netlist::Cells
	   _modports    => '%',		# hash of Verilog::Netlist::ModPorts
	   _ports	=> '%',		# hash of Verilog::Netlist::Ports
	   _portsordered=> '@',		# list of Verilog::Netlist::Ports as ordered in list of ports
	   _nets	=> '%',		# hash of Verilog::Netlist::Nets
	   _level	=> '$',		# Depth in hierarchy (if calculated)
	   ]);

sub delete {
    my $self = shift;
    foreach my $oref ($self->nets) {
	$oref->delete;
    }
    foreach my $oref ($self->ports) {
	$oref->delete;
    }
    foreach my $oref ($self->modports) {
	$oref->delete;
    }
    foreach my $oref ($self->cells) {
	$oref->delete;
    }
    my $h = $self->netlist->{_interfaces};
    delete $h->{$self->name};
    return undef;
}

######################################################################

sub is_top {}  # Ignored, for module compatibility

sub keyword { return 'interface'; }

sub logger {
    return $_[0]->netlist->logger;
}

sub find_modport {
    my $self = shift;
    my $search = shift;
    return $self->_modports->{$search} || $self->_modports->{"\\".$search." "};
}
sub find_port {
    my $self = shift;
    my $search = shift;
    return $self->_ports->{$search} || $self->_ports->{"\\".$search." "};
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
    return $self->_cells->{$search} || $self->_cells->{"\\".$search." "};
}
sub find_net {
    my $self = shift;
    my $search = shift;
    my $rtn = $self->_nets->{$search}||"";
    #print "FINDNET ",$self->name, " SS $search  $rtn\n";
    return $self->_nets->{$search} || $self->_nets->{"\\".$search." "};
}

sub attrs_sorted {
    return (sort {$a cmp $b} @{$_[0]->attrs});
}
sub cells {
    return (values %{$_[0]->_cells});
}
sub cells_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_cells}));
}
sub modports {
    return (values %{$_[0]->_modports});
}
sub modports_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_modports}));
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
    my $self = shift;
    return map {$self->_ports->{$_}} @{$self->_portsordered};
}

sub nets_and_ports_sorted {
    return Verilog::Netlist::Module::nets_and_ports_sorted(@_);
}

sub new_net {
    my $self = shift;
    # @_ params
    # Create a new net under this
    my $netref = new Verilog::Netlist::Net(direction=>'net', data_type=>'wire',
					   @_,
					   module=>$self, );
    $self->_nets($netref->name(), $netref);
    return $netref;
}

sub new_attr {
    my $self = shift;
    my $clean_text = shift;
    push @{$self->attrs}, $clean_text;
}

sub new_modport {
    my $self = shift;
    # @_ params
    my $oref = new Verilog::Netlist::ModPort(@_, module=>$self,);
    $self->_modports($oref->name(), $oref);
    return $oref;
}

sub new_port {
    my $self = shift;
    # @_ params
    # Create a new port under this module
    my $portref = new Verilog::Netlist::Port(@_, module=>$self,);
    $self->_ports($portref->name(), $portref);
    return $portref;
}

sub new_cell {
    return Verilog::Netlist::Module::new_cell(@_);
}

sub level {
    my $self = shift;
    my $level = $self->_level;
    return $level if defined $level;
    $self->_level(2);  # Interfaces are never up "top"
    foreach my $cell ($self->cells) {
	if ($cell->submod) {
	    my $celllevel = $cell->submod->level;
	    $self->_level($celllevel+1) if $celllevel >= $self->_level;
	}
    }
    return $self->_level;
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
    foreach my $oref ($self->modports) {
	$oref->_link();
    }
    foreach my $cellref ($self->cells) {
	$cellref->_link();
    }
}

sub lint {
    my $self = shift;
    if ($self->netlist->{use_vars}) {
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
    my @out = "interface ".$self->name." (\n";
    my $indent = "   ";
    # Port list
    my $comma="";
    push @out, $indent;
    foreach my $portref ($self->ports_sorted) {
	push @out, $comma, $portref->verilog_text;
	$comma = ", ";
    }
    push @out, ");\n";

    foreach my $netref ($self->nets_sorted) {
	push @out, $indent, $netref->verilog_text, "\n";
    }
    foreach my $oref ($self->modports_sorted) {
	push @out, $indent, $oref->verilog_text, "\n";
    }
    foreach my $cellref ($self->cells_sorted) {
	push @out, $indent, $cellref->verilog_text, "\n";
    }

    push @out, "endinterface\n";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"Interface:",$self->name(),"  File:",$self->filename(),"\n";
    if (!$norecurse) {
	foreach my $portref ($self->ports_sorted) {
	    $portref->dump($indent+2);
	}
	foreach my $netref ($self->nets_sorted) {
	    $netref->dump($indent+2);
	}
	foreach my $oref ($self->modports_sorted) {
	    $oref->dump($indent+2);
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

Verilog::Netlist::Interface - Interface within a Verilog Netlist

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $interface = $netlist->find_interface('name');
  my $cell = $self->find_cell('name')
  my $port =  $self->find_port('name')
  my $net =  $self->find_net('name')

=head1 DESCRIPTION

A Verilog::Netlist::Interface object is created by Verilog::Netlist for
every interface in the design.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->find_port_by_index

Returns the port name associated with the given index.

=item $self->modports

Returns list of references to Verilog::Netlist::ModPort in the interface.

=item $self->modports_sorted

Returns list of references to Verilog::Netlist::ModPort in the interface
sorted by name.

=item $self->name

The name of the interface.

=item $self->netlist

Reference to the Verilog::Netlist the interface is under.

=item $self->nets

Returns list of references to Verilog::Netlist::Net in the interface.

=item $self->nets_sorted

Returns list of name sorted references to Verilog::Netlist::Net in the
interface.

=item $self->nets_and_ports_sorted

Returns list of name sorted references to Verilog::Netlist::Net and
Verilog::Netlist::Port in the interface.

=item $self->ports

Returns list of references to Verilog::Netlist::Port in the interface.

=item $self->ports_ordered

Returns list of references to Verilog::Netlist::Port in the interface
sorted by pin number.

=item $self->ports_sorted

Returns list of references to Verilog::Netlist::Port in the interface
sorted by name.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->find_net(I<name>)

Returns Verilog::Netlist::Net matching given name.

=item $self->level

Returns the reverse depth of this interface with respect to other modules
and interfaces.  See also Netlist's modules_sorted_level.

=item $self->lint

Checks the interface for errors.

=item $self->link

Creates interconnections between this interface and other interfaces.

=item $self->new_net

Creates a new Verilog::Netlist::Net.

=item $self->dump

Prints debugging information for this interface.

=item $self->verilog_text

Returns verilog code which represents this interface.  Returned as an array
that must be joined together to form the final text string.  The netlist
must be already ->link'ed for this to work correctly.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2019 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
