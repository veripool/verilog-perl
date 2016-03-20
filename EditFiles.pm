# See copyright, etc in below POD section.
######################################################################

package Verilog::EditFiles;
use Config;
use IO::File;
use File::Path;
use Carp;
use strict;

use vars qw ($VERSION $Debug);

######################################################################
#### Configuration Section

$VERSION = '3.419';

#######################################################################
# CONSTRUCTORS

sub new {
    my $class = shift;
    my $self = {
	# Options
	program => "Verilog::EditFiles",
	outdir => ".",
	translate_synthesis => 0,	# Name of define or "1"
	lint_header => undef,
	celldefine => undef,
	timescale_header => undef,
	timescale_removal => undef,
	lint_command => 'vlint --brief',
	v_suffix => ".v",
	verbose => 1,
	# Internals
	_files => {},   # Hash of module name, contains list of lines
	@_,
    };
    $self->{verbose} = 1 if $Debug;
    $self->{debug} = 1 if $Debug;
    bless $self, $class;
    return $self;
}

######################################################################

sub read_and_split {
    my $self = shift;
    foreach my $filename (@_) {
	$self->_read_split_file($filename);
    }
}

sub _read_split_file {
    my $self = shift;
    my $filename = shift;

    print "Reading $filename...\n" if $self->{verbose};
    my $fh = IO::File->new("<$filename") or die "%Error: $! $filename\n";
    (my $basename = $filename) =~ s!^.*/!!;
    (my $basemod = $basename) =~ s!\.(v|inc)$!!;

    my @header = "// Created by $self->{program} from $basename\n";
    my @trailer = "\n";

    my @lines = (@header);
    my $modname;
    my $ever_module;
    my $commented;
    while (defined(my $line = $fh->getline)) {
	$line =~ s!\r!!mg;
	$line =~ s![ \t]+\n$!\n!;
	if ($self->{translate_synthesis}) {
	    my $define = $self->{translate_synthesis};
	    $define = "SYNTHESIS" if $define eq "1";
	    $line =~ s!^\s*//\s*(ambit|synopsys|synthesis)\s*translate_off\s*$!`ifndef ${define}\n!;
	    $line =~ s!^\s*//\s*(ambit|synopsys|synthesis)\s*translate_on\s*$!`endif //${define}\n!;
	    if ($line =~ m!(ambit|synopsys|synthesis)\s*translate!) {
		die "%Error: Unhandled translate comment: $line\n";
	    }
	}

	while ($line =~ m!.*?(/\*|//|\*/)!g) {
	    if (!$commented && $1 eq '//') {
		last;
	    } elsif (!$commented && $1 eq '/*') {
		$commented = 1;
	    } elsif ($commented && $1 eq '*/') {
		$commented = 0;
	    }
	}

	if (!$commented
	    && $line =~ /^\s*(module|primitive)\s+([A-Za-z0-9_]+)/) {
	    my $newmodname = $2;
	    if ($modname) { # Already in a module
		# Support code like this
		# `ifdef x
		#   module x (...)
		# `else
		#   module x (...)
		($newmodname eq $modname)
		    or die "%Error: $filename:$.: module without previous endmodule\n";
		print "$basename:$.:  continue module $1\n" if $self->{debug};
	    } else {
		$modname = $newmodname;
		$ever_module = 1;
		print "$basename:$.:  module $1\n" if $self->{debug};
		my @afterif;
		my @oldlines = (@lines);
		@lines = (@header);
		# Insert our new header before any `ifdef's or `includes
		my $gotifdef;
		foreach my $oline (@oldlines) {
		    $gotifdef = 1 if $oline =~ /`ifdef\b|`include\b/;
		    if (!$gotifdef) {
			push @lines, $oline;
		    } else{
			push @afterif, $oline;
		    }
		}
		push @lines, $self->{include_header} if $self->{include_header};
		push @lines, $self->{timescale_header} if $self->{timescale_header};
		push @lines, "`celldefine\n" if $self->{celldefine};
		push @lines, $self->{lint_header} if $self->{lint_header};
		push @lines, @afterif;
	    }
	    push @lines, $line;
	}
	elsif (!$commented && $line =~ /^\s*end(module|primitive)\b/) {
	    print "$basename:$.:  endmodule $modname\n" if $self->{debug};
	    $modname or die "%Error: $filename:$.: endmodule without previous module\n";
	    push @lines, $line;
	    push @lines, "`endcelldefine\n" if $self->{celldefine};
	    push @lines, @trailer;
	    $self->{_files}{$modname}{created} = 1;
	    $self->{_files}{$modname}{modname} = $modname;
	    $self->{_files}{$modname}{lines} = [@lines];
	    @lines = ();
	    # Prep for next
	    $modname = undef;
	}
	elsif (!$commented
	    && $line =~ /^\s*\`timescale\s.*/
	    && $self->{timescale_removal}) {
	    # Strip existing timescale
	}
	elsif (!$commented
	       && $line =~ /^\s*\`(end)?celldefine\b/
	       && $self->{celldefine}) {
	    # Strip existing celldefine, we'll add a new one
	}
	else {
	    push @lines, $line;
	}
    }
    $fh->close;

    if (!$ever_module) {
	print "$basename:1: No module, must be include file: $basemod\n" if $self->{debug};
	push @lines, @trailer;
	$self->{_files}{$basemod}{created} = 1;
	$self->{_files}{$basemod}{modname} = $basemod;
	$self->{_files}{$basemod}{lines} = [@lines];
	$self->{_files}{$basemod}{is_include} = 1;
    }
}

#######################################################################

sub write_files {
    my $self = shift;

    mkpath($self->{outdir});
    foreach my $file (sort (keys %{$self->{_files}})) {
	my $fileref = $self->{_files}{$file};
	next if !$fileref->{created};
	$self->_write_file ($self->{outdir}."/".$fileref->{modname}.$self->{v_suffix}, $fileref);
    }
}

sub _write_file {
    my $self = shift;
    my $filename = shift;
    my $fileref = shift;

    print "Writing $filename...\n" if $self->{verbose};

    my $fh = IO::File->new(">$filename") or die "%Error: $! $filename\n";
    foreach my $line (@{$fileref->{lines}}) {
	print $fh $line;
    }
    $fh->close;
}

sub write_lint {
    my $self = shift;
    my %params = (filename => $self->{outdir}."/0LINT.sh",
		  @_);

    print "Writing $params{filename}...\n" if $self->{verbose};

    my $fh = IO::File->new(">$params{filename}") or die "%Error: $! $params{filename}\n";
    print $fh "#!/bin/bash\n";
    print $fh "# Created by $self->{program}\n";
    foreach my $fileref (sort {$a->{modname} cmp $b->{modname}} values %{$self->{_files}}) {
	next if $fileref->{is_include};
	next if $fileref->{skip_lint};
	print $fh "echo \"".("*"x70),"\"\n";
	print $fh "echo Lint ".$fileref->{modname},"\n";
	print $fh $self->{lint_command}." \$* ".$fileref->{modname}.$self->{v_suffix},"\n";
    }
    $fh->close;

    chmod 0777, $params{filename};
}

#######################################################################

sub edit_file {
    my $self = shift;
    my %params = (filename => undef,
		  write_filename => undef,
		  cb => sub {},
		  verbose => $self->{verbose},
		  @_);
    defined $params{filename} or croak "%Error: edit_file not passed filename=>,";
    ref $params{cb} or croak "%Error: edit_file cb=> callback is not code,";
    $params{write_filename} = $params{filename} if !defined $params{write_filename};

    my $wholefile;
    my $origwholefile;
    {	# Read it
	my $fh = IO::File->new ("<$params{filename}")
	    or croak "%Error: $! $params{filename},";
	local $/; undef $/;
	$wholefile = <$fh>;
	$origwholefile = $wholefile;
	$fh->close();
    }

    # Edit
    $wholefile = &{$params{cb}}($wholefile);

    # Writeback
    if ($wholefile ne $origwholefile) {
	print "  $params{write_filename} (Changed)\n" if $params{verbose};
	my ($dev,$ino,$mode) = stat($params{write_filename});
	chmod 0777, $params{filename};

	my $fh = IO::File->new (">$params{write_filename}")
	    or croak "%Error: $! writing $params{write_filename},";
	print $fh $wholefile;
	$fh->close();
	chmod $mode, $params{write_filename} if $mode;  # Preserve mode
    }
}


#######################################################################
1;
__END__

=pod

=head1 NAME

Verilog::EditFiles - Split Verilog modules into separate files.

=head1 SYNOPSIS

See splitmodule command.

   use Verilog::EditFiles;
   my $split = Verilog::EditFiles->new
       (outdir => "processed_rtl",
	translate_synthesis => 0,
	lint_header => undef,
	celldefine => 1,
	);
   $split->read_and_split(glob("inbound_rtl/*.v"));
   $split->write_files();
   $split->edit_file(filename=>"foo", cb => sub { return $_[0]; });

=head1 DESCRIPTION

Verilog::EditFiles provides a easy way to split library Verilog files that
contain multiple modules into many files with one module per file.

=head1 FUNCTIONS

=over 4

=item new (...)

Create a new Verilog::EditFiles object.  Named parameters may be specified:

=over 4

=item celldefine

If true, add "`celldefine" before every module statement.

=item lint_command

For the write_lint method, the name of the linter to use.  Defaults to
"vlint --brief".

=item lint_header

If defined, add the provided text before every module statement.  Generally
used to insert lint off pragmas.

=item outdir

Name of the directory to write the output modules to.  Defaults to ".".

=item program

Name of the program to add to comments.  Defaults to
"Verilog::EditFiles".

=item timescale_header

If defined, add the provided text before every module statement.  Generally
set to the next needed to #include a timescale file.  Use with
timescale_removal.

=item timescale_removal

If set, remove any `timescales.

=item translate_synthesis

If 1, replace any synopsys translate on/offs with "`ifdef SYNTHESIS" and
"`endif"s.  If set to a string, use that string instead of "SYNTHESIS".

=item v_suffix

The suffix to add to convert a module name into a filename.  Defaults to
".v".

=item verbose

If true, print what files are being read and written.

=back

=item $self->read_and_split ([filenames])

Read from the specified filenames.

If there is no module statement in the file, assume it is a include file,
and when write_files is called, place all of the file contents into the
output.  If there is a module statement, when write_files is called place
all following output into a file named based on the module, with .v added.

=item $self->write_files()

Write all of the files created by read_and_split to the outdir.

=item $self->write_lint([filename=>...])

Create a shell script that will lint every file created by write_files.  If
a "filename" parameter is not provided, "0LINT.sh" will be written in the
default outdir.

=item $self->edit_file(filename=>..., cb=>sub{...})

Read a file, edit it with the provided callback, and save it if it has
changed.  The "filename" parameter is the filename to read.  The
"write_filename" parameter is the filename to write, defaulting to the same
name as the filename to read.  The "cb" parameter is a reference to a
callback which takes the string of file contents and returns the string to
write back.  Often the callback will simply perform a search and replace.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2006-2016 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>

=cut

######################################################################
