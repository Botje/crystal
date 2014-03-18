#!/usr/bin/perl
use strict;
use warnings;

use Data::Dumper;
use Text::Table;
use File::Slurp;
use Getopt::Long;
use IPC::Run qw(run);

unless (@ARGV) {
	die "Usage: $0 filename [filename...]\n";
}

our $tex = 0;

GetOptions("tex" => \$tex);

my @smart = qw(./run.sh --stats);
my @dumb  = qw(./run.sh --no-mobility --dumb --stats);

sub crystal {
	my $cmd = shift,
	my ($out, $err, $ret);

	my $retval = run $cmd, \undef, \$out, \$err;
	unless ($retval) {
		warn "crystal failed: $err\n";
		return undef;
	}
	$out =~ s/.*--- STATS ---//s;

	while ($out =~ s,<([\w\s]+)>(.*)</\1>,,s) {
		my ($key, $text) = ($1, $2);
		$text =~ s/\s*\Q<![CDATA[//;
		$text =~ s/\Q]]>\E\s*//;
		$ret->{$key} = $text;
	}
	$ret
}

sub processMovedChecks {
	my $input = shift;

	my %vars = map {split /\t/} grep /\t/, split /\n/, $input;
	for my $k (keys %vars) {
		my @values = sort { $a <=> $b } split " ", $vars{$k};
		$vars{$k} = [$values[0], $values[$#values/2], $values[-1]];
	}
	
	my @sortedkeys = sort {$vars{$b}[1] <=> $vars{$a}[1]} keys %vars;

	my @ret;

	for my $k (@sortedkeys) {
		my $stats = join "/", @{ $vars{$k} };
		push @ret, "$k ($stats)";
	}

	splice @ret, 0, 5;
}

sub countLOC {
	my @lines = read_file(shift);
	s/;.*// for @lines;
	@lines = grep /\S/, @lines;
	scalar @lines;
}

our @columns = ("Filename", "LOC", "Dyn", "BP", "Remaining", "Top 5 comp. dist");

our @sepcolumns = map { ($_, $tex ? \' & ' : \' | ') } @columns;

$sepcolumns[-1] = \' \\\\' if $tex;

our $tt = Text::Table->new(@sepcolumns);

for my $filename (@ARGV) {
	print STDERR "Smart $filename...";
	my $smart = crystal [@smart, $filename];
	print STDERR ($smart ? "OK" : "NOT OK"), "\n";
	next unless defined $smart;
	print STDERR "Dumb $filename...";
	next unless defined $smart;
	my $dumb = crystal [@dumb, $filename];

	print STDERR "OK\n";

	my @reduced = (0+$dumb->{"Number of checks"}, 0+$smart->{"Number of checks"});
	push @reduced, $reduced[0] == 0 ? "N/A" : sprintf "%.2f\\%%", 100 * $reduced[1] / $reduced[0];
	# $reduced = 1.0 - ($smart->{"Number of checks"} / $dumb->{"Number of checks"});
	# $reduced *= 100;
	# $reduced = sprintf '%.0f \%%', $reduced;

	my $top5 = join ", ", processMovedChecks($smart->{"Mobility stats"});

	my ($base) = $filename =~ m!/([^/]+?)(\.\w+)?$!;

	$tt->load([ $base, countLOC($filename), @reduced, $top5 ]);
}

print $tt;
