#!/usr/bin/perl
use strict;
use warnings;

use Data::Dumper;

use IPC::Run qw(run);;

unless (@ARGV) {
	die "Usage: $0 filename [filename...]\n";
}

my @smart = qw(./run.sh);
my @dumb  = qw(./run.sh --no-mobility --dumb);

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
		$ret->{$1} = $2;
	}
	$ret
}

sub processMovedChecks {
	my $input = shift;

	my %vars = map {split /\t/} grep /\t/, split /\n/, $input;
	for my $k (keys %vars) {
		my @values = sort split " ", $vars{$k};
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

for my $filename (@ARGV) {
	my $smart = crystal [@smart, $filename];
	next unless defined $smart;
	my $dumb = crystal [@dumb, $filename];

	my $reduced = 1.0 - ($smart->{"Number of checks"} / $dumb->{"Number of checks"});
	$reduced *= 100;

	my $top5 = join ", ", processMovedChecks($smart->{"Mobility stats"});

	my ($base) = $filename =~ m!/([^/]+)\.sch!;

	my $line = join " & " => $base, "<TODO>", (sprintf '%.0f \%%', $reduced), $top5;
	print "$line \\\\\n";
}
