#!/usr/bin/perl
use strict;
use warnings;
use Getopt::Long;

my $relative = 0;
GetOptions("relative|r!" => \$relative);

my %store;
my %funlength;

my $failed = 0;

while (<>) {
	if (/^FUNCTION (\S+) (\d+)/) {
		$funlength{$1} = $2;
	} elsif ($failed or /Check failed/) {
		$failed = 1;
		print;
	} else {
		my ($fun, $var, $defUse, $defCheck) = split;

		if (!exists $store{$var} || ($defUse < $store{$var}[0])) {
			$store{$var} = [$defUse, $defCheck, $fun];
		}
	}
}

exit 1 if $failed;

if ($relative) {
	$_ = [ 100, 100 * ($_->[1] / $_->[0]), $_->[2] ] for values %store;
}

my @keys = reverse sort { $store{$a}[1] <=> $store{$b}[1] } keys %store;

for my $k (@keys) {
	my ($defUse, $defCheck, $fun) = @{$store{$k}};
	print join("\t" => ($k, $defUse, $defCheck)), "\n";
}
