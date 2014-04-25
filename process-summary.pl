#!/usr/bin/perl
use strict;
use warnings;

my %store;

while (<>) {
	my ($var, $defUse, $defCheck) = split;

	if (!exists $store{$var} || ($defUse < $store{$var}[0])) {
		$store{$var} = [$defUse, $defCheck];
	}
}

my @keys = reverse sort { $store{$a}[1] <=> $store{$b}[1] } keys %store;

for my $k (@keys) {
	my ($defUse, $defCheck) = @{$store{$k}};
	print join("\t" => ($k, $defUse, $defCheck)), "\n";
}
