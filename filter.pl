#!/usr/bin/perl -w

use strict;

my $log = 1;
my $skip = "false";
my %kb = ();

while (<>) {

  if ($log==1) {

    if (/^digraph G/) {
      $log=0 ;
      print $_ ;
    }
    $kb{$1}=12 if /Adding clause #([0-9]+)/ ;

  } else {

    if (/^n([0-9]+) \[/) {
      $skip = "false";
      if (defined $kb{$1}) {
        print $_ ;
      } else {
        $skip = "true";
      }
    } else {
      print $_ if $skip eq "false";
    }
  }
}
print "}\n";
