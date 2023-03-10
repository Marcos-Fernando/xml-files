=head1 NAME

XML::XORT::Util::DbUtil::DB

=head1 SYNOPSIS


=head1 DESCRIPTION

This module has basic methods for connecting with any DB, some methods still need to 
be worked out.

=head1 CONTACT

Pinglei Zhou, FlyBase fellow at Harvard University (zhou@morgan.harvard.edu)

=cut

=head1 METHODS

=cut


package XML::XORT::Util::DbUtil::DB;
# use XML::XORT::Util::GeneralUtil::Structure qw(rearrange);
 use XML::XORT::Util::GeneralUtil::Structure;
 use Carp;
 use DBI;
 use strict;

#warning:   because many data contact % , so try to avoid sprintf function.

my %hash_ddl;
# if there are triggers which may change the unique_key value, then retrieve id after insertion will be DB specific.
my $TRIGGER=1;

#set switch for whether output debug message
my $DEBUG=0;

#usage XML::XORT::Util::DbUtil::DB->new(-db_type=>'mysql', -db=>'flydb',-host=>"localhost", -port=>'3036', -user=>'pinglei', -passsword=>'pinglei')
sub new {
 my $type=shift;
 my $self={};
 my $db_type=undef;
 my $database=undef;
 my $host=undef;
 my $port=undef;
 my $user=undef;
 my $password=undef;
      ($db_type, $database, $host, $port, $user, $password) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['db_type', 'db', 'host', 'port', 'user', 'password'], @_);

$self->{'db_type'}=$db_type;
$self->{'database'}=$database;
$self->{'host'}=$host;
$self->{'port'}=$port;
$self->{'user'}=$user;
$self->{'password'}=$password;

    my $pro=Properties->new('ddl');
    %hash_ddl=$pro->get_properties_hash();

bless ($self, (ref($type)|| $type));
return $self;
}

#usage XML::XORT::Util::DbUtil::DB->new(%dbh_hash)
sub _new {
   my  $type=shift;
     my $self={};

   my    $dbh_hash =  shift;
    my $db_type=$dbh_hash->{db_type};
   chomp($db_type);
   my $database=$dbh_hash->{db};
   chomp($database);
   my  $host=$dbh_hash->{host};
   chomp($host);
   my   $port=$dbh_hash->{port};
   chomp($port);
   my    $user=$dbh_hash->{user};
   chomp($user);
   my     $password=$dbh_hash->{password};
   chomp($password);
   my     $ddl_property=$dbh_hash->{ddl_property};
   chomp($password);
$self->{'db_type'}=$db_type;
$self->{'database'}=$database;
$self->{'host'}=$host;
$self->{'port'}=$port;
$self->{'user'}=$user;
$self->{'password'}=$password;
#print "\n $db_type\t$database\t$host\t$port\t$user\t$password";

    my $pro=XML::XORT::Util::GeneralUtil::Properties->new($ddl_property);
    %hash_ddl=$pro->get_properties_hash();

bless ($self, (ref($type)|| $type));
return $self;
}

sub open {
     my $self=shift;
     my ($data_source, $user, $password, $db_type, $dbh);
     $db_type=$self->{'db_type'};
     $user=$self->{'user'};
     $password=$self->{'password'};
     if ($db_type eq 'mysql'){
       $data_source="DBI:$self->{'db_type'}:$self->{'database'}:$self->{'host'}:$self->{'port'}";
      }
     elsif ($db_type eq 'postgres'){
       $data_source="dbi:Pg:dbname=$self->{'database'};host=$self->{'host'};port=$self->{'port'}";
     }
    # my $data_source="DBI:mysql:test:localhost:3306";
      $user=$self->{'user'};
      $password=$self->{'password'};
      $dbh=DBI->connect($data_source, $user, $password) or die ":can't connect to $data_source:$dbh->errstr\n";
      $dbh->{RaiseError}=0;
      $self->{'dbh'}=$dbh;
     return;
}

sub set_autocommit{
 my $self=shift;
  $self->{'dbh'}->{AutoCommit}=0;
  return;
}

sub close {
 my  $self=shift;
  $self->{'dbh'}->disconnect();
  return;
}

sub commit {
  my  $self=shift;
    $self->{'dbh'}->commit();
    return;
}

sub rollback{
 my  $self=shift;
   $self->{'dbh'}->rollback();
   return;
}

# ----------------------------------------------------------------------------------------------
# This special script execuate any statement will return one value: single colum and sing row
# ---------------------------------------------------------------------------------------------
sub get_one_value(){
  my $self=shift;
  my $dbh=$self->{'dbh'};
  my $stm=shift;
  my $query=$dbh->prepare($stm);
     $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
  my   $row_array = $query->fetchrow_arrayref;

    my $value=$row_array->[0];
    $query->finish();
    return $value;
}


 # exec will be completed sql statement

sub execute_sql(){
  my $self=shift;
  my $dbh=$self->{'dbh'};
  my $stm=shift;
  my $query=$dbh->prepare($stm);
     $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
     $query->finish();

}


# --------------------------------------------------------------------------------------------------------------
# This method is used to get all the data (rows) to be returned from the SQL statement. It returns a reference to an
#      array of arrays of references to each row. You access/print the data by using a nested loop. Example: 
#    my($i, $j); 
#    my $table = $sth->get_all_arrayref;
#      for $i ( 0 .. $#{$table} ) { 
#          for $j ( 0 .. $#{$table->[$i]} ) {
#              print "$table->[$i][$j]\t";
#          }
#      print "\n";
#      }


sub get_all_arrayref(){
    my $self=shift;
    my $stm=shift;

    my $ref_array;
    my $dbh=$self->{'dbh'};
    my $query=$dbh->prepare($stm);
    print "\nstm in DB.pm:$stm:" if ($DEBUG==1);;
    $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
    $ref_array=$query->fetchall_arrayref;
    $query->finish();
    print "\nsize of reutrn result:$#{$ref_array}\n" if ($DEBUG==1);
    return $ref_array;
}

#  Fetches the next row of data and returns it as a reference to a hash containing field name and field value pairs.
#   Null fields are returned as undef values in the hash.
sub get_row_hashref(){
    my $self=shift;
    my $stm=shift;

    my $dbh=$self->{'dbh'};
    my $query=$dbh->prepare($stm);
    $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
    return $query->fetchrow_hashref;
}


# this will return a hash1 of hash_ref, which hash_ref refer to hash of name/value, and key for hash1 is serial number

sub get_all_hashref(){
    my $self=shift;
    my $stm=shift;
    my %hash_ref;
    my $count=0;
    my $flag=0;
    #warn "\nstm in get_all_hashref: $stm";
    my $dbh=$self->{'dbh'};
#  eval {

    my $query=$dbh->prepare($stm);
    $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
#    while (my %hash_temp=%{$query->fetchrow_hashref}){
#       $hash_ref->{$count}=\%hash_temp;
#       $count++;
#    }
    my $hash_temp=undef;
    while ( $hash_temp=$query->fetchrow_hashref){
       $count++; 
       $hash_ref{$count}=$hash_temp;

    }
    if ($count>0){
      #warn "\nthere is some result ...:$stm\n\n";
      #my $r=\hash_ref;
      #warn "\nhash ref" if (ref($r) eq 'HASH');
      return \%hash_ref;
    }
    else {
       #warn "\nno return here:\n$stm";
       return;
    }
#  };
#  if ($@) {
    warn $@; # print the error
#    warn "\nsomething wrong with DB...";
#  }
}


sub get_all_hashref(){
    my $self=shift;
    my $stm=shift;
    my $hash_ref;
    my $count=0;
   # print "\nstm in get_all_hashref: $stm";
    my $dbh=$self->{'dbh'};
  eval {
    my $query=$dbh->prepare($stm);
    $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
    while (my %hash_temp=%{$query->fetchrow_hashref}){
       $hash_ref->{$count}=\%hash_temp;
       $count++;
    }
    if ($count>0){
      return $hash_ref;
    }
    else {warn "\nno return from DB...";
       return;
    }
  };
  if ($@) {
    warn $@; # print the error
  }
}
=cut
sub get_table_info{
    my $self=shift;
    my $dbh=$self->{'dbh'};
  my $sth=$dbh->table_info('%','','');;
  my $table_info;
    my $table_array_ref=$sth->fetchrow_array;

   return $table_info;
 }


# usage: db_obj->db_select(-data_hash=>\%hash, -table=$table_name)
sub db_select(){
     my $self=shift;
     my $DELETE_BATCH=0;
     my ($ref, $table, $hash_local_id, $hash_trans, $log_file,$delete_batch) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash',  'table', 'hash_local_id', 'hash_trans', 'log_file','delete_batch'], @_);
     $DELETE_BATCH=$delete_batch if (defined $delete_batch);
     #my $id=$table."_id";
     my $table_id_string=$table."_primary_key";
     my $id=$hash_ddl{$table_id_string};

     my $data_hash_ref=&_data_type_checker($ref, $table);

     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }

     #here format the select statement
     my ($where_list, $stm_select);
     foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
         #  print "\ninsert unique of $table:$key";
           if (defined $where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if (defined $where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key} && $DELETE_BATCH!=1) {
             print "\nin db_select, you missed this not null column:$key of table: $table  which has NO default value";
             #exit(1);
             return;
          }
        }
     }

    if (defined $where_list){
       $stm_select="select $id from $table where $where_list";
    }

   #print "\n\ndb_select stm:$stm_select";
   if (defined $stm_select){
          # here start the database work, first check, if not in db, then insert
          my ($rs, $query, $row_array, $db_id);
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
          $rs= $query->execute;
          if (! $rs ) {
             &create_log($hash_trans, $hash_local_id, $log_file);
              # die "could not execute: $stm_select\n";
              print "\nunable to execute:$stm_select\n";
              return
          }
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
             #print "\ndb_id is:$db_id";
             $query->finish();
             return $db_id;
          }
          else {
             return;
           }
	}

return;
}

# this is different from db_select: this is special case: "select table_id from table where ...."
# for empty hash_ref, it will do nothing
#two type of lookup: fails if item is not found, or lookup, if not found, insert
# usage: db_obj->db_lookup(-data_hash=>\%hash, -table=$table_name)
sub db_lookup(){
     my $self=shift;

     my ($ref, $table, $hash_local_id, $hash_trans, $log_file) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash',  'table', 'hash_local_id', 'hash_trans', 'log_file'], @_);

    # my $id=$table."_id";
     my $table_id_string=$table."_primary_key";
     my $id=$hash_ddl{$table_id_string};

     my $data_hash_ref=&_data_type_checker($ref, $table);

     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }

     #here format the select statement
     my ($where_list, $stm_select, $stm_insert);
     foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
         #  print "\ninsert unique of $table:$key";
           if (defined $where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if (defined $where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key}) {
             print "\nin db_lookup, you missed this not null column:$key of table: $table  which has NO default value";
             exit(1);
          }
        }
     }

    if ($where_list){
       $stm_select="select $id from $table where $where_list";
    }



    #in case it is not in the database, we may first insert, then return the 
     my ($data_list, $col_list);
     foreach my $key(keys %$data_hash_ref){
       if (defined $data_list){
	      $data_list=$data_list." , ".$data_hash_ref->{$key};

       }
       else {
	      $data_list=$data_hash_ref->{$key};
       }
      if (defined $col_list){
	      $col_list=$col_list." , ".$key;

       }
       else {
	      $col_list=$key;
       }
     }
    if ($data_list && $col_list){
       $stm_insert="insert into $table ($col_list) values ($data_list )";
    }


   print "\n\nlookup stm:$stm_select\n" if ($DEBUG==1);

   if ((defined $stm_select) && (defined $stm_insert)){
          # here start the database work, first check, if not in db, then insert
          my ($rs, $query, $row_array, $db_id);
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
          $rs= $query->execute;
          if (! $rs ) {
             &create_log($hash_trans, $hash_local_id, $log_file);
              die "could not execute: $stm_select\n";
          }
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
             $query->finish();
             return $db_id;
          }

          else {
             &create_log($hash_trans, $hash_local_id, $log_file);
              die "The record you try to lookup is not in database yet: $stm_select\n";

           # $query=$dbh->prepare($stm_insert);
           # $rs= $query->execute;
           # if (! $rs ) {
           #    &create_log($hash_trans, $hash_local_id, $log_file);
           #    die "could not execute: $stm_insert\n";
           # }
           # $query=$dbh->prepare($stm_select);
           # $query->execute or die "Unable to execute query: $dbh->errstr:$stm_select\n";
           # $row_array = $query->fetchrow_arrayref;
           # $db_id= $row_array->[0];
           # if ($db_id){
           #    return $db_id;
           # }

         }
	}

return;
}

# old_hash must have all the unique key(s) to ensure only update ONE record each time, otherwise, error ....
#usage: db_obj->db_update(-data_hash=>\%hash_data, -new_hash=>\%hash_new,  -table=>$table_name)
sub db_update(){
  my $self=shift;
  #   my ($ref, $new_ref, $table) =XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash', 'new_hash', 'table'], @_);

     my ($ref, $new_ref, $table, $hash_local_id, $hash_trans, $log_file) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash', 'new_hash',  'table', 'hash_local_id', 'hash_trans', 'log_file'], @_);

     my $data_hash_ref=&_data_type_checker($ref, $table);
     my $new_hash_ref=&_data_type_checker($new_ref, $table);

  my ($data_list, $where_list, $stm_select, $stm_update);
     # here to get the data_list from $new_hash_ref
     foreach my $key(keys %$new_hash_ref){
       if (defined $data_list){
                   if ($new_hash_ref->{$key}){
		        $data_list=$data_list." , ".$key."=".$new_hash_ref->{$key};
	           }
		   else {
		        $data_list=$data_list." , ".$key."= null ";
		   }
       }
       else {
                   if ($new_hash_ref->{$key}){
		       $data_list=$key."=".$new_hash_ref->{$key};
		   }
		   else{
		        $data_list=$key."= null ";
		   }
       }
     }

     # here to get the where_list from $data_hash_ref 
   #  foreach my $key(keys %$data_hash_ref){
   #    if ($where_list){
   #                if ($data_hash_ref->{$key}){
   #		        $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
   #	           }
   #		   else {
   #		        $where_list=$where_list." and ".$key." is null ";
   #		   }
   #    }
   #    else {
   #                if ($data_hash_ref->{$key}){
   #		       $where_list=$key."=".$data_hash_ref->{$key};
   #		   }
   #		   else {
   #		        $where_list=$key." is null ";
   #		   }

   #   }
   #  }


#  if ($data_list && $where_list){
#          $stm_update="update $table set ".$data_list." where ".$where_list;
#  }
# print "\n\nupdate stm:$stm_update";


     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }

     #here format the select statement
     foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
         #  print "\ninsert unique of $table:$key";
           if (defined $where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if (defined $where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key}) {
             print "\nin db_update, you missed this not null column:$key of table: $table  which has NO default value";
             exit(1);
          }
        }
     }
    #my $id=$table."_id";
    my $table_id_string=$table."_primary_key";
    my $id=$hash_ddl{$table_id_string};

    if ($where_list){
       $stm_select="select $id from $table where $where_list";
    }

  if ($data_list && $where_list){
       $stm_update="update $table set ".$data_list." where ".$where_list;
  }
  #print "\nin update, stm_select:$stm_select\nstm_update:$stm_update";

     my ($rs, $query, $row_array, $db_id);
    if ($stm_select && $stm_update){
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
          # $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
          $rs= $query->execute;
          if (! $rs ) {
             &create_log($hash_trans, $hash_local_id, $log_file);
              die "could not execute: $stm_select\n";
          } 
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
               $query=$dbh->prepare($stm_update);
               $rs= $query->execute;
               if (! $rs ) {
                  &create_log($hash_trans, $hash_local_id, $log_file);
                  die "could not execute: $stm_update\n";
                }
                $query->finish();
                return $db_id;
	  }
          else {
                print "\nthe record you try to update not exist in the db yet";
                &create_log($hash_trans, $hash_local_id, $log_file);
                exit(1);
          }
    }


 return;
}

# need to fix
# hash_data should have all the unique key(s) to ensure only delete ONE record each time
#usage: db_obj->db_delete(-data_hash=>\%hash_data, -table=$table_name)
sub db_delete(){
     my $self=shift;
     my $DELETE_BATCH=0;
     my ($ref, $table, $hash_local_id, $hash_trans, $log_file, $delete_force) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash', 'table', 'hash_local_id', 'hash_trans', 'log_file','delete_force'], @_);
     $DELETE_BATCH=$delete_force if (defined $delete_force);
     my $data_hash_ref=&_data_type_checker($ref, $table);
     #my $id=$table."_id";
     my $table_id_string=$table."_primary_key";
     my $id=$hash_ddl{$table_id_string};
     my ($where_list, $stm_delete, $stm_select, $db_id);



     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }
     #here to check how many unique keys WITH value
     my $unique_keys_with_value=0;
     foreach my $k(keys %hash_unique){
        $unique_keys_with_value ++ if (defined $data_hash_ref->{$k});
     }
     #here format the select statement

     foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
         #  print "\ninsert unique of $table:$key";
           if ($where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if ($where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key}) {
            if ($unique_keys_with_value==0 || $DELETE_BATCH!=1){
             print "\nin db_delete, you missed this not null column:$key of table: $table  which has NO default value";
             exit(1);
	   }
          }
        }
     }


  if ($where_list){
    $stm_select="select $id from $table where $where_list";
    $stm_delete="delete from $table where  $where_list";
  }

  #print "\n\nin delete, delete_stm:$stm_delete\ndelete stm_select:$stm_select";

  if ($stm_delete && $stm_select){
          my ($rs, $query, $row_array, $db_id);
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
            $rs=$query->execute;
            if (!$rs) {
               &create_log($hash_trans, $hash_local_id, $log_file);
               die "unable to execute:$stm_select\n";
             }
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
            $query=$dbh->prepare($stm_delete);
            $rs=$query->execute;
            if (!$rs) {
               &create_log($hash_trans, $hash_local_id, $log_file);
               die "unable to execute:$stm_delete\n";
             }
            $query->finish();
            return $db_id;
	  }
          else {
            print "\nWarning: the record you try to delete is not in db:$stm_delete";
          }
    }

return;
}

# two type of insert: insert faile if unique constrait exists or insert, if already exist, then update
#usage: db_obj->db_insert(-data_hash=>\%hash_old, -table=$table_name)
sub db_insert(){
  my $self=shift;


     my ($ref, $table, $hash_local_id, $hash_trans, $log_file) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash', 'table', 'hash_local_id', 'hash_trans', 'log_file'], @_);

     #my $id=$table."_id";
     my $table_id_string=$table."_primary_key";
     my $id=$hash_ddl{$table_id_string};
     my $data_hash_ref=&_data_type_checker($ref, $table);

     #here we need this because trigger will change the unique_key value, so can't get the id using ORIGINAL unique_key values
     my $table_seq=$table."_".$id."_seq";
     my $stm_select_seq="select last_value from $table_seq";


     my ($data_list, $col_list, $stm_insert, $stm_select, $db_id);
     foreach my $key(keys %$data_hash_ref){
       if ($data_list){
	      $data_list=$data_list." , ".$data_hash_ref->{$key};

       }
       else {
	      $data_list=$data_hash_ref->{$key};
       }
      if ($col_list){
	      $col_list=$col_list." , ".$key;

       }
       else {
	      $col_list=$key;
       }
     }
     if ($col_list && $data_list){
        $stm_insert="insert into $table ($col_list) values ($data_list )";
     }

     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }

     #here format the select statement
     my ($where_list);
  foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
           print "\ninsert unique of $table:$key";
           if ($where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if ($where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key}) {
             print "\nin db_insert, you missed this not null column:$key of table: $table  which has NO default value";
             exit(1);
          }
        }
     }

    if ($where_list){
       $stm_select="select $id from $table where $where_list";
    }

    #print "\ninsert: stm_select:$stm_select\nstm_insert:$stm_insert" if ($DEBUG==1);

    if ($stm_insert && $stm_select){
          my ($rs, $query, $row_array, $db_id);
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
          $query->execute or die "Unable to execute query: $dbh->errstr:$stm_select\n";
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
            print "\nWarning: you try to insert a duplicate record:$stm_insert";
            $query->finish();
            return $db_id;
	  }
          else {
            $query=$dbh->prepare($stm_insert);
            $rs= $query->execute;
            if (! $rs ) {
                  &create_log($hash_trans, $hash_local_id, $log_file);
                  die "could not execute $stm_insert\n";
            }
            if ($TRIGGER==1){
               $query=$dbh->prepare($stm_select_seq);
	     }
            else {
               $query=$dbh->prepare($stm_select);
            }
            $query->execute or die "Unable to execute query: $dbh->errstr:$stm_select\n";
            $row_array = $query->fetchrow_arrayref;
            $db_id= $row_array->[0];
            if ($db_id){
               $query->finish();
               return $db_id;
            }
          }
    }

 return;
}

sub get_last_id (){
  my $self=shift;
  my $table=shift;
  my $table_id_string=$table."_primary_key";
  my $id=$hash_ddl{$table_id_string};
  my $table_seq=$table."_".$id."_seq";
  my $dbh=$self->{'dbh'}; 
  my $stm_select_seq="select last_value from $table_seq";
  my          $query=$dbh->prepare($stm_select_seq);
  my          $rs=$query->execute;

            if (! $rs ) {
                  die "could not execute $stm_select_seq\n";
            }
           my  $row_array = $query->fetchrow_arrayref;
           my  $db_id= $row_array->[0];
            if ($db_id){
               $query->finish();
               return $db_id;
            }
  return;
}

# two type of force: create if look up can't find the data, and update if it already exist and have new data
# usage: db_obj->db_insert(-data_hash=>\%hash_data, -table=$table_name)
sub db_force(){
  my $self=shift;
     my ($ref, $table, $hash_local_id, $hash_trans, $log_file) =
     XML::XORT::Util::GeneralUtil::Structure::rearrange(['data_hash', 'table', 'hash_local_id', 'hash_trans', 'log_file'], @_);

     #my $id=$table."_id";
     my $table_id_string=$table."_primary_key";
     my $id=$hash_ddl{$table_id_string};
     my $data_hash_ref=&_data_type_checker($ref, $table);

     my ($data_list, $col_list, $stm_insert, $stm_select, $stm_update);
     my $update_need;

     #here we need this because trigger will change the unique_key value, so can't get the id using ORIGINAL unique_key values
     my $table_seq=$table."_".$id."_seq";
     my $stm_select_seq="select last_value from $table_seq";

    foreach my $key (keys %$data_hash_ref){
     	print "\nin db_force,key:$key:\tvalue:$data_hash_ref->{$key}" if ($DEBUG==1);
    }

     #format the insert statement
     foreach my $key(keys %$data_hash_ref){
       if (defined $data_list){
	      $data_list=$data_list." , ".$data_hash_ref->{$key};

       }
       else {
	      $data_list=$data_hash_ref->{$key};
       }
      if (defined $col_list){
	      $col_list=$col_list." , ".$key;

       }
       else {
	      $col_list=$key;
       }
     }

     if ($col_list && $data_list){
        $stm_insert="insert into $table ($col_list) values ($data_list )";
     }

     #get the unique column of this table,
     my $unique_key=$table."_unique";
     my %hash_unique;
     my @temp=split(/\s+/, $hash_ddl{$unique_key});
     for (@temp){
       $hash_unique{$_}++;
     }

     #get the not null column of this table
     my $no_null_key=$table."_non_null_cols";
     my %hash_no_null;
     my @temp1=split(/\s+/, $hash_ddl{$no_null_key});
     for (@temp1){
       $hash_no_null{$_}++;
     }

     #here format the select statement
     my ($where_list);
     foreach my $key(keys %hash_unique){
        if (defined $data_hash_ref->{$key}){
         #  print "\ninsert unique of $table:$key";
           if ($where_list){
               $where_list=$where_list." and ".$key."=".$data_hash_ref->{$key};
           }
           else {
 	       $where_list=$key."=".$data_hash_ref->{$key};
           }
         }
        # to see whether there is default value for this not null column
        else {
          my $key_default_value=$table.":".$key."_default";
	  if (defined $hash_ddl{$key_default_value} && $hash_ddl{$key_default_value} ne 'current_timestamp' ){
             if ($where_list){
	         $where_list=$where_list." and ".$key."=".$hash_ddl{$key_default_value};
              }
             else {
                 $where_list=$key."=".$hash_ddl{$key_default_value};
             }
	  }
           #if this is unique, not null, and no default value, it will be error ....
          elsif(defined $hash_no_null{$key}) {
             print "\nin db_force, you missed this not null column:$key of table: $table  which has NO default value";
             exit(1);
          }
        }
     }

    my ($select_what, $stm_select_temp);
    if ($where_list){
       #print "\nin db_force:$where_list";
       $stm_select="select $id from $table where $where_list";
       foreach my $key (keys %$data_hash_ref){
	 if ($key =~/\w/){
           if (defined $select_what){
              $select_what=$select_what.", ".$key;
	   }
           else {
              $select_what=$key;
           }
	 }
       }
       $stm_select_temp="select $select_what from $table where $where_list";
       #print "\nin db_force:$stm_select_temp";
    }




    #test whether has new data, if yes, then need update
   foreach my $key (keys %$data_hash_ref){
    if (!(defined $hash_unique{$key})){
      #$update_need='true';
      last;
    }
  }




    # here to get the update list
    my ($data_update_list);
     foreach my $key (keys %$data_hash_ref){
       if ($data_update_list){
                   if (defined $data_hash_ref->{$key}){
		        $data_update_list=$data_update_list." , ".$key."=".$data_hash_ref->{$key};
	           }
		   else {
		        $data_update_list=$data_update_list." , ".$key."= null ";
		   }
       }
       else {
                   if (defined $data_hash_ref->{$key}){
		       $data_update_list=$key."=".$data_hash_ref->{$key};
		   }
		   else{
		        $data_update_list=$key."= null ";
		   }
       }
     }

  if ($data_update_list){
      $stm_update="update $table set $data_update_list where $where_list";
  }


   print "\ndb_force: stm_select:$stm_select\nstm_insert:$stm_insert\nstm_update:$stm_update" if ($DEBUG==1);
    my ($rs, $row_array, $query, $db_id);
    if ($stm_insert && $stm_select && $stm_update){
          my $dbh=$self->{'dbh'}; 
          $query=$dbh->prepare($stm_select);
          # $query->execute or die "Unable to execute query: $dbh->errstr:$stm\n";
          $rs= $query->execute;
          if (! $rs ) {
             &create_log($hash_trans, $hash_local_id, $log_file);
              die "could not execute $stm_select\n";
          } 
          $row_array = $query->fetchrow_arrayref;
          $db_id= $row_array->[0];
          if ($db_id){
            #here to test whether need update
            my $query_temp=$dbh->prepare($stm_select_temp);
            my $rs_temp=$query_temp->execute;
            my $ref_temp=$query_temp->fetchrow_hashref;
            my $ref_temp1=&_data_type_checker($ref_temp, $table);
            foreach my $key (keys %$ref_temp1){
                #attention: +1 and 1 should see as 'same'
	      if ($key eq 'name' && $ref_temp1->{$key} =~/CG10026:6_temp1/){
                     print "\ this column:$key, old value:$ref_temp1->{$key}, new value:$data_hash_ref->{$key}\nstm_select:$stm_select_temp\n";
              }
	      if ($ref_temp1->{$key} =~/^\d\d*/){
                  if ( $ref_temp1->{$key} == $data_hash_ref->{$key}){
                      print "$ref_temp1->{$key}, new value:$data_hash_ref->{$key} are equal ????" if ($key eq 'name' && $ref_temp1->{$key} =~/CG10026:6_temp1/);
                  }

                  else {
                        $update_need='true';
                        print "\nneed update for this column:$key, old value:$ref_temp1->{$key}, new value:$data_hash_ref->{$key}\nstm_select:$stm_select_temp\n\n$stm_update\n";
                        last;
                  }
	      }
              else {
                  if ($ref_temp1->{$key} eq $data_hash_ref->{$key} ){
                      print "$ref_temp1->{$key}, new value:$data_hash_ref->{$key} are equal ????" if ($key eq 'name' && $ref_temp1->{$key} =~/CG10026:6_temp1/);
	          }
                  else {
                        $update_need='true';
                        print "\nneed update for this column:$key, old value:$ref_temp1->{$key}, new value:$data_hash_ref->{$key}\nstm_select:$stm_select_temp\n\n$stm_update\n";
                        last;
                  }
              }
	    }
            $query_temp->finish();
            if ($update_need eq 'true'){
               $query=$dbh->prepare($stm_update);
               #  $query->execute || (  &create_log() && die);
               $rs= $query->execute;
               if (! $rs ) {
                  &create_log($hash_trans, $hash_local_id, $log_file);
                  die "could not execute $stm_update\n";
                }
	    }
            $query->finish();
            #here some test to see whether have update
            return $db_id;
	  }
          else {
            $query=$dbh->prepare($stm_insert);
            $rs=$query->execute;
            if (!$rs) {
               &create_log($hash_trans, $hash_local_id, $log_file);
               die "unable to execute:$stm_insert\n";
             }

            if ($TRIGGER==1){
               $query=$dbh->prepare($stm_select_seq);
	     }
            else {
               $query=$dbh->prepare($stm_select);
            }

           # $query->execute || (  &create_log() && die);
            $rs= $query->execute;
            if (! $rs ) {
                  &create_log($hash_trans, $hash_local_id, $log_file);
                  die "could not execute $stm_select or \n$stm_select_seq\n";
            }
            $row_array = $query->fetchrow_arrayref;
            $db_id= $row_array->[0];
            if ($db_id){
               $query->finish();
               return $db_id;
            }
          }
    }

 return;
}


sub beginTransaction {

  my ($pkg) = @_;

  my $sql = "begin work;";
  (DBAPI::exec($pkg->{dbhandle}, "$sql", 0) == 0)
  
    or die "couldn't exec query: $sql\n";
}

sub endTransaction {

  my ($pkg) = @_;

  my $sql = "commit work;";
  (DBAPI::exec($pkg->{dbhandle}, "$sql", 0) == 0)
    or die "couldn't exec query: $sql\n";
}

sub escapeQuotes {
  my ($pkg, $q) = @_;

  if (!ref($pkg)) {
    $q = $pkg;
  }

  $q =~ s/\'/\'\'/g;
  return $q;
}



#
# updateTableHash
# 
# Inserts a row into the table whose name is passed in as $_[0]
# $_[1] must contain a hash with {column name, value} pairs
#
sub updateTableHash {
  
  my ($pkg, $table, $entry, $key_col, $key_val) = @_;

  my $key;
  my $names = "";
  my $values = "";
  
  foreach $key ( keys %$entry ) {
    my $val = $entry->{$key};
    
    if (defined($val)) {
      if ($val =~ /ARRAY\(0x\w+\)/) {
      }
      elsif ($val =~ /FILETO/) {
	$names .= "$key,";
	$values .= "$val,";
      }
      else {
	$names .= "$key,";
	$values .= "'$val',";
      }
    }
  }
  # Remove last commas
  chop $names;
  chop $values;
  
  my $sql = "update $table set ($names) = ($values) ";
  $sql .= "where $key_col = '$key_val';";
  
  print "$sql\n" if ($DEBUG);
  
  (DBAPI::exec($pkg->{dbhandle}, "$sql", 0) == 0)
    or die "couldn't exec query: $sql\n";
  
}


#
# insertTableHash
# 
# Inserts a row into the table whose name is passed in as $_[0]
# $_[1] must contain a hash with {column name, value} pairs
#
sub insertTableHash {
  my ($pkg, $table, $entry) = @_;
  my $key;
  my $names = "";
  my $values = "";
  
  foreach $key ( keys %$entry ) {
    my $val = $entry->{$key};
    if (defined($val)) {
	   $names .= "$key,";
	   $values .= "$val,";
      }
    else {
	   $names .= "$key,";
	   $values .= "'$val',";
      }
    }

  # Remove last commas
  chop $names;
  chop $values;

  #    if (defined($entry->{name})) {
  #      print "$table: $entry->{name}\n";
  #    }
  
  my $sql = "insert into $table ";
  $sql .= "($names) values ($values);";
  
  print "$sql\n" if ($DEBUG);
  print "\nsql:$sql\n";
  my $dbh=$pkg->{dbh};
  my $query=$dbh->prepare($sql);
     $query->execute or die "Unable to execute query: $dbh->errstr\n";
}

#
# insertTableHashSerial
# 
# Inserts a row into the table whose name is passed in as $_[0]
# $_[1] must contain a hash with {column name, value} pairs
#
sub insertTableHashSerial {

  my ($pkg, $table, $entry) = @_;
  
  my $key;
  my $names = "";
  my $values = "";

  
  foreach $key ( keys %$entry ) {
	my $val = $entry->{$key};
	
	if (defined($val)) {
	  if ($val =~ /ARRAY\(0x\w+\)/) {
	  }
	  elsif ($val =~ /FILETO/) {
	    $names .= "$key,";
	    $values .= "$val,";
	  }
	  else {
	    $names .= "$key,";
	    $values .= "'$val',";
	  }
	}
      }
  # Remove last commas
  chop $names;
  chop $values;

  my $sql = "insert into $table ";
  $sql .= "($names) values ($values);";

  #    if (defined($entry->{name})) {
  #      print "$table: $entry->{name}\n";
  #    }
  
  print "$sql\n" if ($DEBUG);
  
  (DBAPI::exec($pkg->{dbhandle}, "$sql", 0) == 0)
    or die "couldn't exec query: $sql\n";
  
  my $result = &DBAPI::get_result($pkg->{dbhandle});
  my $num = &DBAPI::last_serial8($pkg->{dbhandle});
  #    print "Inserted $table id: $num\n";
  
  return $num;
}

 #accessory method to that check data type, for anything that is not the (int, float, serial, small, bigint decimal numeric real bigserial) , value will be closed in ''
# for boolean type, replace 0 with 'f' and 1 with 't'
 # $hash_ref=&_data_type_checker($hash_ref,$table_name);
sub _data_type_checker(){
    my $hash_ref=shift;
    my $table=shift;
    my %hash_boolean={
          0=>'TRUE',
          1=>'FALSE',
    };

    foreach my $key (keys %$hash_ref){
     	print "\nin DB, before type check key:$key:\tvalue:$hash_ref->{$key}" if ($DEBUG==1);
    }

  #  print "\ndata_type:$data_type";

    # here for updated columns, need to replace with new records to cascade the update(here is for non_unique key)
	#foreach my $value (keys %$hash_ref){
        #    if (defined $hash_new_value{$value}){
	#	$hash_ref->{$value}=$hash_new_value{$value};
	#    }
	#}


   #here to deal with special case: O'Reiley, 
    foreach my $key (keys %$hash_ref){
        $hash_ref->{$key} =~ s/\'/\'\'/g;
        #$hash_ref->{$key} =~ s/\\/\\\\/g;
    }

    my $data_type_name=$table."_data_type";
    my $data_type=$hash_ddl{$data_type_name};
   # print "\n\ndata_type:$data_type";
    my @temp=split(/;/, $data_type);
    for my $i(0..$#temp){
        my @temp1=split(/:/, $temp[$i]);
	if ($temp1[1] !~ /int|serial|float|smallint|integer|bigint|decimal|numeric|real|bigserial/ && $hash_ref->{$temp1[0]} ne 'NULL' ){
            if ($temp1[1] =~  /boolean/ && defined $hash_boolean{$hash_ref->{$temp1[0]}} && defined($hash_ref->{$temp1[0]}) && ($hash_ref->{$temp1[0]} !~ /^\'\S*\'$/)){
                  $hash_ref->{$temp1[0]}="\'".$hash_boolean{$hash_ref->{$temp1[0]}}."\'";
            }
	    elsif ( defined($hash_ref->{$temp1[0]}) && ($hash_ref->{$temp1[0]} !~ /^\'\S*\'$/)){
              $hash_ref->{$temp1[0]}="\'".$hash_ref->{$temp1[0]}."\'";
            }
       	}
             # in case of boolean type, need to replace 0/1 with f/t ?
            if ($temp1[1] =~/boolean/ && exists $hash_boolean{$hash_ref->{$temp1[0]}} ){
               $hash_ref->{$temp1[0]}=$hash_boolean{$hash_ref->{$temp1[0]}};
	    }
    }

   return $hash_ref;
}

sub create_log(){
   my $hash_trans=shift;
   my $hash_local_id=shift;
   my $file=shift;

   my $log_file=">".$file;
   print "\nlog file:$log_file";
   open (LOG, $log_file);
   foreach my  $key (keys %$hash_local_id){
      print LOG "$key\t$hash_local_id->{$key}\n";
   }
   print "\nsorry, for some reason, this process stop before finish the following transaction:$hash_trans->{table}";
   foreach my $key (keys %$hash_trans){
     if ($key ne 'table'){
         print "\nelement:$key\tvalue:$hash_trans->{$key}";
    }
   }
   print "\n\n";
}

1;


