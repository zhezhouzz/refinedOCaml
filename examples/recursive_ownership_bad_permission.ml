let[@refined.over
     {
       pre = "true";
       post = "true";
       result_references = [ ("0", "true") ];
       result_reference_permissions = [ ("0", "consume") ];
     }] bad_permission (cell : int ref) : int ref * int =
  (cell, 0)
