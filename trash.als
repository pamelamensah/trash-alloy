var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

pred do_something_else {
  File' = File
  Trash' = Trash
}

pred forceDelete[f: File] {
  File' = File - f
  Trash' = Trash - f
}

fact trans {
  always (
    empty
    or (some f : File | delete[f] or restore[f] or forceDelete[f])
    or do_something_else
  )
}


//run example {} for 5

/*assert restore_after_delete {
  always (all f : File | restore[f] implies once delete[f])
}

check restore_after_delete for 5 but 20 steps
*/
assert delete_all {
  always ((Trash = File and empty) implies after always no File)
}

check delete_all for 5 but 20 steps
