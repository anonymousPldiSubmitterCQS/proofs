From iris.heap_lang Require Export notation.

Record outerStorageInterface :=
  OuterStorageInterface {
      tryInsert : val;
      tryRetrieve : val;
      newStorage : val;
    }.
