From iris.heap_lang Require Export notation.

Record listInterface :=
  ListInterface {
      newList: val;
      cleanPrev: val;
      findSegm: val;
      moveForward: val;
      onSlotCleaned: val;
    }.
