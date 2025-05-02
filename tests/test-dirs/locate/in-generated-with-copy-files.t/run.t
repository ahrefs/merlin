  $ dune exec ./main.exe
  Hello, World: 42

  $ $MERLIN single locate -look-for ml -position 1:56 -filename main.ml <main.ml
  {
    "class": "return",
    "value": {
      "file": "$TESTCASE_ROOT/_build/default/lib/native/client.ml",
      "pos": {
        "line": 1,
        "col": 4
      }
    },
    "notifications": []
  }
