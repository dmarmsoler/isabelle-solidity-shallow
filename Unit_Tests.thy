theory Unit_Tests
imports Solidity "HOL-Library.Code_Target_Numeral"
begin
(*
  Tested with v0.8.25
*)

global_interpretation method: Method A1 250
  defines method_sender_monad = method.sender_monad
      and method_value_monad  = method.value_monad
  by standard (simp add: null_def)

global_interpretation contract: Contract A1 
  defines contract_assign_stack_monad = contract.assign_stack_monad
      and contract_assign_stack       = contract.assign_stack
      and contract_stackLookup        = contract.stackLookup
      and contract_storeLookup        = contract.storeLookup
      and contract_assign_storage_monad = contract.assign_storage_monad
      and contract_assign_storage = contract.assign_storage
      and contract_storage_update_monad = contract.storage_update_monad
      and contract_storage_update = contract.storage_update
      and contract_this_monad = contract.this_monad
      and contract_storearrayLength = contract.storeArrayLength
      and contract_arrayLength = contract.arrayLength
      and contract_allocate = contract.allocate
  .

global_interpretation keccak256: Keccak256 id
  defines keccak256_keccak256_monad = keccak256.keccak256_monad
  by standard simp

section "States"

definition emptyState::"aspace state" where "emptyState =
  \<lparr>
    state.Memory = [],
    state.Calldata = fmempty,
    state.Storage = (\<lambda>_ _. undefined),
    state.Stack = fmempty,
    state.Balances = (\<lambda>_. 0)
  \<rparr>"

section "Expressions"

subsection "Constant monads"

lemma "P (execute (bool_monad True) emptyState) = P (Normal (rvalue.Value (Bool True),emptyState))"
  by (normalization)

lemma "P (execute (bool_monad False) emptyState) = P (Normal (rvalue.Value (Bool False),emptyState))"
  by (normalization)

lemma "P (execute (sint_monad 5) emptyState) = P (Normal (rvalue.Value (Sint 5),emptyState))"
  by (normalization, simp)

lemma "P (execute (address_monad A5) emptyState) = P (Normal (rvalue.Value (Address A5),emptyState))"
  by (normalization)

subsection "Not monad"
(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        assert (!true == false);
    }

    function test2() public {
        assert (!false == true);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (not_monad true_monad) false_monad)
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (not_monad false_monad) true_monad)
      }) emptyState)"
  by (normalization)

subsection "Less monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          assert (10 <= 100);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (less_monad (sint_monad 10) (sint_monad 100))
      }) emptyState)"
  by (normalization)

subsection "And monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
        assert (true && false == false);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (and_monad (true_monad) (false_monad)) (false_monad))
      }) emptyState)"
  by (normalization)

subsection "And monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
        assert (true || false == true);
      }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (or_monad (true_monad) (false_monad)) (true_monad))
      }) emptyState)"
  by (normalization)

subsection "This monad"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract.this_monad) (address_monad A1))
      }) emptyState)"
  by (normalization)

subsection "Plus monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      unchecked{ assert(5 + 6 == 11); }
    }

    function test2() public {
      unchecked{ assert(2**256-1 + uint256 (6) == 5); }
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad (sint_monad 5) (sint_monad 6)) (sint_monad 11))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad (sint_monad (2^256 - 1)) (sint_monad 6)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

subsection "Plus monad safe"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
      assert(5 + 6 == 11);
    }

    function test2() public {
      assert(2**256-1 + uint256(6) == 5);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (plus_monad_safe (sint_monad 5) (sint_monad 6)) (sint_monad 11))
      }) emptyState)"
  by (normalization)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (plus_monad_safe (sint_monad (2^256 - 1)) (sint_monad 6)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

subsection "Minus monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        unchecked {assert(6 - 5 == 1);}
    }

    function test2() public {
        unchecked {assert(uint256(5) - uint256(10) == uint256(2**256-5));}
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (minus_monad (sint_monad 6) (sint_monad 5)) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Minus monad safe"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test1() public {
        unchecked {assert(6 - 5 == 1);}
    }

    function test2() public {
        unchecked {assert(uint256(5) - uint256(10) == uint256(2**256-5));}
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (minus_monad_safe (sint_monad 6) (sint_monad 5)) (sint_monad 1))
      }) emptyState)"
  by (normalization)

lemma "is_Exception (execute (do {
        assert_monad (equals_monad (minus_monad_safe (sint_monad 5) (sint_monad 6)) (sint_monad (2^256 - 5)))
      }) emptyState)"
  by (normalization)

subsection "Mult monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test() public {
      assert(5 * 6 == 30);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mult_monad (sint_monad 5) (sint_monad 6)) (sint_monad 30))
      }) emptyState)"
  by (normalization)

subsection "Mod monad"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
    function test() public {
      assert(9 % 5 == 4);
    }
  }
*)

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (mod_monad (sint_monad 9) (sint_monad 5)) (sint_monad 4))
      }) emptyState)"
  by (normalization)

subsection "Keccak monad"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (keccak256_keccak256_monad (sint_monad 5)) (sint_monad 5))
      }) emptyState)"
  by (normalization)

subsection "Value monad"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (method_value_monad) (sint_monad 250))
      }) emptyState)"
  by (normalization)

subsection "Sender monad"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (method_sender_monad) (address_monad A1))
      }) emptyState)"
  by (normalization)

subsection "Store lookup"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      int x = 5;
  
      function test() public {
          assert(x == 5);
      }
  }
*)

subsubsection "Value type"

definition "pstorage1 = (\<lambda>_. undefined) (STR ''x'' := sdata.Value (Sint 5))"
definition "storage1 = (\<lambda>_. undefined) (A1 := pstorage1)"
definition "state1 = emptyState\<lparr>Storage := storage1\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') []) (sint_monad 5))
      }) state1)" by normalization

subsubsection "Array"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          assert(x[0] == 5);
      }
  }
*)

definition "pstorage2 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 5)])"
definition "storage2 = (\<lambda>_. undefined) (A1 := pstorage2)"
definition "state2 = emptyState\<lparr>Storage := storage2\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) state2)" by normalization

subsubsection "Mappings"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      mapping (uint => uint) x;
  
      constructor () public {
          x [0] = 5;
      }
  
      function test() public {
          assert(x[0] == 5);
      }
  }
*)

definition "pstorage3 = (\<lambda>_. undefined) (STR ''x'' := sdata.Map ((\<lambda>_. undefined) (Sint (0) := sdata.Value (Sint 5))))"
definition "storage3 = (\<lambda>_. undefined) (A1 := pstorage3)"
definition "state3 = emptyState\<lparr>Storage := storage3\<rparr>"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) state2)" by normalization

subsection "Stack lookup"

subsubsection "Value type"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint x = 5;
          assert(x == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (STR ''x'') (Sint 5);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 5))
      }) emptyState)" by normalization

subsubsection "Memory"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [uint256(5)];
          assert(x[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        minit (STR ''x'') (cdata.Array [cdata.Value (Sint 5)]);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1][1] memory x = [[uint256(5)]];
          uint[1] memory y = x[0];
          assert(y[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        minit (STR ''x'') (cdata.Array [cdata.Array [cdata.Value (Sint 5)]]);
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') [sint_monad 0]);
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

subsubsection "Calldata"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          require (x[0] == 5, "Testcase requires x[0] == 5");
          assert (x[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (STR ''x'') (cdata.Array [cdata.Value (Sint 5)]);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1][1] calldata x) public {
          require (x[0][0] == 5, "Testcase requires x[0] == 0");
          uint[1] calldata y = x[0]; 
          assert (y[0] == 5);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (STR ''x'') (cdata.Array [cdata.Array [cdata.Value (Sint 5)]]);
        cdecl (STR ''y'') (STR ''x'') [Sint 0];
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) emptyState)" by normalization

subsubsection "Storage pointers"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          uint[1] storage y = x;
          assert (y[0] == 5);
      }
  }
*)

definition "pstorage8 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 5)])"
definition "storage8 = (\<lambda>_. undefined) (A1 := pstorage8)"
definition "state8 = emptyState\<lparr>Storage := storage8\<rparr>"

lemma "is_Normal (execute (do {
        sinit (STR ''y'') (STR ''x'') [];
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) state8)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1][1] x = [[5]];
  
      function test() public {
          uint[1] storage y = x[0];
          assert (y[0] == 5);
      }
  }
*)

definition "pstorage9 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Array [sdata.Value (Sint 5)]])"
definition "storage9 = (\<lambda>_. undefined) (A1 := pstorage9)"
definition "state9 = emptyState\<lparr>Storage := storage9\<rparr>"

lemma "is_Normal (execute (do {
        sinit (STR ''y'') (STR ''x'') [Sint 0];
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 5))
      }) state9)" by normalization

subsection "Arrays"

subsubsection "Storage Arrays"

paragraph "Length"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          assert (x.length == 1);
      }
  }
*)

definition "pstorage10 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 5)])"
definition "storage10 = (\<lambda>_. undefined) (A1 := pstorage10)"
definition "state10 = emptyState\<lparr>Storage := storage10\<rparr>"

paragraph "Push"

lemma "is_Normal (execute (do {
        assert_monad (equals_monad (contract_storearrayLength (STR ''x'') []) (sint_monad 1))
      }) state10)" by normalization

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[] x = [5];
  
      function test() public {
          x.push(uint(6));
          assert (x[0] == 5);
          assert (x[1] == 6);
      }
  }
*)

definition "pstorage11 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 5)])"
definition "storage11 = (\<lambda>_. undefined) (A1 := pstorage11)"
definition "state11 = emptyState\<lparr>Storage := storage11\<rparr>"

lemma "is_Normal (execute (do {
        contract_allocate (STR ''x'') [] (sdata.Value (Sint 6));
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 5));
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 1]) (sint_monad 6))
      }) state11)" by normalization

subsubsection "Memory Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [5];
          assert (x.length == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        minit (STR ''x'') (cdata.Array [cdata.Value (Sint 5)]);
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1))
      }) emptyState)" by normalization

subsubsection "Calldata Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          assert (x.length == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (STR ''x'') (cdata.Array [cdata.Array [cdata.Value (Sint 5)]]);
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1))
      }) emptyState)" by normalization

subsubsection "Storage pointer Arrays"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      uint[1] x = [5];
  
      function test() public {
          uint[1] storage y = x;
          assert (y.length == 1);
      }
  }
*)

definition "pstorage14 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 5)])"
definition "storage14 = (\<lambda>_. undefined) (A1 := pstorage14)"
definition "state14 = emptyState\<lparr>Storage := storage14\<rparr>"

lemma "is_Normal (execute (do {
        sinit (STR ''x'') (STR ''x'') [];
        assert_monad (equals_monad (contract_arrayLength (STR ''x'') []) (sint_monad 1))
      }) state14)" by normalization

section "Loops"
(*
  pragma solidity =0.8.25;
  
  contract MyToken {
      function test0() public {
          uint x = 0;
          while (x > 0) {
              x = 1;
          }
          assert (x == 0);
      }
  
      function test1() public {
          uint x = 5;
          while (x > 0) {
              x --;
          }
          assert (x == 0);
      }
  }
*)

(*

declare while_monad.simps[code]

value "(execute (do {
        init (STR ''x'') (Sint 0);
        while_monad (false_monad)
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 2));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 0))
      }) emptyState)"
  by (normalization)

*)

section "Conditionals"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      function test0() public {
          uint x = 0;
          if (true) {
              x = 1;
          } else {
              x = 2;
          }
          assert (x == 1);
      }
  
      function test1() public {
          uint x = 0;
          if (false) {
              x = 1;
          } else {
              x = 2;
          }
          assert (x == 2);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (STR ''x'') (Sint 0);
        cond_monad (true_monad)
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 1))
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 2));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 1))
      }) emptyState)"
  by (normalization)

lemma "is_Normal (execute (do {
        init (STR ''x'') (Sint 0);
        cond_monad (false_monad)
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 1))
          (contract_assign_stack_monad (STR ''x'') [] (sint_monad 2));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 2))
      }) emptyState)"
  by (normalization)

section "Assignments"

subsection "Stack Value to Stack Value"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint x=0;
          uint y=x;
          y = 1;
          assert (x == 0);
          assert (y == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        init (STR ''x'') (Sint 0);
        init (STR ''y'') (Sint 0);
        contract_assign_stack_monad (STR ''y'') [] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') []) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') []) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Memory Array to Memory Array"

(*
  pragma solidity = 0.8.25;
  
  contract Test {
      function test() public {
          uint[1] memory x = [0];
          uint[1] memory y = [0];
          y = x;
          x[0] = 1;
          assert (x[0] == 1);
          assert (y[0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        minit (STR ''x'') (cdata.Array [cdata.Value (Sint 0)]);
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad  (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Calldata Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      function test(uint[1] calldata x) public {
          require (x[0] == 0, "Testcase requires x[0] == 0");

          uint[1] memory y = (0);
  
          y = x;
          y[0] = 1;
  
          assert (x[0] == 0);
          assert (y[0] == 1);
      }
  }
*)

lemma "is_Normal (execute (do {
        cinit (STR ''x'') (cdata.Array [cdata.Value (Sint 0)]);
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        require_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad  (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) emptyState)"
  by (normalization)

subsection "Storage Pointer Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [uint256 (0)];
  
      function test() public {
          require (s[0] == 0, "Testcase requires s[0] == 0");

          uint[1] storage x = s;
          uint[1] memory y = [uint256 (0)];
  
          y = x;
          y[0] = 1;
  
          assert (x[0] == 0);
          assert (y[0] == 1);
      }
  }
*)

definition "pstorage17 = (\<lambda>_. undefined) (STR ''s'' := sdata.Array [sdata.Value (Sint 0)])"
definition "storage17 = (\<lambda>_. undefined) (A1 := pstorage17)"
definition "state17 = emptyState\<lparr>Storage := storage17\<rparr>"

lemma "is_Normal (execute (do {
        require_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 0));
        sinit (STR ''x'') (STR ''s'') [];
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        contract_assign_stack_monad (STR ''y'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state17)" by normalization

subsection "Storage Array to Memory Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (0);
  
      function test() public {
        uint[1] memory y = (0);

        y=x;
        y[0] = 1;
        
        assert (x[0] == 0);
        assert (y[0] == 1);
      }
  }
*)

definition "pstorage18 = (\<lambda>_. undefined) (STR ''x'' := sdata.Array [sdata.Value (Sint 0)])"
definition "storage18 = (\<lambda>_. undefined) (A1 := pstorage18)"
definition "state18 = emptyState\<lparr>Storage := storage18\<rparr>"

lemma "is_Normal (execute (do {
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        contract_assign_stack_monad (STR ''y'') [] (contract_storeLookup (STR ''x'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state18)" by normalization

subsection "Storage Pointer Array to Storage Pointer Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s1 = (0);
      uint[1] s2 = (0);
  
      function test() public {
          assert (s1[0]==0); //OK
          assert (s2[0]==0); //OK
      
          uint[1] storage x=s1; // this is storage pointer
          uint[1] storage y=s2; // this is storage pointer
      
          y=x;  //y is a pointer to content of s1
          y[0]=1;
      
          assert (s1[0]==1);
          assert (s2[0]==0);
          assert (x[0]==1);
          assert (y[0]==1);
      }
  }
*)

definition "pstorage19 = (\<lambda>_. undefined) (STR ''s1'' := sdata.Array [sdata.Value (Sint 0)], STR ''s2'' := sdata.Array [sdata.Value (Sint 0)])"
definition "storage19 = (\<lambda>_. undefined) (A1 := pstorage19)"
definition "state19 = emptyState\<lparr>Storage := storage19\<rparr>"

lemma "is_Normal (execute (do {
        sinit (STR ''x'') (STR ''s1'') [];
        sinit (STR ''y'') (STR ''s2'') [];
        contract_assign_stack_monad (STR ''x'') [] (contract_stackLookup (STR ''y'') []);
        contract_assign_stack_monad (STR ''y'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s1'') [sint_monad 0]) (sint_monad 0));
        assert_monad (equals_monad (contract_storeLookup (STR ''s2'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 1))
      }) state19)" by normalization

subsection "Storage Array to Storage Pointer Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [0];
  
      function test() public {
        uint[1] storage x; // this is storage pointer
        x=s;
        s[0]=1;
  
        assert (s[0]==1); //OK
        assert (s[0]==0); //OK
        assert (x[0]==1); //OK
      }
  }
*)

definition "pstorage20 = (\<lambda>_. undefined) (STR ''s'' := sdata.Array [sdata.Value (Sint 0)])"
definition "storage20 = (\<lambda>_. undefined) (A1 := pstorage20)"
definition "state20 = emptyState\<lparr>Storage := storage20\<rparr>"

lemma "is_Normal (execute (do {
        sinit (STR ''x'') (STR '''') [];
        contract_assign_stack_monad (STR ''x'') [] (contract_storeLookup (STR ''s'') []);
        contract_assign_storage_monad (STR ''s'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 1))
      }) state20)" by normalization

subsection "Memory Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] x = (0);
  
      function test() public {
        uint[1] memory y = (0);

        x=y;
        x[0] = 1;
        
        assert (x[0] == 1);
        assert (y[0] == 0);
      }
  }
*)

lemma "is_Normal (execute ( do {
        minit (STR ''y'') (cdata.Array [cdata.Value (Sint 0)]);
        contract_assign_storage_monad (STR ''x'') [] (contract_stackLookup (STR ''y'') []);
        contract_assign_storage_monad (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) emptyState)" by normalization

subsection "Calldata Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract Test {
      uint[1] s = [0];
  
      function test(uint[1] calldata x) public {
          require (x[0] == 0, "Testcase requires x[0] == 0");
  
          s = x;
          s[0] = 1;
  
          assert (s[0] == 1);
          assert (x[0] == 0);
      }
  }
*)

definition "pstorage22 = (\<lambda>_. undefined) (STR ''s'' := (sdata.Array [sdata.Value (Sint 0)]))"
definition "storage22 = (\<lambda>_. undefined) (A1 := pstorage22)"
definition "state22 = emptyState\<lparr>Storage := storage22\<rparr>"

lemma "is_Normal (execute (do {
        cinit (STR ''x'') (cdata.Array [cdata.Value (Sint 0)]);
        require_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0));
        contract_assign_storage_monad (STR ''s'') [] (contract_stackLookup (STR ''x'') []);
        contract_assign_storage_monad (STR ''s'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''s'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_stackLookup (STR ''x'') [sint_monad 0]) (sint_monad 0))
      }) state22)"
  by (normalization)

subsection "Storage Array to Storage Array"
(*
  pragma solidity =0.8.25;
  
  contract MyToken {
      uint[1] x = [0];
      uint[1] y = [0];
  
      function test() public {
        x=y;
        x[0]=1;

        assert (x[0]==1);
        assert (y[0]==0);
      }
  }
*)

definition "pstorage23 = (\<lambda>_. undefined) (STR ''x'' := (sdata.Array [sdata.Value (Sint 0)]), STR ''y'' := (sdata.Array [sdata.Value (Sint 0)]))"
definition "storage23 = (\<lambda>_. undefined) (A1 := pstorage23)"
definition "state23 = emptyState\<lparr>Storage := storage23\<rparr>"

lemma "is_Normal (execute ( do {
        contract_assign_storage_monad (STR ''x'') [] (contract_storeLookup (STR ''y'') []);
        contract_assign_storage_monad (STR ''x'') [sint_monad 0] (sint_monad 1);
        assert_monad (equals_monad (contract_storeLookup (STR ''x'') [sint_monad 0]) (sint_monad 1));
        assert_monad (equals_monad (contract_storeLookup (STR ''y'') [sint_monad 0]) (sint_monad 0))
      }) state23)" by normalization

end