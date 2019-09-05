def movups1 : instruction :=
  definst "movups" $ do
    pattern fun (v_2687 : reg (bv 128)) (v_2688 : reg (bv 128)) => do
      v_4102 <- getRegister v_2687;
      setRegister (lhs.of_reg v_2688) v_4102;
      pure ()
    pat_end;
    pattern fun (v_2679 : reg (bv 128)) (v_2678 : Mem) => do
      v_8491 <- evaluateAddress v_2678;
      v_8492 <- getRegister v_2679;
      store v_8491 v_8492 16;
      pure ()
    pat_end;
    pattern fun (v_2682 : Mem) (v_2683 : reg (bv 128)) => do
      v_8732 <- evaluateAddress v_2682;
      v_8733 <- load v_8732 16;
      setRegister (lhs.of_reg v_2683) v_8733;
      pure ()
    pat_end
