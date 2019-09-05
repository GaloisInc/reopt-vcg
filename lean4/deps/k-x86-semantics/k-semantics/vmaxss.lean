def vmaxss1 : instruction :=
  definst "vmaxss" $ do
    pattern fun (v_2657 : reg (bv 128)) (v_2658 : reg (bv 128)) (v_2659 : reg (bv 128)) => do
      v_4527 <- getRegister v_2658;
      v_4529 <- eval (extract v_4527 96 128);
      v_4530 <- getRegister v_2657;
      v_4531 <- eval (extract v_4530 96 128);
      setRegister (lhs.of_reg v_2659) (concat (extract v_4527 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4529 v_4531) (expression.bv_nat 1 1)) v_4529 v_4531));
      pure ()
    pat_end;
    pattern fun (v_2652 : Mem) (v_2653 : reg (bv 128)) (v_2654 : reg (bv 128)) => do
      v_9974 <- getRegister v_2653;
      v_9976 <- eval (extract v_9974 96 128);
      v_9977 <- evaluateAddress v_2652;
      v_9978 <- load v_9977 4;
      setRegister (lhs.of_reg v_2654) (concat (extract v_9974 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9976 v_9978) (expression.bv_nat 1 1)) v_9976 v_9978));
      pure ()
    pat_end
