def vmaxss1 : instruction :=
  definst "vmaxss" $ do
    pattern fun (v_2682 : reg (bv 128)) (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) => do
      v_4554 <- getRegister v_2683;
      v_4556 <- eval (extract v_4554 96 128);
      v_4557 <- getRegister v_2682;
      v_4558 <- eval (extract v_4557 96 128);
      setRegister (lhs.of_reg v_2684) (concat (extract v_4554 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4556 v_4558) (expression.bv_nat 1 1)) v_4556 v_4558));
      pure ()
    pat_end;
    pattern fun (v_2677 : Mem) (v_2678 : reg (bv 128)) (v_2679 : reg (bv 128)) => do
      v_10001 <- getRegister v_2678;
      v_10003 <- eval (extract v_10001 96 128);
      v_10004 <- evaluateAddress v_2677;
      v_10005 <- load v_10004 4;
      setRegister (lhs.of_reg v_2679) (concat (extract v_10001 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10003 v_10005) (expression.bv_nat 1 1)) v_10003 v_10005));
      pure ()
    pat_end
