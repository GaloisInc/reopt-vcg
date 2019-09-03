def vmaxsd1 : instruction :=
  definst "vmaxsd" $ do
    pattern fun (v_2583 : reg (bv 128)) (v_2584 : reg (bv 128)) (v_2585 : reg (bv 128)) => do
      v_4454 <- getRegister v_2584;
      v_4456 <- eval (extract v_4454 64 128);
      v_4457 <- getRegister v_2583;
      v_4458 <- eval (extract v_4457 64 128);
      setRegister (lhs.of_reg v_2585) (concat (extract v_4454 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4456 v_4458) (expression.bv_nat 1 1)) v_4456 v_4458));
      pure ()
    pat_end;
    pattern fun (v_2577 : Mem) (v_2578 : reg (bv 128)) (v_2579 : reg (bv 128)) => do
      v_10098 <- getRegister v_2578;
      v_10100 <- eval (extract v_10098 64 128);
      v_10101 <- evaluateAddress v_2577;
      v_10102 <- load v_10101 8;
      setRegister (lhs.of_reg v_2579) (concat (extract v_10098 0 64) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10100 v_10102) (expression.bv_nat 1 1)) v_10100 v_10102));
      pure ()
    pat_end
