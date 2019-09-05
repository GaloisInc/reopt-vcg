def cmovew1 : instruction :=
  definst "cmovew" $ do
    pattern fun (v_2615 : reg (bv 16)) (v_2616 : reg (bv 16)) => do
      v_4302 <- getRegister zf;
      v_4304 <- getRegister v_2615;
      v_4305 <- getRegister v_2616;
      setRegister (lhs.of_reg v_2616) (mux (eq v_4302 (expression.bv_nat 1 1)) v_4304 v_4305);
      pure ()
    pat_end;
    pattern fun (v_2610 : Mem) (v_2611 : reg (bv 16)) => do
      v_7935 <- getRegister zf;
      v_7937 <- evaluateAddress v_2610;
      v_7938 <- load v_7937 2;
      v_7939 <- getRegister v_2611;
      setRegister (lhs.of_reg v_2611) (mux (eq v_7935 (expression.bv_nat 1 1)) v_7938 v_7939);
      pure ()
    pat_end
